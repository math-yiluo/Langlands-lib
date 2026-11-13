import Langlands.Representation.Classification.OrderedExponentGroupingProof
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Stable merging of exponent-sorted families into equal-exponent groups

Finitely many labelled items with positive degrees and real exponents are
reordered by a stable decreasing sort of the exponents and then cut into
consecutive runs of equal exponent. Two labels whose order already agrees with
decreasing exponents keep their relative order.
-/

noncomputable section

namespace Langlands.Classification.A6ii

open GeneralLinear

/-- Equal-exponent groups of a stable decreasing merge of labelled items: the
groups form a block shape whose block sizes are the total degrees of their
members, with strictly decreasing group exponents. Items listed by group and
then by position keep the relative order of every pair already ordered by
decreasing exponent. -/
structure MergeGrouping {N : ℕ} (n : ℕ) (deg : Fin N → ℕ) (ex : Fin N → ℝ) where
  /-- The block shape of the groups. -/
  shape : BlockShape n
  /-- The common exponent of each group. -/
  exponent : Fin shape.length → ℝ
  strictAnti : StrictAnti exponent
  /-- The number of members of each group. -/
  count : Fin shape.length → ℕ
  /-- The members of the groups, in order. -/
  label : ((g : Fin shape.length) × Fin (count g)) ≃ Fin N
  label_exponent : ∀ g j, ex (label ⟨g, j⟩) = exponent g
  size_sum : ∀ g, ∑ j, deg (label ⟨g, j⟩) = shape.size g
  lt_of_lt : ∀ x y, label x < label y → ex (label y) ≤ ex (label x) →
    finSigmaFinEquiv x < finSigmaFinEquiv y

namespace MergeGrouping

variable {N n : ℕ} {deg : Fin N → ℕ} {ex : Fin N → ℝ}

/-- The degrees of the members of each group, as a block refinement. -/
def refinement (m : MergeGrouping n deg ex) (hdeg : ∀ ℓ, 0 < deg ℓ) :
    Geometric.BlockRefinement m.shape := fun g =>
  { length := m.count g
    size j := deg (m.label ⟨g, j⟩)
    positive _ := hdeg _
    sum_eq := m.size_sum g }

/-- Later positions of the flattened members lie in the same or later groups. -/
theorem group_monotone (m : MergeGrouping n deg ex) (hdeg : ∀ ℓ, 0 < deg ℓ)
    {k k' : Fin (m.shape.flatten (m.refinement hdeg)).length} (h : k ≤ k') :
    ((m.shape.flattenBlockEquiv (m.refinement hdeg)).symm k).1 ≤
      ((m.shape.flattenBlockEquiv (m.refinement hdeg)).symm k').1 := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hk := (BlockShape.finSigmaFinEquiv_lt_iff
    ((m.shape.flattenBlockEquiv (m.refinement hdeg)).symm k')
    ((m.shape.flattenBlockEquiv (m.refinement hdeg)).symm k)).mpr (Or.inl hlt)
  change (m.shape.flattenBlockEquiv (m.refinement hdeg))
      ((m.shape.flattenBlockEquiv (m.refinement hdeg)).symm k') <
    (m.shape.flattenBlockEquiv (m.refinement hdeg))
      ((m.shape.flattenBlockEquiv (m.refinement hdeg)).symm k) at hk
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hk
  exact absurd h (not_le.mpr hk)

/-- The exponents of the flattened members decrease. -/
theorem antitone_exponent (m : MergeGrouping n deg ex) (hdeg : ∀ ℓ, 0 < deg ℓ) :
    Antitone (fun k => ex (m.label ((m.shape.flattenBlockEquiv (m.refinement hdeg)).symm k))) := by
  intro k k' h
  change ex (m.label ⟨_, _⟩) ≤ ex (m.label ⟨_, _⟩)
  rw [m.label_exponent, m.label_exponent]
  exact m.strictAnti.antitone (m.group_monotone hdeg h)

end MergeGrouping

/-- A stable decreasing sort keeps the order of pairs already in decreasing order. -/
theorem sort_symm_lt {N : ℕ} (ex : Fin N → ℝ) {p p' : Fin N}
    (hlt : Tuple.sort (fun ℓ => -ex ℓ) p < Tuple.sort (fun ℓ => -ex ℓ) p')
    (hle : ex (Tuple.sort (fun ℓ => -ex ℓ) p') ≤ ex (Tuple.sort (fun ℓ => -ex ℓ) p)) :
    p < p' := by
  obtain ⟨hmon, hstab⟩ := (Tuple.eq_sort_iff (σ := Tuple.sort (fun ℓ => -ex ℓ))
    (f := fun ℓ => -ex ℓ)).mp rfl
  by_contra hp
  replace hp := not_lt.mp hp
  rcases hp.lt_or_eq with hp | hp
  · have h1 : -ex (Tuple.sort (fun ℓ => -ex ℓ) p') ≤ -ex (Tuple.sort (fun ℓ => -ex ℓ) p) :=
      hmon hp.le
    have h2 := hstab p' p hp (by linarith)
    exact absurd hlt (not_lt.mpr h2.le)
  · subst hp
    exact lt_irrefl _ hlt

/-- Every labelled family of positive degrees has a stable decreasing merge
into equal-exponent groups. -/
theorem exists_mergeGrouping {N n : ℕ} (deg : Fin N → ℕ) (hdeg : ∀ ℓ, 0 < deg ℓ)
    (hsum : ∑ ℓ, deg ℓ = n) (ex : Fin N → ℝ) :
    Nonempty (MergeGrouping n deg ex) := by
  classical
  let σ : Equiv.Perm (Fin N) := Tuple.sort (fun ℓ => -ex ℓ)
  let M : BlockShape n :=
    { length := N
      size p := deg (σ p)
      positive p := hdeg _
      sum_eq := (Equiv.sum_comp σ deg).trans hsum }
  let a : Fin M.length → ℝ := fun p => ex (σ p)
  have ha : Antitone a := by
    intro p p' h
    have := Tuple.monotone_sort (fun ℓ => -ex ℓ) h
    change -ex (σ p) ≤ -ex (σ p') at this
    change ex (σ p') ≤ ex (σ p)
    linarith
  obtain ⟨Bc, b, q, hb, hq, -, hab, S, e, h, hmono, -⟩ :=
    orderedExponentGrouping n M a ha
  refine ⟨{
    shape := Bc
    exponent := b
    strictAnti := hb
    count := fun g => (S g).length
    label := (Equiv.sigmaCongrRight e).trans ((Equiv.sigmaFiberEquiv q).trans σ)
    label_exponent := ?_
    size_sum := ?_
    lt_of_lt := ?_ }⟩
  · intro g j
    change a (e g j).val = b g
    rw [hab, (e g j).property]
  · intro g
    change ∑ j, M.size (e g j).val = Bc.size g
    exact (Finset.sum_congr rfl fun j _ => (h g j).symm).trans (S g).sum_eq
  · rintro ⟨g, j⟩ ⟨g', j'⟩ hlt hle
    change σ (e g j).val < σ (e g' j').val at hlt
    change ex (σ (e g' j').val) ≤ ex (σ (e g j).val) at hle
    have hpp := sort_symm_lt ex hlt hle
    have hg : g ≤ g' := by
      have := hq hpp.le
      rwa [(e g j).property, (e g' j').property] at this
    apply BlockShape.finSigmaFinEquiv_lt_of
    rcases hg.lt_or_eq with hg | hg
    · exact Or.inl hg
    · subst hg
      exact Or.inr ⟨rfl, (hmono g).lt_iff_lt.mp hpp⟩

end Langlands.Classification.A6ii

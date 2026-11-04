import Langlands.Representation.Classification.SegmentGenericStatement
import Langlands.Representation.Classification.SegmentSocleCriterionHalvesStatement
import Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityStatement
import Langlands.Representation.Classification.SegmentProductPermutation
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.Parabolic.ProductInductionSubrepresentation
import Langlands.Representation.Filtration.RepresentationLength
import Langlands.Representation.Filtration.LengthTwoMatching

/-!
# Assembly of the segment socle irreducibility criterion

Zelevinsky's Theorem 4.2 for segment socles is derived from three explicit
proposition hypotheses: the unlinked sufficient direction, reducibility of a
linked pair of socles, and the irreducible two-factor case of Theorem 1.9.
The adjacent-pair regrouping is restated for an unsaturated segment universe.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

namespace SegmentSocleCriterionAssembly

/-! ### Elementary facts about irreducible representations -/

section Irreducible

variable {G : Type*} [Monoid G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- The top subrepresentation differs from the bottom one exactly for a nonzero carrier. -/
theorem top_ne_bot_iff {ρ : Representation ℂ G V} :
    (⊤ : Subrepresentation ρ) ≠ ⊥ ↔ Nontrivial V := by
  constructor
  · intro h
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    apply h
    apply Subrepresentation.toSubmodule_injective
    ext v
    change v ∈ (⊤ : Submodule ℂ V) ↔ v ∈ (⊥ : Submodule ℂ V)
    simp [Subsingleton.elim v 0]
  · intro hV h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hmem : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [h] at hmem
    exact hv ((Submodule.mem_bot ℂ).mp hmem)

/-- An irreducible representation has a nonzero carrier. -/
theorem nontrivial_of_isIrreducible {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) :
    Nontrivial V :=
  top_ne_bot_iff.mp (bot_ne_top (α := Subrepresentation ρ)).symm

/-- A reducible representation with a nonzero carrier has a proper nonzero
subrepresentation. -/
theorem exists_proper_of_not_isIrreducible {ρ : Representation ℂ G V} [Nontrivial V]
    (h : ¬ ρ.IsIrreducible) : ∃ S : Subrepresentation ρ, S ≠ ⊥ ∧ S ≠ ⊤ := by
  by_contra hS
  push Not at hS
  apply h
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun e => top_ne_bot_iff.mpr inferInstance e.symm
  have : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hne⟩⟩
  exact ⟨fun S => by
    by_cases hb : S = ⊥
    · exact Or.inl hb
    · exact Or.inr (hS S hb)⟩

/-- A representation with a proper nonzero subrepresentation is not irreducible. -/
theorem not_isIrreducible_of_proper {ρ : Representation ℂ G V} (S : Subrepresentation ρ)
    (h₀ : S ≠ ⊥) (h₁ : S ≠ ⊤) : ¬ ρ.IsIrreducible := by
  intro h
  rcases h.eq_bot_or_eq_top S with hS | hS
  · exact h₀ hS
  · exact h₁ hS

/-- The map from a representation to the only graded quotient of a one-step filtration. -/
def toGraded {ρ : Representation ℂ G V} (s : ObjectRepFiltration (Rep.of ρ) 1) :
    ρ.IntertwiningMap (s.gradedRepresentation 0).ρ :=
  (s.gradedProjection 0).hom.comp
    { toLinearMap := LinearMap.codRestrict _ LinearMap.id
        (fun v => by
          have htop : s.subrepresentation (0 : Fin 1).succ = ⊤ := s.subrepresentation_last
          rw [htop]
          trivial)
      isIntertwining' := fun _ => rfl }

theorem toGraded_bijective {ρ : Representation ℂ G V} (s : ObjectRepFiltration (Rep.of ρ) 1) :
    Function.Bijective (toGraded s) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    have hmem := (Submodule.Quotient.mk_eq_zero _).mp hv
    change v ∈ s.subrepresentation 0 at hmem
    rw [ObjectRepFiltration.subrepresentation_zero] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  · intro x
    obtain ⟨⟨v, hv⟩, rfl⟩ := s.gradedProjection_surjective 0 x
    exact ⟨v, rfl⟩

/-- A representation is equivalent to the graded quotient of any one-step filtration. -/
def toGradedEquiv {ρ : Representation ℂ G V} (s : ObjectRepFiltration (Rep.of ρ) 1) :
    ρ.Equiv (s.gradedRepresentation 0).ρ :=
  (toGraded s).ofBijective (toGraded_bijective s)

/-- Two irreducible representations with the same composition factors are equivalent. -/
theorem nonempty_equiv_of_haveSameJordanHolderFactors {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (hρ : ρ.IsIrreducible)
    (h : HaveSameJordanHolderFactors (Rep.of ρ) (Rep.of σ)) : Nonempty (ρ.Equiv σ) := by
  obtain ⟨m, s, t, hs, -, e, he⟩ := h
  have hm : m = 1 := by
    have h₁ := repLength_eq_of_hasSimpleFactors s hs
    have h₂ : repLength (Rep.of ρ).ρ = 1 := repLength_eq_one_iff.mpr hρ
    rw [h₂] at h₁
    exact_mod_cast h₁.symm
  subst hm
  have he0 : e 0 = 0 := Subsingleton.elim _ _
  obtain ⟨φ⟩ := he 0
  rw [he0] at φ
  exact ⟨(toGradedEquiv s).trans (φ.trans (toGradedEquiv t).symm)⟩

end Irreducible

/-! ### Segment-product data -/

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A segment socle is irreducible. -/
theorem isIrreducible_of_isSegmentSocle {Δ : T.Segment.{uV, uF}}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (h : T.IsSegmentSocle Δ π) :
    letI := T.topology
    π.representation.IsIrreducible := by
  let := T.topology
  obtain ⟨_, _, h⟩ := h
  exact h.1

/-- A datum with at least one segment has positive rank. -/
theorem rank_pos {m : ℕ} (e : T.SegmentProductDatum.{uV, uF} m) (hl : 0 < e.length) :
    0 < m := by
  rw [← e.degree_sum]
  exact Finset.sum_pos (fun i _ => (e.segments i).degree_pos)
    ⟨⟨0, hl⟩, Finset.mem_univ _⟩

/-- A datum of positive rank has at least one segment. -/
theorem length_pos {m : ℕ} (e : T.SegmentProductDatum.{uV, uF} m) (hm : 0 < m) :
    0 < e.length := by
  apply Nat.pos_of_ne_zero
  intro hl
  have hs := e.degree_sum
  have : IsEmpty (Fin e.length) := by rw [hl]; infer_instance
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hs
  omega

/-- The product of nonzero smooth blocks over a datum of positive rank is nonzero. -/
theorem induced_nontrivial {m : ℕ} (e : T.SegmentProductDatum.{uV, uF} m) (hm : 0 < m)
    (hb : ∀ i, Nontrivial (e.blocks i)) :
    letI := T.topology
    Nontrivial e.induced := by
  let := T.topology
  let := T.generalLinearTopologicalGroup m
  let j : Fin e.length := ⟨0, length_pos e hm⟩
  have hne := Parabolic.normalizedProductSlotSubrepresentation_ne_bot T e.shape
    (fun i => (e.blocks i).representation) j (fun h => hb h.1)
    (⊤ : Subrepresentation (e.blocks j).representation)
    (top_ne_bot_iff.mpr (hb j)) (fun i => (e.blocks i).isSmooth)
  have htop := Parabolic.normalizedProductSlotSubrepresentation_top T e.shape
    (fun i => (e.blocks i).representation) j
  exact (top_ne_bot_iff (ρ := T.normalizedProductInduced e.shape
    (fun i => (e.blocks i).representation))).mp (fun hbot => hne (htop.trans hbot))

/-- Socle blocks over a datum of positive rank give a nonzero product. -/
theorem induced_nontrivial_of_socles {m : ℕ} (e : T.SegmentProductDatum.{uV, uF} m)
    (hm : 0 < m) (hs : e.HasSegmentSocles) :
    letI := T.topology
    Nontrivial e.induced :=
  induced_nontrivial e hm fun i => nontrivial_of_isIrreducible (isIrreducible_of_isSegmentSocle (hs i))

/-- Reindexing keeps the multiset of segment occurrences. -/
theorem permute_multisegment {m : ℕ} (e : T.SegmentProductDatum.{uV, uF} m)
    (σ : Equiv.Perm (Fin e.length)) : (e.permute σ).multisegment = e.multisegment :=
  Multiset.coe_eq_coe.mpr (σ.ofFn_comp_perm e.segments)

/-- The values of the adjacent transposition of a block shape. -/
theorem adjacentSwap_apply_val {m : ℕ} (B : BlockShape m) (j : ℕ) (h : j + 1 < B.length)
    (x : Fin B.length) :
    (B.adjacentSwap j h x).val =
      if x.val = j then j + 1 else if x.val = j + 1 then j else x.val := by
  rcases x with ⟨x, hx⟩
  unfold BlockShape.adjacentSwap
  simp only [Equiv.swap_apply_def, Fin.mk.injEq]
  split_ifs <;> rfl

/-! ### Adjacent regrouping for an unsaturated segment universe

The following restates the published `AdjacentSegmentSwapLifting` construction
for `T.SegmentProductDatum.{uV, uF}`; the blocks still have carrier universe
`max uF uV`, which is the universe of the published regrouping theorem. -/

section Lifting

variable {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n)

/-- Retain selected actual segment occurrences and their supplied blocks. -/
def select {r m : ℕ} (f : Fin r → Fin d.length)
    (hs : ∑ i, (d.segments (f i)).degree = m) :
    T.SegmentProductDatum.{uV, uF} m where
  length := r
  segments i := d.segments (f i)
  degree_sum := hs
  blocks i := d.blocks (f i)

theorem select_congr {r m : ℕ} {f g : Fin r → Fin d.length}
    (hf : ∑ i, (d.segments (f i)).degree = m)
    (hg : ∑ i, (d.segments (g i)).degree = m) (he : f = g) :
    select d f hf = select d g hg := by
  subst g
  rfl

variable (j : ℕ) (h : j + 1 < d.length)

/-- The actual inner datum of the direct adjacent refinement. -/
def directFiber (m : Fin (d.shape.adjacentMerge j h).length) :
    T.SegmentProductDatum.{uV, uF} ((d.shape.adjacentMerge j h).size m) :=
  select d (fun k => d.shape.adjacentBlockEquiv j h ⟨m, k⟩)
    (d.shape.adjacentRefinement j h m).sum_eq

/-- The actual inner datum of the swapped refinement in the same outer shape. -/
def swappedFiber (m : Fin (d.shape.adjacentMerge j h).length) :
    T.SegmentProductDatum.{uV, uF} ((d.shape.adjacentMerge j h).size m) :=
  select d (fun k => d.shape.adjacentSwap j h
    (d.shape.adjacentSwapBlockEquiv j h ⟨m, k⟩))
    (d.shape.adjacentSwapRefinement j h m).sum_eq

theorem directFiber_socles (hd : d.HasSegmentSocles)
    (m : Fin (d.shape.adjacentMerge j h).length) :
    (directFiber d j h m).HasSegmentSocles :=
  fun k => hd (d.shape.adjacentBlockEquiv j h ⟨m, k⟩)

/-- Outside the merged slot, the actual inner data are equal. -/
theorem swappedFiber_eq_of_ne (m : Fin (d.shape.adjacentMerge j h).length)
    (hm : m.val ≠ j) : swappedFiber d j h m = directFiber d j h m := by
  apply select_congr
  funext k
  change d.shape.adjacentSwap j h (d.shape.adjacentBlockEquiv j h ⟨m, k⟩) =
    d.shape.adjacentBlockEquiv j h ⟨m, k⟩
  have hk : k.val < 1 := (d.shape.adjacentRefinement_length_of_ne j h m hm) ▸ k.isLt
  have hv := d.shape.adjacentBlockEquiv_val j h ⟨m, k⟩
  dsimp only at hv
  apply Equiv.swap_apply_of_ne_of_ne
  · rw [ne_eq, Fin.ext_iff, hv]
    dsimp only
    split_ifs <;> omega
  · rw [ne_eq, Fin.ext_iff, hv]
    dsimp only
    split_ifs <;> omega

/-- The actual two-block datum at the merged slot: the original blocks `j` and
`j + 1`, in this order. -/
def mergedFiber :
    T.SegmentProductDatum.{uV, uF}
      ((d.shape.adjacentMerge j h).size (d.shape.adjacentMergeIndex j h)) :=
  directFiber d j h (d.shape.adjacentMergeIndex j h)

theorem mergedFiber_length : (mergedFiber d j h).length = 2 :=
  d.shape.adjacentRefinement_length_merged j h

theorem mergedFiber_swap_bound : 0 + 1 < (mergedFiber d j h).length := by
  rw [mergedFiber_length]
  omega

theorem mergedFiber_label (k : Fin (mergedFiber d j h).length) :
    (d.shape.adjacentBlockEquiv j h ⟨d.shape.adjacentMergeIndex j h, k⟩).val = j + k.val := by
  rw [d.shape.adjacentBlockEquiv_val j h]
  change j + k.val + (if j < j then 1 else 0) = j + k.val
  simp

theorem mergedFiber_segments_zero :
    (mergedFiber d j h).segments ⟨0, by rw [mergedFiber_length]; omega⟩ =
      d.segments ⟨j, by omega⟩ := by
  change d.segments (d.shape.adjacentBlockEquiv j h
    ⟨d.shape.adjacentMergeIndex j h, ⟨0, _⟩⟩) = _
  congr 1
  exact Fin.ext (mergedFiber_label d j h _)

theorem mergedFiber_segments_one :
    (mergedFiber d j h).segments ⟨1, by rw [mergedFiber_length]; omega⟩ =
      d.segments ⟨j + 1, h⟩ := by
  change d.segments (d.shape.adjacentBlockEquiv j h
    ⟨d.shape.adjacentMergeIndex j h, ⟨1, _⟩⟩) = _
  congr 1
  exact Fin.ext (mergedFiber_label d j h _)

/-- In the merged slot, the swapped inner datum is exactly the two-block permutation. -/
theorem swappedFiber_eq_permute :
    swappedFiber d j h (d.shape.adjacentMergeIndex j h) =
      (mergedFiber d j h).permute
        ((mergedFiber d j h).shape.adjacentSwap 0 (mergedFiber_swap_bound d j h)) := by
  apply select_congr
  funext k
  change d.shape.adjacentSwap j h
      (d.shape.adjacentBlockEquiv j h ⟨d.shape.adjacentMergeIndex j h, k⟩) =
    d.shape.adjacentBlockEquiv j h ⟨d.shape.adjacentMergeIndex j h,
      Equiv.swap ⟨0, _⟩ ⟨1, _⟩ k⟩
  let f := fun q : Fin (mergedFiber d j h).length =>
    d.shape.adjacentBlockEquiv j h ⟨d.shape.adjacentMergeIndex j h, q⟩
  have hf : Function.Injective f := by
    intro q r hqr
    have he := (d.shape.adjacentBlockEquiv j h).injective hqr
    exact Fin.ext (congrArg (fun a => a.2.val) he)
  let a : Fin (mergedFiber d j h).length :=
    ⟨0, by rw [mergedFiber_length]; omega⟩
  let b : Fin (mergedFiber d j h).length :=
    ⟨1, by rw [mergedFiber_length]; omega⟩
  have ha : f a = ⟨j, by change j < d.length; omega⟩ :=
    Fin.ext ((mergedFiber_label d j h a).trans (Nat.add_zero j))
  have hb : f b = ⟨j + 1, h⟩ := Fin.ext (mergedFiber_label d j h b)
  have hs := hf.swap_apply a b k
  rw [ha, hb] at hs
  exact hs

theorem directFiber_induced (m : Fin (d.shape.adjacentMerge j h).length) :
    letI := T.topology
    (directFiber d j h m).induced =
      (T.normalizedProductInductionFunctor (d.shape.adjacentRefinement j h m)).obj
        (fun k => d.blocks (d.shape.adjacentBlockEquiv j h ⟨m, k⟩)) := rfl

theorem swappedFiber_induced (m : Fin (d.shape.adjacentMerge j h).length) :
    letI := T.topology
    (swappedFiber d j h m).induced =
      (T.normalizedProductInductionFunctor (d.shape.adjacentSwapRefinement j h m)).obj
        (fun k => d.blocks (d.shape.adjacentSwap j h
          (d.shape.adjacentSwapBlockEquiv j h ⟨m, k⟩))) := rfl

/-- Exact regrouping identifies the direct product with its actual inner data. -/
theorem regroup_direct :
    letI := T.topology
    Nonempty (d.induced ≅ (T.normalizedProductInductionFunctor
      (d.shape.adjacentMerge j h)).obj (fun m => (directFiber d j h m).induced)) := by
  let := T.topology
  have hh := Parabolic.orderedProductRegrouping.{uF, max uF uV} F T n d.shape
    (d.shape.adjacentMerge j h) (d.shape.adjacentRefinement j h) (d.shape.adjacentBlockEquiv j h)
    (fun _ => rfl) (d.shape.adjacent_index j h) d.blocks
  have he := funext (fun m => directFiber_induced d j h m)
  have he' := congrArg
    (fun A => (T.normalizedProductInductionFunctor (d.shape.adjacentMerge j h)).obj A) he
  obtain ⟨e⟩ := hh
  dsimp only at e
  exact ⟨e ≪≫ eqToIso he'.symm⟩

/-- The swapped refinement uses the very same outer shape. -/
theorem regroup_swapped :
    letI := T.topology
    Nonempty ((d.permute (d.shape.adjacentSwap j h)).induced ≅
      (T.normalizedProductInductionFunctor (d.shape.adjacentMerge j h)).obj
        (fun m => (swappedFiber d j h m).induced)) := by
  let := T.topology
  have hh := Parabolic.orderedProductRegrouping.{uF, max uF uV} F T n
    (d.shape.permute (d.shape.adjacentSwap j h))
    (d.shape.adjacentMerge j h) (d.shape.adjacentSwapRefinement j h)
    (d.shape.adjacentSwapBlockEquiv j h) (fun _ => rfl)
    (d.shape.adjacentSwap_index j h) (fun i => d.blocks (d.shape.adjacentSwap j h i))
  have he := funext (fun m => swappedFiber_induced d j h m)
  have he' := congrArg
    (fun A => (T.normalizedProductInductionFunctor (d.shape.adjacentMerge j h)).obj A) he
  obtain ⟨e⟩ := hh
  dsimp only at e
  exact ⟨e ≪≫ eqToIso he'.symm⟩

/-- The family of inner isomorphisms: the supplied one at the merged slot and
identities elsewhere. -/
theorem fiber_iso
    (hm₀ : letI := T.topology
      Nonempty ((mergedFiber d j h).induced ≅
        ((mergedFiber d j h).permute
          ((mergedFiber d j h).shape.adjacentSwap 0 (mergedFiber_swap_bound d j h))).induced))
    (m : Fin (d.shape.adjacentMerge j h).length) :
    letI := T.topology
    Nonempty ((directFiber d j h m).induced ≅ (swappedFiber d j h m).induced) := by
  let := T.topology
  by_cases hm : m.val = j
  · have he : m = d.shape.adjacentMergeIndex j h := Fin.ext hm
    subst m
    rw [swappedFiber_eq_permute]
    exact hm₀
  · rw [swappedFiber_eq_of_ne d j h m hm]
    exact ⟨Iso.refl _⟩

/-- An isomorphism between the two orders of the merged two-block datum lifts to an
isomorphism of the full products. -/
theorem lift
    (hm₀ : letI := T.topology
      Nonempty ((mergedFiber d j h).induced ≅
        ((mergedFiber d j h).permute
          ((mergedFiber d j h).shape.adjacentSwap 0 (mergedFiber_swap_bound d j h))).induced)) :
    letI := T.topology
    Nonempty (d.induced ≅ (d.permute (d.shape.adjacentSwap j h)).induced) := by
  let := T.topology
  obtain ⟨e₀⟩ := regroup_direct d j h
  obtain ⟨e₁⟩ := regroup_swapped d j h
  let e : ∀ m, (directFiber d j h m).induced ≅ (swappedFiber d j h m).induced :=
    fun m => (fiber_iso d j h hm₀ m).some
  exact ⟨e₀ ≪≫ (T.normalizedProductInductionFunctor
    (d.shape.adjacentMerge j h)).mapIso (Pi.isoMk e) ≪≫ e₁.symm⟩

/-- Irreducibility of the full product forces irreducibility of the merged
two-block product, for socle blocks: a proper nonzero subrepresentation of the
merged slot lifts to the outer normalized product. -/
theorem mergedFiber_isIrreducible (hd : d.HasSegmentSocles)
    (hirr : letI := T.topology
      d.induced.representation.IsIrreducible) :
    letI := T.topology
    (mergedFiber d j h).induced.representation.IsIrreducible := by
  let := T.topology
  let M := d.shape.adjacentMerge j h
  let := T.generalLinearTopologicalGroup n
  by_contra hred
  have : Nontrivial (mergedFiber d j h).induced :=
    induced_nontrivial_of_socles _ (M.positive _) (directFiber_socles d j h hd _)
  obtain ⟨S, hS₀, hS₁⟩ := exists_proper_of_not_isIrreducible hred
  have hV : ∀ m : ({d.shape.adjacentMergeIndex j h}ᶜ : Set (Fin M.length)),
      Nontrivial (directFiber d j h m).induced := fun m =>
    induced_nontrivial_of_socles _ (M.positive _) (directFiber_socles d j h hd _)
  have hP := Parabolic.normalizedProductSlotSubrepresentation_proper_nonzero T M
    (fun m => (directFiber d j h m).induced.representation) (d.shape.adjacentMergeIndex j h)
    hV S hS₀ hS₁ (fun m => (directFiber d j h m).induced.isSmooth)
  obtain ⟨e₀⟩ := regroup_direct d j h
  have hPirr : ((T.normalizedProductInductionFunctor M).obj
      (fun m => (directFiber d j h m).induced)).representation.IsIrreducible :=
    LengthTwo.isIrreducible_of_equiv (SmoothRep.equivOfIso e₀) hirr
  exact not_isIrreducible_of_proper _ hP.1 hP.2 hPirr

end Lifting

/-! ### The local steps of the criterion -/

variable (F T)

/-- The sufficient direction at an arbitrary rank of positive value. -/
theorem isIrreducible_of_unlinked
    (h1 : UnlinkedSegmentSocleProductIrreducible.{uF, uV} F T)
    {m : ℕ} (e : T.SegmentProductDatum.{uV, uF} m) (hm : 0 < m)
    (hs : e.HasSegmentSocles) (hu : e.multisegment.IsUnlinked) :
    letI := T.topology
    e.induced.representation.IsIrreducible := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hm)
  exact h1 k e hs hu

/-- Two unlinked socles commute up to isomorphism: both orders are irreducible
and have the same composition factors. -/
theorem pair_swap_iso
    (h1 : UnlinkedSegmentSocleProductIrreducible.{uF, uV} F T)
    (h19 : TwoFactorProductConstituentCommutativity.{uF, max uF uV} F T)
    {m : ℕ} (e : T.SegmentProductDatum.{uV, uF} m) (h₂ : e.length = 2)
    (hb : 0 + 1 < e.length) (hs : e.HasSegmentSocles)
    (hu : ¬ (e.segments ⟨0, by omega⟩).IsLinked (e.segments ⟨1, by omega⟩)) :
    letI := T.topology
    Nonempty (e.induced ≅ (e.permute (e.shape.adjacentSwap 0 hb)).induced) := by
  let := T.topology
  have hm : 0 < m := rank_pos e (by omega)
  have hunl : e.multisegment.IsUnlinked := by
    intro Δ₁ hΔ₁ Δ₂ hΔ₂
    obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ _).mp (Multiset.mem_coe.mp hΔ₁)
    obtain ⟨b, rfl⟩ := (List.mem_ofFn' _ _).mp (Multiset.mem_coe.mp hΔ₂)
    have ha : a.val = 0 ∨ a.val = 1 := by omega
    have hb' : b.val = 0 ∨ b.val = 1 := by omega
    rcases ha with ha | ha <;> rcases hb' with hb' | hb'
    · rw [show a = b from Fin.ext (ha.trans hb'.symm)]
      exact PadicField.TopologicalData.Segment.not_isLinked_self _
    · rw [show a = ⟨0, by omega⟩ from Fin.ext ha, show b = ⟨1, by omega⟩ from Fin.ext hb']
      exact hu
    · rw [show a = ⟨1, by omega⟩ from Fin.ext ha, show b = ⟨0, by omega⟩ from Fin.ext hb']
      exact fun hl => hu hl.symm
    · rw [show a = b from Fin.ext (ha.trans hb'.symm)]
      exact PadicField.TopologicalData.Segment.not_isLinked_self _
  have hirr := isIrreducible_of_unlinked F T h1 e hm hs hunl
  have hJH := h19 m e.shape h₂ e.blocks
    (fun i => isIrreducible_of_isSegmentSocle (hs i))
  dsimp only at hJH
  obtain ⟨φ⟩ := nonempty_equiv_of_haveSameJordanHolderFactors hirr hJH
  exact ⟨SmoothRep.mkIso φ⟩

/-- Adjacent unlinked socles may be interchanged in a full product. -/
theorem swap_iso
    (h1 : UnlinkedSegmentSocleProductIrreducible.{uF, uV} F T)
    (h19 : TwoFactorProductConstituentCommutativity.{uF, max uF uV} F T)
    {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n) (j : ℕ) (h : j + 1 < d.length)
    (hs : d.HasSegmentSocles)
    (hu : ¬ (d.segments ⟨j, by omega⟩).IsLinked (d.segments ⟨j + 1, h⟩)) :
    letI := T.topology
    Nonempty (d.induced ≅ (d.permute (d.shape.adjacentSwap j h)).induced) := by
  apply lift d j h
  apply pair_swap_iso F T h1 h19 (mergedFiber d j h) (mergedFiber_length d j h)
    (mergedFiber_swap_bound d j h) (directFiber_socles d j h hs _)
  rw [mergedFiber_segments_zero, mergedFiber_segments_one]
  exact hu

/-- In an irreducible product of socles, adjacent segments are not linked. -/
theorem adjacent_not_isLinked
    (h3 : LinkedSegmentSoclePairReducible.{uF, uV} F T)
    {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n) (hs : d.HasSegmentSocles)
    (hirr : letI := T.topology
      d.induced.representation.IsIrreducible)
    (j : ℕ) (h : j + 1 < d.length) :
    ¬ (d.segments ⟨j, by omega⟩).IsLinked (d.segments ⟨j + 1, h⟩) := by
  intro hl
  apply h3 _ (mergedFiber d j h) (mergedFiber_length d j h) (directFiber_socles d j h hs _)
  · rw [mergedFiber_segments_zero, mergedFiber_segments_one]
    exact hl
  · exact mergedFiber_isIrreducible d j h hs hirr

/-- In an irreducible product of socles, no two segments at distance `k + 1`
are linked. -/
theorem not_isLinked_of_isIrreducible
    (h1 : UnlinkedSegmentSocleProductIrreducible.{uF, uV} F T)
    (h3 : LinkedSegmentSoclePairReducible.{uF, uV} F T)
    (h19 : TwoFactorProductConstituentCommutativity.{uF, max uF uV} F T) (k : ℕ) :
    ∀ {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n), d.HasSegmentSocles →
      (letI := T.topology; d.induced.representation.IsIrreducible) →
      ∀ (i : ℕ) (hk : i + k + 1 < d.length),
        ¬ (d.segments ⟨i, by omega⟩).IsLinked (d.segments ⟨i + k + 1, hk⟩) := by
  induction k with
  | zero =>
    intro n d hs hirr i hk
    exact adjacent_not_isLinked F T h3 d hs hirr i hk
  | succ k ih =>
    intro n d hs hirr i hk
    let := T.topology
    have h01 : i + 1 < d.length := by omega
    obtain ⟨φ⟩ := swap_iso F T h1 h19 d i h01 hs (adjacent_not_isLinked F T h3 d hs hirr i h01)
    have hs' : (d.permute (d.shape.adjacentSwap i h01)).HasSegmentSocles :=
      fun x => hs _
    have hirr' := LengthTwo.isIrreducible_of_equiv (SmoothRep.equivOfIso φ) hirr
    have hk' : i + 1 + k + 1 < (d.permute (d.shape.adjacentSwap i h01)).length := by
      change i + 1 + k + 1 < d.length
      omega
    have key := ih (d.permute (d.shape.adjacentSwap i h01)) hs' hirr' (i + 1) hk'
    have e1 : (d.permute (d.shape.adjacentSwap i h01)).segments ⟨i + 1, by omega⟩ =
        d.segments ⟨i, by omega⟩ := by
      refine congrArg d.segments (Fin.ext ((adjacentSwap_apply_val d.shape i h01 _).trans ?_))
      dsimp only
      split_ifs <;> omega
    have e2 : (d.permute (d.shape.adjacentSwap i h01)).segments ⟨i + 1 + k + 1, hk'⟩ =
        d.segments ⟨i + (k + 1) + 1, hk⟩ := by
      refine congrArg d.segments (Fin.ext ((adjacentSwap_apply_val d.shape i h01 _).trans ?_))
      dsimp only
      split_ifs <;> omega
    rw [e1, e2] at key
    exact key

/-- Zelevinsky 1980, Theorem 4.2 for segment socles, from the two halves and the
irreducible two-factor case of Theorem 1.9 supplied as explicit hypotheses. -/
theorem segmentSocleProductIrreducibility_of_halves
    (h1 : UnlinkedSegmentSocleProductIrreducible.{uF, uV} F T)
    (h3 : LinkedSegmentSoclePairReducible.{uF, uV} F T)
    (h19 : TwoFactorProductConstituentCommutativity.{uF, max uF uV} F T) :
    SegmentSocleProductIrreducibility.{uF, uV} F T := by
  let := T.topology
  intro n d hs
  constructor
  · intro hirr Δ₁ hΔ₁ Δ₂ hΔ₂
    obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ _).mp (Multiset.mem_coe.mp hΔ₁)
    obtain ⟨b, rfl⟩ := (List.mem_ofFn' _ _).mp (Multiset.mem_coe.mp hΔ₂)
    rcases lt_trichotomy a b with hab | rfl | hab
    · have hk : a.val + (b.val - a.val - 1) + 1 < d.length := by omega
      have key := not_isLinked_of_isIrreducible F T h1 h3 h19 (b.val - a.val - 1) d hs hirr
        a.val hk
      have hb : (⟨a.val + (b.val - a.val - 1) + 1, hk⟩ : Fin d.length) = b := by
        apply Fin.ext
        simp only
        rw [Fin.lt_def] at hab
        omega
      rw [hb] at key
      exact key
    · exact PadicField.TopologicalData.Segment.not_isLinked_self _
    · have hk : b.val + (a.val - b.val - 1) + 1 < d.length := by omega
      have key := not_isLinked_of_isIrreducible F T h1 h3 h19 (a.val - b.val - 1) d hs hirr
        b.val hk
      have ha : (⟨b.val + (a.val - b.val - 1) + 1, hk⟩ : Fin d.length) = a := by
        apply Fin.ext
        simp only
        rw [Fin.lt_def] at hab
        omega
      rw [ha] at key
      exact fun hl => key hl.symm
  · intro hu
    exact h1 n d hs hu

end SegmentSocleCriterionAssembly

end Langlands.Classification

import Langlands.Representation.Geometric.TypeASolomonCoefficientProof
import Langlands.Representation.Aubert.BooleanIntervalComplex

/-! The Boolean interval of cuts with whole target Weyl intersection. -/

noncomputable section

namespace Langlands.Aubert.WholeTarget

open GeneralLinear Geometric Geometric.TypeASolomon

variable {n : ℕ}

/-- Uncut target edges are sent to adjacent increasing coordinates. -/
def BlockEdgeAdjacent (C : BlockShape n) (v : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin (n - 1), i ∉ C.cuts →
    (v (edgeHi i)).val = (v (edgeLo i)).val + 1

/-- Image edges internal to a target block. -/
def blockEdgeImages (C : BlockShape n) (v : Equiv.Perm (Fin n)) :
    Finset (Fin (n - 1)) :=
  Finset.univ.filter fun e =>
    ∃ i : Fin (n - 1), i ∉ C.cuts ∧ e.val = (v (edgeLo i)).val

@[simp] theorem mem_blockEdgeImages (C : BlockShape n) (v : Equiv.Perm (Fin n))
    (e : Fin (n - 1)) :
    e ∈ blockEdgeImages C v ↔
      ∃ i : Fin (n - 1), i ∉ C.cuts ∧ e.val = (v (edgeLo i)).val := by
  simp [blockEdgeImages]

/-- Source cuts may occur precisely outside the images of uncut target edges. -/
def allowedCuts (C : BlockShape n) (v : Equiv.Perm (Fin n)) :
    Finset (Fin (n - 1)) :=
  (blockEdgeImages C v)ᶜ

theorem blockEdgeAdjacent_of_admissible (C : BlockShape n)
    (v : Equiv.Perm (Fin n)) {S : Finset (Fin (n - 1))}
    (h : Admissible C C v S) : BlockEdgeAdjacent C v := by
  intro i hi
  have hm := mt (h.2.2 i hi).mpr hi
  push Not at hm
  obtain ⟨e, he1, he2, _⟩ := hm
  omega

theorem descents_subset_allowedCuts (C : BlockShape n) (v : Equiv.Perm (Fin n))
    (hadj : BlockEdgeAdjacent C v) :
    permutationDescents v.symm ⊆ allowedCuts C v := by
  intro e he
  rw [allowedCuts, Finset.mem_compl, mem_blockEdgeImages]
  rintro ⟨i, hi, hei⟩
  have ha := hadj i hi
  have hlo : v.symm (edgeLo e) = edgeLo i := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext hei
  have hhi : v.symm (edgeHi e) = edgeHi i := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by rw [val_hi, ha, hei])
  rw [mem_descents_iff, hlo, hhi] at he
  exact lt_asymm he (lo_lt_hi i)

/-- Whole-target admissibility is exactly the interval between inverse
descents and the allowed cuts, once the two fixed permutation conditions hold. -/
theorem admissible_iff_interval (C : BlockShape n) (v : Equiv.Perm (Fin n))
    (hinc : SourceIncreasing C v) (hadj : BlockEdgeAdjacent C v)
    (S : Finset (Fin (n - 1))) :
    Admissible C C v S ↔
      CutComplex.BooleanInterval.Active (permutationDescents v.symm) (allowedCuts C v) S := by
  constructor
  · rintro ⟨_, hD, hcl⟩
    refine ⟨hD, ?_⟩
    intro e he
    rw [allowedCuts, Finset.mem_compl, mem_blockEdgeImages]
    rintro ⟨i, hi, hei⟩
    have hnot := mt (hcl i hi).mpr hi
    push Not at hnot
    obtain ⟨e', he'1, _, he'3⟩ := hnot
    have heq : e' = e := Fin.ext (he'1.trans hei.symm)
    exact he'3 (heq ▸ he)
  · rintro ⟨hD, hU⟩
    refine ⟨hinc, hD, fun i hi => ?_⟩
    constructor
    · intro hic
      exact False.elim (hi hic)
    · intro h
      have ha := hadj i hi
      have hb : (v (edgeLo i)).val < n - 1 := by
        have := (v (edgeHi i)).isLt
        omega
      let e : Fin (n - 1) := ⟨(v (edgeLo i)).val, hb⟩
      have he := h e rfl ha.symm
      have hu := hU he
      rw [allowedCuts, Finset.mem_compl, mem_blockEdgeImages] at hu
      exact False.elim (hu ⟨i, hi, rfl⟩)

/-- No permutation conditions are hidden in the interval characterization. -/
theorem admissible_whole_iff (C : BlockShape n) (v : Equiv.Perm (Fin n))
    (S : Finset (Fin (n - 1))) :
    Admissible C C v S ↔
      SourceIncreasing C v ∧ BlockEdgeAdjacent C v ∧
        CutComplex.BooleanInterval.Active (permutationDescents v.symm) (allowedCuts C v) S := by
  constructor
  · intro h
    have ha := blockEdgeAdjacent_of_admissible C v h
    exact ⟨h.1, ha, (admissible_iff_interval C v h.1 ha S).mp h⟩
  · rintro ⟨hi, ha, hs⟩
    exact (admissible_iff_interval C v hi ha S).mpr hs

/-- The actual whole-target Weyl intersection, with the reversed representative
orientation appropriate to the inverse support permutation. -/
theorem wholeTarget_iff_interval (B C : BlockShape n) (v : Equiv.Perm (Fin n)) :
    (IsMinimalRepresentative C B v ∧
      blockWeyl C ⊓ (blockWeyl B).comap (MulAut.conj v).toMonoidHom = blockWeyl C) ↔
      SourceIncreasing C v ∧ BlockEdgeAdjacent C v ∧
        CutComplex.BooleanInterval.Active (permutationDescents v.symm)
          (allowedCuts C v) B.cuts := by
  exact (admissible_iff C B C Finset.Subset.rfl v).trans
    (admissible_whole_iff C v B.cuts)

theorem blockEdgeImages_card (C : BlockShape n) (v : Equiv.Perm (Fin n))
    (hadj : BlockEdgeAdjacent C v) :
    (blockEdgeImages C v).card = C.uncuts.card := by
  symm
  refine Finset.card_bij (fun i hi => ⟨(v (edgeLo i)).val, ?_⟩) ?_ ?_ ?_
  · have hiC : i ∉ C.cuts := (BlockShape.mem_uncuts_iff C i).mp hi
    have ha := hadj i hiC
    have := (v (edgeHi i)).isLt
    omega
  · intro i hi
    rw [mem_blockEdgeImages]
    exact ⟨i, (BlockShape.mem_uncuts_iff C i).mp hi, rfl⟩
  · intro i₁ _ i₂ _ h
    have hv := congrArg Fin.val h
    exact lo_injective (v.injective (Fin.ext hv))
  · intro e he
    obtain ⟨i, hi, hei⟩ := (mem_blockEdgeImages C v e).mp he
    exact ⟨i, (BlockShape.mem_uncuts_iff C i).mpr hi, Fin.ext hei.symm⟩

/-- The largest active degree is the number of target cuts, including rank zero. -/
theorem allowedCuts_card (C : BlockShape n) (v : Equiv.Perm (Fin n))
    (hadj : BlockEdgeAdjacent C v) :
    (allowedCuts C v).card = C.length - 1 := by
  have hc : C.uncuts.card = (n - 1) - C.cuts.card := by
    rw [BlockShape.uncuts, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin]
  have hle : C.cuts.card ≤ n - 1 :=
    (Finset.card_le_card (Finset.subset_univ C.cuts)).trans_eq
      (by simp only [Finset.card_univ, Fintype.card_fin])
  rw [allowedCuts, Finset.card_compl, Fintype.card_fin, blockEdgeImages_card C v hadj,
    hc, Nat.sub_sub_self hle, C.cuts_card]

universe uM

variable (C : BlockShape n) (v : Equiv.Perm (Fin n))
  (M : Type uM) [AddCommGroup M] [Module ℂ M]

/-- The constant coefficient signed cut diagram on the whole-target interval. -/
def diagram : CutComplex.Diagram (Fin (n - 1)) :=
  CutComplex.BooleanInterval.diagram (permutationDescents v.symm) (allowedCuts C v) M

/-- The existing signed insertion differential is exact below the target degree. -/
theorem exact_below_target (hadj : BlockEdgeAdjacent C v) (k : ℕ)
    (hk : k + 1 < C.length - 1) :
    LinearMap.range ((diagram C v M).degreeDifferential k) =
      LinearMap.ker ((diagram C v M).degreeDifferential (k + 1)) := by
  apply CutComplex.BooleanInterval.exact_below_allowed
    (permutationDescents v.symm) (allowedCuts C v) M
    (descents_subset_allowedCuts C v hadj) k
  rwa [allowedCuts_card C v hadj]

/-- The initial signed differential is injective when the target degree is positive. -/
theorem injective_before_target (hadj : BlockEdgeAdjacent C v)
    (hC : 0 < C.length - 1) :
    Function.Injective ((diagram C v M).degreeDifferential 0) := by
  apply CutComplex.BooleanInterval.injective_before_allowed
    (permutationDescents v.symm) (allowedCuts C v) M
    (descents_subset_allowedCuts C v hadj)
  rwa [allowedCuts_card C v hadj]

end Langlands.Aubert.WholeTarget

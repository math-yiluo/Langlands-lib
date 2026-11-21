import Langlands.Shimura.Unitary.SplitPlaceFactors
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Global.AdelicFunctoriality.CompletedRamification
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Oriented completion charts at split finite CM places -/

noncomputable section

universe u v

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped NumberField TensorProduct FiniteExtension WithZero

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  {p : Langlands.Global.FinitePlace E}

namespace SplitPlaceIdentification

variable (h : SplitPlaceIdentification E K p)

/-- Index the specified upper place by zero. -/
def orientedPlacesEquiv (q : FinitePlacesAbove K p) : FinitePlacesAbove K p ≃ Fin 2 :=
  h.placesEquivFinTwo.trans (Equiv.swap (h.placesEquivFinTwo q) 0)

@[simp] theorem orientedPlacesEquiv_apply_self (q : FinitePlacesAbove K p) :
    h.orientedPlacesEquiv q q = 0 := Equiv.swap_apply_left _ _

/-- The other actual upper place at a split place. -/
def otherPlace (q : FinitePlacesAbove K p) : FinitePlacesAbove K p :=
  (h.orientedPlacesEquiv q).symm 1

@[simp] theorem orientedPlacesEquiv_apply_otherPlace (q : FinitePlacesAbove K p) :
    h.orientedPlacesEquiv q (h.otherPlace q) = 1 :=
  (h.orientedPlacesEquiv q).apply_symm_apply 1

theorem otherPlace_ne (q : FinitePlacesAbove K p) : h.otherPlace q ≠ q := by
  intro he
  have h01 := congrArg (h.orientedPlacesEquiv q) he
  simp at h01

theorem eq_or_eq_otherPlace (q r : FinitePlacesAbove K p) : r = q ∨ r = h.otherPlace q := by
  have finTwoCases (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  have hi := finTwoCases (h.orientedPlacesEquiv q r)
  rcases hi with hi | hi
  · exact Or.inl ((h.orientedPlacesEquiv q).injective (hi.trans
      (h.orientedPlacesEquiv_apply_self q).symm))
  · exact Or.inr ((h.orientedPlacesEquiv q).injective (hi.trans
      (h.orientedPlacesEquiv_apply_otherPlace q).symm))

include h in
/-- Both completions above a split place have local degree one. -/
theorem localDegree_eq_one (q : FinitePlacesAbove K p) :
    Module.finrank (FiniteCompletion E p) (FiniteCompletion K q.val) = 1 := by
  classical
  let d (r : FinitePlacesAbove K p) :=
    Module.finrank (FiniteCompletion E p) (FiniteCompletion K r.val)
  have hq : 0 < d q := Module.finrank_pos
  have hother : 0 < d (h.otherPlace q) := Module.finrank_pos
  have hsum : ∑ r, d r ≤ 2 :=
    (IsQuadraticExtension.finrank_eq_two E K) ▸ finiteLocalDegree_sum_le (L := K) p
  have hpair : d q + d (h.otherPlace q) ≤ 2 := calc
    _ = ∑ r ∈ ({q, h.otherPlace q} : Finset (FinitePlacesAbove K p)), d r := by
      rw [Finset.sum_pair (h.otherPlace_ne q).symm]
    _ ≤ ∑ r, d r := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ 2 := hsum
  change d q = 1
  omega

/-- The canonical completion embedding is an equivalence at either upper place. -/
def completionEquiv (q : FinitePlacesAbove K p) :
    FiniteCompletion E p ≃ₐ[FiniteCompletion E p] FiniteCompletion K q.val :=
  AlgEquiv.ofBijective (Algebra.ofId _ _)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp (h.localDegree_eq_one q))

@[simp] theorem completionEquiv_apply (q : FinitePlacesAbove K p) (x : FiniteCompletion E p) :
    h.completionEquiv q x = FiniteExtension.completionMap p q.val x := rfl

theorem continuous_completionEquiv (q : FinitePlacesAbove K p) :
    Continuous (h.completionEquiv q) := FiniteExtension.continuous_completionMap p q.val

theorem continuous_completionEquiv_symm (q : FinitePlacesAbove K p) :
    Continuous (h.completionEquiv q).symm := by
  let : NontriviallyNormedField (FiniteCompletion E p) :=
    Valued.toNontriviallyNormedField (FiniteCompletion E p) ℤᵐ⁰
  exact (h.completionEquiv q).symm.toLinearMap.continuous_of_finiteDimensional

theorem valuation_completionEquiv (q : FinitePlacesAbove K p) (x : FiniteCompletion E p) :
    (Valued.v (h.completionEquiv q x) : ℤᵐ⁰) = Valued.v x := by
  have hprod : q.val.asIdeal.ramificationIdx (𝓞 E) * q.val.asIdeal.inertiaDeg (𝓞 E) = 1 :=
    (AdelicFunctoriality.localDegree_eq p q.val).symm.trans (h.localDegree_eq_one q)
  have hram : q.val.asIdeal.ramificationIdx (𝓞 E) = 1 :=
    Nat.dvd_one.mp (hprod ▸ dvd_mul_right _ _)
  rw [completionEquiv_apply, FiniteExtension.valuation_completionMap, hram, pow_one]

/-- The canonical identification of two upper completions over the base completion. -/
def completionEquivBetween (q r : FinitePlacesAbove K p) :
    FiniteCompletion K q.val ≃ₐ[FiniteCompletion E p] FiniteCompletion K r.val :=
  (h.completionEquiv q).symm.trans (h.completionEquiv r)

theorem continuous_completionEquivBetween (q r : FinitePlacesAbove K p) :
    Continuous (h.completionEquivBetween q r) :=
  (h.continuous_completionEquiv r).comp (h.continuous_completionEquiv_symm q)

theorem valuation_completionEquivBetween (q r : FinitePlacesAbove K p)
    (x : FiniteCompletion K q.val) :
    (Valued.v (h.completionEquivBetween q r x) : ℤᵐ⁰) = Valued.v x := by
  obtain ⟨y, rfl⟩ := (h.completionEquiv q).surjective x
  change Valued.v (h.completionEquiv r ((h.completionEquiv q).symm (h.completionEquiv q y))) = _
  rw [AlgEquiv.symm_apply_apply, valuation_completionEquiv, valuation_completionEquiv]

private theorem completedCenterMap_eq_finiteTensorMap (q : FinitePlacesAbove K p)
    (z : LocalCenter E K p) :
    completedCenterMap E K p q.val z = finiteTensorMap (L := K) p z q := by
  induction z using TensorProduct.inductionOn with
  | tmul x a => rw [completedCenterMap_tmul, finiteTensorMap_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

private def orientedCenterEquiv (q : FinitePlacesAbove K p) :
    LocalCenter E K p ≃ₐ[FiniteCompletion E p] (FiniteCompletion E p × FiniteCompletion E p) :=
  let e := AlgEquiv.ofBijective (finiteTensorMap (L := K) p)
    ((completedTensorComparison E K).1 p)
  let f := AlgEquiv.piCongrRight (fun r : FinitePlacesAbove K p => (h.completionEquiv r).symm)
  let g := AlgEquiv.piCongrLeft' (FiniteCompletion E p) (fun _ => FiniteCompletion E p)
    (h.orientedPlacesEquiv q)
  let prod := AlgEquiv.ofRingEquiv (f := RingEquiv.piFinTwo (fun _ => FiniteCompletion E p))
    (fun _ => rfl)
  e.trans (f.trans (g.trans prod))

private theorem prodEquiv_swap {F : Type*} [Field F]
    (e : (F × F) ≃ₐ[F] (F × F)) (z : F × F) : e z.swap = (e z).swap := by
  have htrace : (e z).1 + (e z).2 = z.1 + z.2 := by
    simpa only [Algebra.trace_prod_apply, Algebra.trace_self_apply] using
      Algebra.trace_eq_of_algEquiv e z
  have hswap (x : F × F) : x.swap = algebraMap F (F × F) (x.1 + x.2) - x := by
    ext <;> simp
  rw [hswap z, map_sub, e.commutes, hswap (e z), htrace]

/-- The split chart whose first coordinate corresponds to the specified upper place. -/
def oriented (q : FinitePlacesAbove K p) : SplitPlaceIdentification E K p where
  equiv := h.orientedCenterEquiv q
  conjugation_eq z := by
    let e := h.equiv.symm.trans (h.orientedCenterEquiv q)
    have he (x : LocalCenter E K p) : e (h.equiv x) = h.orientedCenterEquiv q x := by
      simp [e]
    rw [← he, h.conjugation_eq, prodEquiv_swap, he]

@[simp] theorem oriented_fst (q : FinitePlacesAbove K p) (z : LocalCenter E K p) :
    ((h.oriented q).equiv z).1 = (h.completionEquiv q).symm (completedCenterMap E K p q.val z) := by
  have h0 : (h.orientedPlacesEquiv q).symm 0 = q :=
    (h.orientedPlacesEquiv q).symm_apply_eq.mpr (h.orientedPlacesEquiv_apply_self q).symm
  change (h.completionEquiv ((h.orientedPlacesEquiv q).symm 0)).symm
    (finiteTensorMap (L := K) p z ((h.orientedPlacesEquiv q).symm 0)) = _
  rw [completedCenterMap_eq_finiteTensorMap]
  exact congrArg (fun r => (h.completionEquiv r).symm (finiteTensorMap (L := K) p z r)) h0

@[simp] theorem oriented_snd (q : FinitePlacesAbove K p) (z : LocalCenter E K p) :
    ((h.oriented q).equiv z).2 = (h.completionEquiv (h.otherPlace q)).symm
      (completedCenterMap E K p (h.otherPlace q).val z) := by
  change (h.completionEquiv (h.otherPlace q)).symm
    (finiteTensorMap (L := K) p z (h.otherPlace q)) = _
  rw [completedCenterMap_eq_finiteTensorMap]

end SplitPlaceIdentification

end Langlands.Shimura.FiniteUnitary

import Langlands.TraceFormula.FinitePlacePositiveTensor
import Langlands.TraceFormula.GeneralLinearBaseChangeLocal

/-! # The exterior factor of a restricted adelic tensor -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global AdelicGroupPoints PositiveRealTorus Langlands.GroupScheme

universe u

variable (K : Type u) [Field K] [NumberField K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffine G.X.left]
  (v : FinitePlace K) (S : Finset (Place K))
  (U : (i : Place K) → Subgroup (PlaceGroupPoints K G i))
  (g : (i : Place K) → PlaceGroupPoints K G i → ℂ)

local instance : DecidableEq (Place K) := Classical.decEq _

/-- The product of the components other than `v` of a restricted tensor with `v` in `S`. -/
def finitePlaceExteriorFactor (x : AdelicGroupPoints K G) : ℂ :=
  {y : AdelicGroupPoints K G | ∀ i ∉ S, atPlace K G i y ∈ U i}.indicator
    (fun y => ∏ i ∈ S.erase (.inr v), g i (atPlace K G i y)) x

/-- In a restricted tensor, changing the test at `v` leaves the exterior factor
unchanged. Right translation by a point inserted at `v` fixes this factor. -/
def AdelicFinitePlaceExteriorStatement : Prop :=
  (Sum.inr v : Place K) ∈ S →
    let exterior := finitePlaceExteriorFactor K G v S U g
    (∀ z x, exterior (z * finitePlacePointInclusion K G v x) = exterior z) ∧
    ∀ (f : AdelicGroupPoints K G → ℂ)
      (fLoc : (i : Place K) → PlaceGroupPoints K G i → ℂ),
      IsAdelicFactorization K S fLoc U f → (∀ i ∈ S.erase (.inr v), fLoc i = g i) →
      f = fun z => fLoc (.inr v) (atPlace K G (.inr v) z) * exterior z

theorem adelicFinitePlaceExterior : AdelicFinitePlaceExteriorStatement K G v S U g := by
  classical
  intro hv exterior
  let C : Set (AdelicGroupPoints K G) := {y | ∀ i ∉ S, atPlace K G i y ∈ U i}
  constructor
  · intro z x
    have hAway (i : Place K) (hi : i ≠ .inr v) :
        atPlace K G i (z * finitePlacePointInclusion K G v x) = atPlace K G i z := by
      rw [map_mul, atPlace_finitePlacePointInclusion_of_ne K G v i hi, mul_one]
    have hC : z * finitePlacePointInclusion K G v x ∈ C ↔ z ∈ C := by
      change (∀ i ∉ S, _) ↔ (∀ i ∉ S, _)
      apply forall_congr'
      intro i
      apply imp_congr_right
      intro hi
      rw [hAway i (fun h => hi (h.symm ▸ hv))]
    change C.indicator _ _ = C.indicator _ _
    by_cases hz : z ∈ C
    · rw [Set.indicator_of_mem (hC.mpr hz), Set.indicator_of_mem hz]
      exact Finset.prod_congr rfl fun i hi => congrArg (g i) (hAway i (Finset.ne_of_mem_erase hi))
    · rw [Set.indicator_of_notMem (hC.not.mpr hz), Set.indicator_of_notMem hz]
  · intro f fLoc hf hLoc
    funext z
    rw [hf z]
    change C.indicator _ z = _ * C.indicator _ z
    by_cases hz : z ∈ C
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz,
        ← Finset.mul_prod_erase _ _ hv]
      exact congrArg (fLoc (.inr v) (atPlace K G (.inr v) z) * ·)
        (Finset.prod_congr rfl (fun i hi => congrFun (hLoc i hi) _))
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]

variable (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G)

omit [IsAffine G.X.left] in
/-- A nonzero positive-torus average of a finite-place tensor has nonzero
value in the distinguished local factor. -/
theorem localFactor_ne_zero_of_normOnePositiveAverage (hT : IsSplitTorus T.toGrp)
    (ρ : Measure (intrinsicSubgroup K T)) (fv : PlaceGroupPoints K G (.inr v) → ℂ)
    (fw : AdelicGroupPoints K G → ℂ) (z : normOneSubgroup K G)
    (hz : normOnePositiveAverage K G T i ρ
      (fun x => fv (atPlace K G (.inr v) x) * fw x) z ≠ 0) :
    fv (atPlace K G (.inr v) z) ≠ 0 := by
  intro h
  apply hz
  unfold normOnePositiveAverage
  simp only [atPlace_positivePointMap_mul K G T i hT v, h, zero_mul, integral_zero]

end Langlands.TraceFormula

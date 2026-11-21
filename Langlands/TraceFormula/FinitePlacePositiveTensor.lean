import Langlands.TraceFormula.NormOneFinitePlaceSplit
import Langlands.Global.AdelicSplitCenterHaar

/-! # Positive-torus averaging of a finite-place tensor -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme

universe u

variable (K : Type u) [Field K] [NumberField K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (v : Langlands.Global.FinitePlace K)
  (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
  (hc : IsCentral i)

/-- Integrate a full adelic function along the positive torus at a norm-one point. -/
def normOnePositiveAverage (ρ : Measure (intrinsicSubgroup K T))
    (f : AdelicGroupPoints K G → ℂ) (x : normOneSubgroup K G) : ℂ :=
  ∫ a, f (positivePointMap K G T i a * (x : AdelicGroupPoints K G)) ∂ρ

set_option maxRecDepth 2200 in
/-- Positive-torus averaging keeps the distinguished local factor and
averages the exterior function on the kernel of the local projection. -/
def FinitePlacePositiveTensorStatement : Prop :=
  ∀ (fv : PlaceGroupPoints K G (.inr v) → ℂ) (fw : AdelicGroupPoints K G → ℂ),
    (∀ z x, fw (z * finitePlacePointInclusion K G v x) = fw z) →
    let ρ := normalizedPositiveHaarMeasure K G T i hi I e hc
    let D := normOneFinitePlaceDecomposition K G v T i hi I e hc
    ∀ p : PlaceGroupPoints K G (.inr v) × (normOneFinitePlaceProjection K G v).toMonoidHom.ker,
      normOnePositiveAverage K G T i ρ (fun x => fv (atPlace K G (.inr v) x) * fw x) (D p) =
        fv p.1 * normOnePositiveAverage K G T i ρ fw p.2.val

set_option maxRecDepth 2400 in
set_option maxHeartbeats 1700000 in
theorem finitePlacePositiveTensor : FinitePlacePositiveTensorStatement K G v T i hi I e hc := by
  intro fv fw hfw ρ D p
  let P := positivePointMap K G T i
  let q := atPlace K G (.inr v)
  let A := AdelicGroupPoints K G
  let d := finitePlacePointInclusion K G v p.1
  let b := positiveFactor K G T i hi I e d
  let z : A := p.2.val
  have hD : (D p : A) = ((P b)⁻¹ * d) * z := by
    change (normOneFactor K G T i hi I e d : A) * z = _
    rw [normOneFactor_val]
  have hcomm : d * z = z * d := by
    apply ext_atPlace K G
    intro j
    rw [map_mul, map_mul]
    by_cases hj : j = .inr v
    · subst j
      have hz : atPlace K G (.inr v) z = 1 := p.2.property
      rw [hz, mul_one, one_mul]
    · have hd := atPlace_finitePlacePointInclusion_of_ne K G v j hj p.1
      change atPlace K G j d = 1 at hd
      rw [hd, one_mul, mul_one]
  have htransport (a : intrinsicSubgroup K T) :
      P a * (D p : A) = P (a * b⁻¹) * z * d := by
    rw [hD, map_mul, map_inv]
    simp only [mul_assoc, hcomm]
  have hψ (a : intrinsicSubgroup K T) :
      fw (P a * (D p : A)) = fw (P (a * b⁻¹) * z) :=
    (congrArg fw (htransport a)).trans (hfw _ p.1)
  have hq (a : intrinsicSubgroup K T) : q (P a * (D p : A)) = p.1 := by
    have hT : IsSplitTorus T.toGrp := ⟨I, inferInstance, ⟨e⟩⟩
    change atPlace K G (.inr v) (positivePointMap K G T i a * (D p : A)) = p.1
    rw [atPlace_positivePointMap_mul K G T i hT v]
    change normOneFinitePlaceProjection K G v (D p) = p.1
    exact (normOneFinitePlaceDecomposition_symm_fst K G v T i hi I e hc (D p)).symm.trans
      (congrArg Prod.fst (D.symm_apply_apply p))
  let := positiveIsTopologicalGroup K T I e
  let := normalizedPositiveHaarMeasure_isMulRightInvariant K G T i hi I e hc
  unfold normOnePositiveAverage
  calc
    _ = ∫ a, fv p.1 * fw (P (a * b⁻¹) * z) ∂ρ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun a => by
        change fv (q (P a * (D p : A))) * fw (P a * (D p : A)) = _
        rw [hq a, hψ a])
    _ = _ := by
      rw [integral_const_mul]
      have hright := integral_mul_right_eq_self («μ» := ρ) (fun a => fw (P a * z)) (b⁻¹)
      exact congrArg (fun t => fv p.1 * t) hright

end Langlands.TraceFormula

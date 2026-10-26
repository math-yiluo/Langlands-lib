import Langlands.Geometry.Analytic.StrictTestDomain.RationalPullbackProof
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Algebraic tensor comparison for actual rational base change -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalData

open scoped TensorProduct

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P Q : PresentedStrictAffinoidAlgebra K} (d : RationalData K P)
  (φ : BoundedAlgHom K P Q)

/-- The ordinary algebraic tensor product formed using the two actual base
maps. No norm or completion is imposed on this tensor product. -/
def algebraicBaseChange : Type u :=
  letI : Algebra P d.algebra := d.baseMap.toAlgHom.toRingHom.toAlgebra
  letI : Algebra P Q := φ.toAlgHom.toRingHom.toAlgebra
  d.algebra ⊗[P] Q

instance algebraicBaseChangeCommRing : CommRing (d.algebraicBaseChange φ) := by
  letI : Algebra P d.algebra := d.baseMap.toAlgHom.toRingHom.toAlgebra
  letI : Algebra P Q := φ.toAlgHom.toRingHom.toAlgebra
  change CommRing (d.algebra ⊗[P] Q)
  infer_instance

/-- The left map into the actual algebraic base change. -/
def tensorLeft : d.algebra →+* d.algebraicBaseChange φ := by
  letI : Algebra P d.algebra := d.baseMap.toAlgHom.toRingHom.toAlgebra
  letI : Algebra P Q := φ.toAlgHom.toRingHom.toAlgebra
  exact Algebra.TensorProduct.includeLeftRingHom

/-- The right map into the actual algebraic base change. -/
def tensorRight : Q →+* d.algebraicBaseChange φ := by
  letI : Algebra P d.algebra := d.baseMap.toAlgHom.toRingHom.toAlgebra
  letI : Algebra P Q := φ.toAlgHom.toRingHom.toAlgebra
  exact Algebra.TensorProduct.includeRight.toRingHom

/-- The two tensor factors agree on the precise original base. -/
theorem tensorLeft_comp_baseMap :
    (d.tensorLeft φ).comp d.baseMap.toAlgHom.toRingHom =
      (d.tensorRight φ).comp φ.toAlgHom.toRingHom := by
  let : Algebra P d.algebra := d.baseMap.toAlgHom.toRingHom.toAlgebra
  let : Algebra P Q := φ.toAlgHom.toRingHom.toAlgebra
  exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap

/-- The canonical comparison to the constructed rational quotient after
base change, induced by its two already constructed bounded factor maps. -/
def tensorComparison : d.algebraicBaseChange φ →+* (d.pullback φ).algebra := by
  letI : Algebra P d.algebra := d.baseMap.toAlgHom.toRingHom.toAlgebra
  letI : Algebra P Q := φ.toAlgHom.toRingHom.toAlgebra
  letI : Algebra P (d.pullback φ).algebra :=
    ((d.pullback φ).baseMap.comp φ).toAlgHom.toRingHom.toAlgebra
  let a : d.algebra →ₐ[P] (d.pullback φ).algebra :=
    { (d.comparison φ).toAlgHom.toRingHom with
      commutes' := fun x => congrArg (fun h : BoundedAlgHom K P (d.pullback φ).algebra =>
        h x) (d.comparison_comp_baseMap φ) }
  let b : Q →ₐ[P] (d.pullback φ).algebra :=
    { (d.pullback φ).baseMap.toAlgHom.toRingHom with commutes' := fun _ => rfl }
  exact (Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _)).toRingHom

@[simp]
theorem tensorComparison_tensorLeft (a : d.algebra) :
    d.tensorComparison φ (d.tensorLeft φ a) = d.comparison φ a := by
  change d.comparison φ a * (d.pullback φ).baseMap 1 = _
  simp

@[simp]
theorem tensorComparison_tensorRight (b : Q) :
    d.tensorComparison φ (d.tensorRight φ b) = (d.pullback φ).baseMap b := by
  change d.comparison φ 1 * (d.pullback φ).baseMap b = _
  simp

/-- Evaluation on products of the two factor maps, hence on pure tensors. -/
theorem tensorComparison_mul (a : d.algebra) (b : Q) :
    d.tensorComparison φ (d.tensorLeft φ a * d.tensorRight φ b) =
      d.comparison φ a * (d.pullback φ).baseMap b := by
  rw [map_mul, tensorComparison_tensorLeft, tensorComparison_tensorRight]

/-- Fractions with powers of the denominator are dense for the actual
rational quotient of any presented strict affinoid algebra. -/
theorem dense_fractionSubalgebra :
    Dense (fractionSubalgebra K d.baseMap.toAlgHom d.denominator :
      Set d.algebra) := by
  let b : BoundedAlgHom K (RationalLocalization.model K P) d.algebra :=
    RationalPresentation.baseMap K P.arity d.arity P.ideal
      (RationalLocalization.seriesLift K P d.denominator)
      (fun j => RationalLocalization.seriesLift K P (d.numerator j))
  have hd := RationalPresentation.dense_fractionSubalgebra K P.arity d.arity P.ideal
    (RationalLocalization.seriesLift K P d.denominator)
    (fun j => RationalLocalization.seriesLift K P (d.numerator j))
  change Dense (fractionSubalgebra K b.toAlgHom
    (PresentedStrictAffinoidAlgebra.presentationMap K (RationalLocalization.model K P)
      (RationalLocalization.seriesLift K P d.denominator)) : Set d.algebra) at hd
  apply hd.mono
  rintro x ⟨r, a, ha⟩
  refine ⟨r, RationalLocalization.modelEquiv K P a, ?_⟩
  change b ((RationalLocalization.modelEquiv K P).symm d.denominator) ^ r * x =
    b ((RationalLocalization.modelEquiv K P).symm
        (RationalLocalization.modelEquiv K P a))
  rw [BoundedAlgEquiv.symm_apply_apply]
  simpa only [RationalLocalization.presentationMap_seriesLift] using ha

/-- Every algebraic fraction in the pulled-back rational quotient is already
in the image of the ordinary tensor comparison. -/
theorem fractionSubalgebra_subset_range_tensorComparison :
    (fractionSubalgebra K (d.pullback φ).baseMap.toAlgHom
      (d.pullback φ).denominator : Set (d.pullback φ).algebra) ⊆
      Set.range (d.tensorComparison φ) := by
  have hu : IsUnit (d.baseMap d.denominator) :=
    RationalLocalization.isUnit_baseMap_denominator K P d.arity
      d.denominator d.numerator d.generatesUnitIdeal
  obtain ⟨s, hs⟩ := hu.exists_right_inv
  have hs' : (d.pullback φ).baseMap (φ d.denominator) * d.comparison φ s = 1 := by
    have hbase := congrArg (fun h : BoundedAlgHom K P (d.pullback φ).algebra =>
      h d.denominator) (d.comparison_comp_baseMap φ)
    change d.comparison φ (d.baseMap d.denominator) =
      (d.pullback φ).baseMap (φ d.denominator) at hbase
    rw [← hbase, ← map_mul, hs, map_one]
  rintro x ⟨r, b, hb⟩
  refine ⟨d.tensorLeft φ s ^ r * d.tensorRight φ b, ?_⟩
  rw [map_mul, map_pow, tensorComparison_tensorLeft, tensorComparison_tensorRight]
  have hunit : IsUnit ((d.pullback φ).baseMap (φ d.denominator) ^ r) :=
    (IsUnit.of_mul_eq_one (d.comparison φ s) hs').pow r
  apply hunit.mul_left_cancel
  calc
    (d.pullback φ).baseMap (φ d.denominator) ^ r *
        (d.comparison φ s ^ r * (d.pullback φ).baseMap b) =
      ((d.pullback φ).baseMap (φ d.denominator) * d.comparison φ s) ^ r *
        (d.pullback φ).baseMap b := by rw [mul_pow]; ring
    _ = (d.pullback φ).baseMap b := by rw [hs']; simp
    _ = (d.pullback φ).baseMap (φ d.denominator) ^ r * x := hb.symm

/-- The canonical algebraic tensor comparison has dense image. This does
not assert injectivity, surjectivity or any completion isomorphism. -/
theorem denseRange_tensorComparison : DenseRange (d.tensorComparison φ) :=
  (d.pullback φ).dense_fractionSubalgebra.mono
    (d.fractionSubalgebra_subset_range_tensorComparison φ)

end Langlands.Analytic.StrictTestDomain.RationalData

import Langlands.Global.AdelicNormOneDecomposition
import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Analysis.Local.QuotientMeasureEquiv
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Prod

/-! # Haar measure and exact normalization of actual positive/norm-one factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal Topology

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]

section Coordinates

variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (I : Type u) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

/-- Borel sets of finite real logarithmic coordinates, with addition written multiplicatively. -/
instance logCoordinateMeasurableSpace : MeasurableSpace (Multiplicative (I → ℝ)) :=
  borel _

instance logCoordinateBorelSpace : BorelSpace (Multiplicative (I → ℝ)) := ⟨rfl⟩

/-- Actual positive points have finite real logarithmic group coordinates. -/
def positiveLogCoordinateEquiv :
    intrinsicSubgroup F T ≃ₜ* Multiplicative (I → ℝ) :=
  (positiveLogEquiv F T I e).trans {
    toFun := fun ℓ => Multiplicative.ofAdd (dualCoordinatesContinuousEquiv F T I e ℓ.toAdd)
    invFun := fun v =>
      Multiplicative.ofAdd ((dualCoordinatesContinuousEquiv F T I e).symm v.toAdd)
    left_inv := fun ℓ => (dualCoordinatesContinuousEquiv F T I e).left_inv ℓ.toAdd
    right_inv := fun v => (dualCoordinatesContinuousEquiv F T I e).right_inv v.toAdd
    map_mul' := fun ℓ m =>
      (dualCoordinatesContinuousEquiv F T I e).map_add ℓ.toAdd m.toAdd
    continuous_toFun := (dualCoordinatesContinuousEquiv F T I e).continuous
    continuous_invFun := (dualCoordinatesContinuousEquiv F T I e).symm.continuous }

include I e in
/-- The existing subtype topology makes the actual positive subgroup a topological group. -/
theorem positiveIsTopologicalGroup : IsTopologicalGroup (intrinsicSubgroup F T) :=
  (positiveLogCoordinateEquiv F T I e).toHomeomorph.isInducing.isTopologicalGroup
    (positiveLogCoordinateEquiv F T I e)

include I e in
/-- Local compactness is transferred to the existing positive subgroup topology. -/
theorem positiveLocallyCompactSpace : LocallyCompactSpace (intrinsicSubgroup F T) :=
  (positiveLogCoordinateEquiv F T I e).toHomeomorph.isClosedEmbedding.locallyCompactSpace

include I e in
/-- The actual positive subgroup is second countable, including in rank zero. -/
theorem positiveSecondCountableTopology : SecondCountableTopology (intrinsicSubgroup F T) :=
  (positiveLogCoordinateEquiv F T I e).toHomeomorph.secondCountableTopology

/-- Push finite real-coordinate Haar measure to the actual intrinsic positive subgroup. -/
def positiveHaarMeasure : Measure (intrinsicSubgroup F T) :=
  Measure.map (positiveLogCoordinateEquiv F T I e).symm
    (Measure.haar : Measure (Multiplicative (I → ℝ)))

theorem positiveHaarMeasure_isHaarMeasure :
    (positiveHaarMeasure F T I e).IsHaarMeasure := by
  let := positiveIsTopologicalGroup F T I e
  exact (positiveLogCoordinateEquiv F T I e).symm.isHaarMeasure_map _

theorem positiveHaarMeasure_sigmaFinite : SigmaFinite (positiveHaarMeasure F T I e) := by
  let := positiveLocallyCompactSpace F T I e
  let := positiveSecondCountableTopology F T I e
  let := positiveHaarMeasure_isHaarMeasure F T I e
  infer_instance

theorem positiveHaarMeasure_regular : (positiveHaarMeasure F T I e).Regular := by
  exact Measure.Regular.map (positiveLogCoordinateEquiv F T I e).symm.toHomeomorph

/-- Commutativity of logarithmic coordinates supplies actual positive right invariance. -/
theorem positiveHaarMeasure_isMulRightInvariant :
    (positiveHaarMeasure F T I e).IsMulRightInvariant := by
  let := positiveIsTopologicalGroup F T I e
  exact Langlands.QuotientIntegration.isMulRightInvariant_map
    (positiveLogCoordinateEquiv F T I e).symm _

end Coordinates

variable (G : GroupScheme (Spec (CommRingCat.of F)))
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (i : T.toGrp ⟶ G)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (I : Type u) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Push the actual positive and norm-one Haar product through actual multiplication. -/
def decompositionHaarMeasure : Measure (AdelicGroupPoints F G) :=
  Measure.map (normOneDecomposition F G T i hi I e)
    ((positiveHaarMeasure F T I e).prod (Measure.haar : Measure (normOneSubgroup F G)))

include hi I e in
theorem decompositionHaarMeasure_isHaarMeasure (hc : IsCentral i) :
    (decompositionHaarMeasure F G T i hi I e).IsHaarMeasure := by
  let := positiveIsTopologicalGroup F T I e
  let := positiveHaarMeasure_isHaarMeasure F T I e
  let := positiveHaarMeasure_sigmaFinite F T I e
  change IsHaarMeasure (Measure.map (normOneDecompositionMulEquiv F G T i hi I e hc)
    ((positiveHaarMeasure F T I e).prod (Measure.haar : Measure (normOneSubgroup F G))))
  exact (normOneDecompositionMulEquiv F G T i hi I e hc).isHaarMeasure_map _

/-- The exact positive scalar relating the constructed product to existing ambient Haar. -/
def decompositionHaarScalar (hc : IsCentral i) : ℝ≥0 := by
  let := decompositionHaarMeasure_isHaarMeasure F G T i hi I e hc
  exact Measure.haarScalarFactor (decompositionHaarMeasure F G T i hi I e)
    (Measure.haar : Measure (AdelicGroupPoints F G))

theorem decompositionHaarScalar_pos (hc : IsCentral i) :
    0 < decompositionHaarScalar F G T i hi I e hc := by
  let := decompositionHaarMeasure_isHaarMeasure F G T i hi I e hc
  exact Measure.haarScalarFactor_pos_of_isHaarMeasure _ _

theorem decompositionHaarMeasure_eq_smul (hc : IsCentral i) :
    decompositionHaarMeasure F G T i hi I e =
      decompositionHaarScalar F G T i hi I e hc •
        (Measure.haar : Measure (AdelicGroupPoints F G)) := by
  let := decompositionHaarMeasure_isHaarMeasure F G T i hi I e hc
  exact Measure.isMulLeftInvariant_eq_smul _ _

/-- Rescale only positive Haar, keeping the existing norm-one Haar fixed. -/
def normalizedPositiveHaarMeasure (hc : IsCentral i) : Measure (intrinsicSubgroup F T) :=
  (decompositionHaarScalar F G T i hi I e hc)⁻¹ • positiveHaarMeasure F T I e

theorem normalizedPositiveHaarMeasure_isHaarMeasure (hc : IsCentral i) :
    (normalizedPositiveHaarMeasure F G T i hi I e hc).IsHaarMeasure := by
  let := positiveIsTopologicalGroup F T I e
  let := positiveHaarMeasure_isHaarMeasure F T I e
  exact IsHaarMeasure.nnreal_smul _ (inv_ne_zero (decompositionHaarScalar_pos
    F G T i hi I e hc).ne')

theorem normalizedPositiveHaarMeasure_sigmaFinite (hc : IsCentral i) :
    SigmaFinite (normalizedPositiveHaarMeasure F G T i hi I e hc) := by
  let := positiveHaarMeasure_sigmaFinite F T I e
  unfold normalizedPositiveHaarMeasure
  infer_instance

theorem normalizedPositiveHaarMeasure_regular (hc : IsCentral i) :
    (normalizedPositiveHaarMeasure F G T i hi I e hc).Regular := by
  let := positiveHaarMeasure_regular F T I e
  unfold normalizedPositiveHaarMeasure
  infer_instance

theorem normalizedPositiveHaarMeasure_isMulRightInvariant (hc : IsCentral i) :
    (normalizedPositiveHaarMeasure F G T i hi I e hc).IsMulRightInvariant := by
  let := positiveIsTopologicalGroup F T I e
  let := positiveHaarMeasure_isMulRightInvariant F T I e
  unfold normalizedPositiveHaarMeasure
  infer_instance

/-- With norm-one Haar unchanged, the normalized product is exactly ambient Haar. -/
theorem map_normalizedPositiveHaarMeasure_prod (hc : IsCentral i) :
    Measure.map (normOneDecomposition F G T i hi I e)
      ((normalizedPositiveHaarMeasure F G T i hi I e hc).prod
        (Measure.haar : Measure (normOneSubgroup F G))) =
      (Measure.haar : Measure (AdelicGroupPoints F G)) := by
  rw [normalizedPositiveHaarMeasure, Measure.prod_smul_left,
    Measure.map_smul _ (normOneDecomposition F G T i hi I e).continuous.measurable.aemeasurable]
  change (decompositionHaarScalar F G T i hi I e hc)⁻¹ •
    decompositionHaarMeasure F G T i hi I e = _
  rw [decompositionHaarMeasure_eq_smul F G T i hi I e hc, smul_smul,
    inv_mul_cancel₀ (decompositionHaarScalar_pos F G T i hi I e hc).ne', one_smul]

/-- Multiplication preserves the exact normalized product and existing ambient Haar. -/
theorem measurePreserving_normOneDecomposition (hc : IsCentral i) :
    MeasurePreserving (normOneDecomposition F G T i hi I e)
      ((normalizedPositiveHaarMeasure F G T i hi I e hc).prod
        (Measure.haar : Measure (normOneSubgroup F G)))
      (Measure.haar : Measure (AdelicGroupPoints F G)) :=
  ⟨(normOneDecomposition F G T i hi I e).continuous.measurable,
    map_normalizedPositiveHaarMeasure_prod F G T i hi I e hc⟩

/-- The actual positive/norm-one coordinate map preserves the same normalization. -/
theorem measurePreserving_normOneDecomposition_symm (hc : IsCentral i) :
    MeasurePreserving (normOneDecomposition F G T i hi I e).symm
      (Measure.haar : Measure (AdelicGroupPoints F G))
      ((normalizedPositiveHaarMeasure F G T i hi I e hc).prod
        (Measure.haar : Measure (normOneSubgroup F G))) :=
  MeasurePreserving.symm (normOneDecomposition F G T i hi I e).toMeasurableEquiv
    (measurePreserving_normOneDecomposition F G T i hi I e hc)

/-- Ambient complex convergence is exactly convergence in the actual product coordinates. -/
theorem integrable_normOneDecomposition_iff (hc : IsCentral i)
    (f : AdelicGroupPoints F G → ℂ) :
    Integrable f (Measure.haar : Measure (AdelicGroupPoints F G)) ↔
      Integrable (fun p : intrinsicSubgroup F T × normOneSubgroup F G =>
        f (positivePointMap F G T i p.1 * p.2))
        ((normalizedPositiveHaarMeasure F G T i hi I e hc).prod Measure.haar) := by
  rw [← map_normalizedPositiveHaarMeasure_prod F G T i hi I e hc]
  exact integrable_map_equiv (normOneDecomposition F G T i hi I e).toMeasurableEquiv f

/-- Equality of total Bochner integrals, independently of the convergence assertion. -/
theorem integral_normOneDecomposition (hc : IsCentral i)
    (f : AdelicGroupPoints F G → ℂ) :
    (∫ x, f x ∂(Measure.haar : Measure (AdelicGroupPoints F G))) =
      ∫ p : intrinsicSubgroup F T × normOneSubgroup F G,
        f (positivePointMap F G T i p.1 * p.2)
        ∂((normalizedPositiveHaarMeasure F G T i hi I e hc).prod Measure.haar) := by
  rw [← map_normalizedPositiveHaarMeasure_prod F G T i hi I e hc]
  exact integral_map_equiv (normOneDecomposition F G T i hi I e).toMeasurableEquiv f

/-- For a convergent ambient integral, integrate norm-one points first. -/
theorem integral_normOneDecomposition_fubini (hc : IsCentral i)
    (f : AdelicGroupPoints F G → ℂ)
    (hf : Integrable f (Measure.haar : Measure (AdelicGroupPoints F G))) :
    (∫ x, f x ∂(Measure.haar : Measure (AdelicGroupPoints F G))) =
      ∫ a : intrinsicSubgroup F T, ∫ n : normOneSubgroup F G,
        f (positivePointMap F G T i a * n) ∂Measure.haar
        ∂normalizedPositiveHaarMeasure F G T i hi I e hc := by
  let := normalizedPositiveHaarMeasure_sigmaFinite F G T i hi I e hc
  exact (integral_normOneDecomposition F G T i hi I e hc f).trans
    (integral_prod _ ((integrable_normOneDecomposition_iff F G T i hi I e hc f).mp hf))

/-- For a convergent ambient integral, integrate actual positive points first. -/
theorem integral_normOneDecomposition_fubini_symm (hc : IsCentral i)
    (f : AdelicGroupPoints F G → ℂ)
    (hf : Integrable f (Measure.haar : Measure (AdelicGroupPoints F G))) :
    (∫ x, f x ∂(Measure.haar : Measure (AdelicGroupPoints F G))) =
      ∫ n : normOneSubgroup F G, ∫ a : intrinsicSubgroup F T,
        f (positivePointMap F G T i a * n)
        ∂normalizedPositiveHaarMeasure F G T i hi I e hc ∂Measure.haar := by
  let := normalizedPositiveHaarMeasure_sigmaFinite F G T i hi I e hc
  exact (integral_normOneDecomposition F G T i hi I e hc f).trans
    (integral_prod_symm _ ((integrable_normOneDecomposition_iff F G T i hi I e hc f).mp hf))

include hi I e in
/-- Norm-one Haar right invariance suffices for ambient Haar right invariance
under this actual central direct-product decomposition. -/
theorem ambientHaar_isMulRightInvariant (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant] :
    (Measure.haar : Measure (AdelicGroupPoints F G)).IsMulRightInvariant := by
  let := positiveIsTopologicalGroup F T I e
  let := normalizedPositiveHaarMeasure_sigmaFinite F G T i hi I e hc
  let := normalizedPositiveHaarMeasure_isMulRightInvariant F G T i hi I e hc
  rw [← map_normalizedPositiveHaarMeasure_prod F G T i hi I e hc]
  change IsMulRightInvariant (Measure.map (normOneDecompositionMulEquiv F G T i hi I e hc)
    ((normalizedPositiveHaarMeasure F G T i hi I e hc).prod
      (Measure.haar : Measure (normOneSubgroup F G))))
  exact Langlands.QuotientIntegration.isMulRightInvariant_map _ _

end Langlands.Global.PositiveRealTorus

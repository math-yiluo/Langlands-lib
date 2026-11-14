import Langlands.GroupScheme.IntegralModel.FiniteInnerUnramifiedSolution
import Langlands.GroupScheme.IntegralModel.CoefficientTower
import Langlands.GroupScheme.IntegralModel.IntegerPresentation

/-! # Exact inertia-field recovery for the descended inner model -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped ValuativeRel CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.IntegralModel
open Descent Descent.FiniteUnramified GaloisPointComparison

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance finiteInnerRecoveryNormedField : NontriviallyNormedField F := localNormedField F
local instance finiteInnerRecoveryUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance finiteInnerRecoveryComplete : CompleteSpace F := localNormedField_complete F

variable (E : IntermediateField F (SeparableClosure F)) [hEinertia : Fact (E ≤ inertiaFixedField F)]

local instance finiteInnerRecoveryFieldAlgebra : Algebra E (inertiaFixedField F) :=
  (IntermediateField.inclusion (show E ≤ inertiaFixedField F from hEinertia.out)).toAlgebra
local instance finiteInnerRecoveryFieldTower : IsScalarTower F E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance finiteInnerRecoveryIntegerAlgebra :
    Algebra (extensionIntegers F E) (fixedFieldIntegers F) :=
  (spectralIntegerInclusion F E (show E ≤ inertiaFixedField F from hEinertia.out)).toAlgebra
local instance finiteInnerRecoveryIntegerFieldAlgebra :
    Algebra (extensionIntegers F E) (inertiaFixedField F) :=
  ((IntermediateField.inclusion (show E ≤ inertiaFixedField F from hEinertia.out)).toRingHom.comp
    (algebraMap (extensionIntegers F E) E)).toAlgebra
local instance finiteInnerRecoveryGenericTower :
    IsScalarTower (extensionIntegers F E) E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance finiteInnerRecoveryIntegralTower :
    IsScalarTower (extensionIntegers F E) (fixedFieldIntegers F) (inertiaFixedField F) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact spectralIntegerInclusion_inertia F E (show E ≤ inertiaFixedField F from hEinertia.out) x
local instance finiteInnerRecoveryCoefficientFlat :
    Flat (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E (show E ≤ inertiaFixedField F from hEinertia.out)).2.1
local instance finiteInnerRecoveryCoefficientSurjective :
    Surjective (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E (show E ≤ inertiaFixedField F from hEinertia.out)).1

local instance finiteInnerRecoveryIntegerFlat : Flat (integerMap F E) :=
  (integerMap_fpqc F E).2.1
local instance finiteInnerRecoveryIntegerSurjective : Surjective (integerMap F E) :=
  (integerMap_fpqc F E).1

variable [FiniteDimensional F E] [IsGalois F E]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (N : IntegralModel (extensionIntegers F E) E (baseChanged F E G))
  (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G))
  (e : (N.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).Iso P
    (finiteInertiaGenericIso F E G))
  (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
    rationalPoints (baseChanged F (inertiaFixedField F) G))
  (d : (E ≃ₐ[F] E) → rationalPoints (baseChanged F E G))
  (hrec : ∀ σ : E ≃ₐ[F] E,
    relativeRationalExtend F E (inertiaFixedField F) G (d σ) =
      c (liftAutomorphism F E (show E ≤ inertiaFixedField F from hEinertia.out) σ))
  (hP : P.IsSmooth)
  (hstable : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
    ∀ g ∈ P.integralPoints,
      c σ * rationalConjugate F (inertiaFixedField F) G σ g * (c σ)⁻¹ ∈ P.integralPoints)
  (hstable' : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
    ∀ g ∈ P.integralPoints,
      rationalConjugate F (inertiaFixedField F) G σ.symm
        ((c σ)⁻¹ * g * c σ) ∈ P.integralPoints)
  (hd : ∀ σ τ : E ≃ₐ[F] E,
    d (σ * τ) = d σ * rationalConjugate F E G σ (d τ))
  (hUnram : ArithmeticUnramified F E)


local instance recoveryInnerNormIntegerAlgebra : Algebra (baseIntegers F) (fixedFieldIntegers F) :=
  presentationNormIntegerAlgebra F
local instance recoveryInnerNormGenericAlgebra : Algebra (baseIntegers F) (inertiaFixedField F) :=
  presentationNormGenericAlgebra F
local instance recoveryInnerNormGenericTower : IsScalarTower (baseIntegers F) F (inertiaFixedField F) :=
  presentationNormGenericTower F
local instance recoveryInnerNormIntegralTower :
    IsScalarTower (baseIntegers F) (fixedFieldIntegers F) (inertiaFixedField F) :=
  presentationNormIntegralTower F
local instance recoveryInnerIntegerTower :
    IsScalarTower (baseIntegers F) (extensionIntegers F E) (fixedFieldIntegers F) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The actual comparison over the inertia fixed field is induced by the
finite inner generic comparison and the canonical generic tower maps. -/
def finiteInnerInertiaGenericComparison :
    baseChanged F (inertiaFixedField F)
        (finiteInnerGenericGroup F E G N P e c d hrec hP hstable hstable' hd hUnram) ≅
      baseChanged F (inertiaFixedField F) G :=
  (coefficientTowerGenericIso (K := F) (L := E) (P := inertiaFixedField F)
    (G := finiteInnerGenericGroup F E G N P e c d hrec hP hstable hstable' hd hUnram)).symm ≪≫
      ((GroupScheme.baseChange (Spec.algebraMap E (inertiaFixedField F))).mapIso
        (finiteInnerGenericComparison F E G N P e c d hrec hP hstable hstable' hd hUnram) ≪≫
          finiteInertiaGenericIso F E G)

set_option maxHeartbeats 800000 in
/-- The descended norm-integer model recovers the supplied inertia-field
model over exactly the induced inner generic comparison. -/
def normFiniteInnerInertiaModelIso :
    ((normFiniteInnerModel F E G N P e c d hrec hP hstable hstable' hd hUnram).baseChange
      (fixedFieldIntegers F) (inertiaFixedField F)).Iso P
        (finiteInnerInertiaGenericComparison F E G N P e c d hrec hP hstable hstable' hd hUnram) := by
  let M := normFiniteInnerModel F E G N P e c d hrec hP hstable hstable' hd hUnram
  let bc := (normFiniteInnerModelIso F E G N P e c d hrec hP hstable hstable' hd hUnram).baseChangeCoefficients
    (fixedFieldIntegers F) (inertiaFixedField F)
  let t := baseChangeTowerIso (A := extensionIntegers F E) (L := E)
    (B := fixedFieldIntegers F) (P := inertiaFixedField F) M
  exact t.symm.trans (bc.trans e)

/-- The actual smooth descended model over the given valuation integers. -/
def givenFiniteInnerModel :
    IntegralModel ↥𝒪[F] F
      (finiteInnerGenericGroup F E G N P e c d hrec hP hstable hstable' hd hUnram) :=
  givenIntegerModel F (normFiniteInnerModel F E G N P e c d hrec hP hstable hstable' hd hUnram)

theorem givenFiniteInnerModel_smooth :
    (givenFiniteInnerModel F E G N P e c d hrec hP hstable hstable' hd hUnram).IsSmooth :=
  givenIntegerModel_smooth F _
    (normFiniteInnerModel_smooth F E G N P e c d hrec hP hstable hstable' hd hUnram)

/-- Its actual unramified coefficient extension recovers the original
supplied model with the entire inner generic comparison retained. -/
def givenFiniteInnerModelIso :
    (givenFiniteInnerModel F E G N P e c d hrec hP hstable hstable' hd hUnram).baseChangeUnramified.Iso P
      (finiteInnerInertiaGenericComparison F E G N P e c d hrec hP hstable hstable' hd hUnram) :=
  givenIntegerModelIso F _
    (normFiniteInnerInertiaModelIso F E G N P e c d hrec hP hstable hstable' hd hUnram)

/-- The induced generic comparison carries the actual original integral-point
image onto the supplied model's actual integral-point image. -/
theorem givenFiniteInnerModel_map_integralPoints :
    (givenFiniteInnerModel F E G N P e c d hrec hP hstable hstable' hd hUnram).baseChangeUnramified.integralPoints.map
      (rationalPoints.map
        (finiteInnerInertiaGenericComparison F E G N P e c d hrec hP hstable hstable' hd hUnram).hom) =
      P.integralPoints :=
  (givenFiniteInnerModelIso F E G N P e c d hrec hP hstable hstable' hd hUnram).map_integralPoints

end Langlands.GroupScheme.IntegralModel

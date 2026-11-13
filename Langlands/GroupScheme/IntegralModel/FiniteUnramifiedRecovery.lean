import Langlands.GroupScheme.IntegralModel.FiniteUnramifiedSolution
import Langlands.GroupScheme.IntegralModel.CoefficientTower
import Langlands.GroupScheme.IntegralModel.IntegerPresentation

/-! # Exact maximal-unramified recovery from finite integral descent -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped ValuativeRel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.IntegralModel
open Descent Descent.FiniteUnramified GaloisPointComparison

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance finiteRecoveryNormedField : NontriviallyNormedField F := localNormedField F
local instance finiteRecoveryUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance finiteRecoveryComplete : CompleteSpace F := localNormedField_complete F

variable (E : IntermediateField F (SeparableClosure F)) [hEinertia : Fact (E ≤ inertiaFixedField F)]
local notation "hE" => hEinertia.out

local instance finiteRecoveryFieldAlgebra : Algebra E (inertiaFixedField F) :=
  (IntermediateField.inclusion hE).toAlgebra
local instance finiteRecoveryFieldTower : IsScalarTower F E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance finiteRecoveryIntegerAlgebra :
    Algebra (extensionIntegers F E) (fixedFieldIntegers F) :=
  (spectralIntegerInclusion F E hE).toAlgebra
local instance finiteRecoveryIntegerFieldAlgebra :
    Algebra (extensionIntegers F E) (inertiaFixedField F) :=
  ((IntermediateField.inclusion hE).toRingHom.comp
    (algebraMap (extensionIntegers F E) E)).toAlgebra
local instance finiteRecoveryGenericTower :
    IsScalarTower (extensionIntegers F E) E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance finiteRecoveryIntegralTower :
    IsScalarTower (extensionIntegers F E) (fixedFieldIntegers F) (inertiaFixedField F) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact spectralIntegerInclusion_inertia F E hE x
local instance finiteRecoveryCoefficientFlat :
    Flat (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E hE).2.1
local instance finiteRecoveryCoefficientSurjective :
    Surjective (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E hE).1


local instance finiteRecoveryIntegerFpqcFlat : Flat (integerMap F E) := (integerMap_fpqc F E).2.1
local instance finiteRecoveryIntegerFpqcSurjective : Surjective (integerMap F E) := (integerMap_fpqc F E).1

variable [FiniteDimensional F E] [IsGalois F E]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (N : IntegralModel (extensionIntegers F E) E (baseChanged F E G))
  (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G))
  (e : (N.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).Iso P
    (finiteInertiaGenericIso F E G))
  (hext : HasSmoothHomExtension (R := fixedFieldIntegers F) (L := inertiaFixedField F))
  (hP : P.IsSmooth)
  (hstable : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
    ∀ g ∈ P.integralPoints, rationalConjugate F (inertiaFixedField F) G σ g ∈ P.integralPoints)
  (hUnram : ArithmeticUnramified F E)


local instance recoveryNormIntegerAlgebra : Algebra (baseIntegers F) (fixedFieldIntegers F) :=
  presentationNormIntegerAlgebra F
local instance recoveryNormGenericAlgebra : Algebra (baseIntegers F) (inertiaFixedField F) :=
  presentationNormGenericAlgebra F
local instance recoveryNormGenericTower : IsScalarTower (baseIntegers F) F (inertiaFixedField F) :=
  presentationNormGenericTower F
local instance recoveryNormIntegralTower :
    IsScalarTower (baseIntegers F) (fixedFieldIntegers F) (inertiaFixedField F) :=
  presentationNormIntegralTower F
local instance recoveryIntegerTower :
    IsScalarTower (baseIntegers F) (extensionIntegers F E) (fixedFieldIntegers F) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The effective norm-integer model recovers the original model over the
maximal-unramified integers and the identity generic map. -/
def normFiniteDescendedModelIso (hN : N.IsSmooth) :
    ((finiteDescendedModel F E G N P e hext hP hstable hUnram hN).baseChange
      (fixedFieldIntegers F) (inertiaFixedField F)).Iso P (CategoryTheory.Iso.refl _) := by
  let M := finiteDescendedModel F E G N P e hext hP hstable hUnram hN
  let c := (finiteDescendedModelIso F E G N P e hext hP hstable hUnram hN).baseChangeCoefficients (fixedFieldIntegers F) (inertiaFixedField F)
  let t := baseChangeTowerIso (A := extensionIntegers F E) (L := E)
    (B := fixedFieldIntegers F) (P := inertiaFixedField F) M
  let u := t.symm.trans (c.trans e)
  refine u.changeGeneric (CategoryTheory.Iso.refl _) ?_
  change (coefficientTowerGenericIso (K := F) (L := E) (P := inertiaFixedField F) (G := G)).inv ≫
      (GroupScheme.baseChange (Spec.algebraMap E (inertiaFixedField F))).map (𝟙 (baseChanged F E G)) ≫
        (finiteInertiaGenericIso F E G).hom = 𝟙 (baseChanged F (inertiaFixedField F) G)
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact (finiteInertiaGenericIso F E G).inv_hom_id

/-- The resulting actual model uses the given valuation integers of F. -/
def givenFiniteDescendedModel (hN : N.IsSmooth) : IntegralModel ↥𝒪[F] F G :=
  givenIntegerModel F (finiteDescendedModel F E G N P e hext hP hstable hUnram hN)

theorem givenFiniteDescendedModel_smooth (hN : N.IsSmooth) :
    (givenFiniteDescendedModel F E G N P e hext hP hstable hUnram hN).IsSmooth :=
  givenIntegerModel_smooth F _
    (finiteDescendedModel_smooth F E G N P e hext hP hstable hUnram hN)

/-- Its actual unramified base change recovers the supplied original upstairs
model over the identity of the prescribed generic group. -/
def givenFiniteDescendedModelIso (hN : N.IsSmooth) :
    (givenFiniteDescendedModel F E G N P e hext hP hstable hUnram hN).baseChangeUnramified.Iso P
      (CategoryTheory.Iso.refl _) :=
  givenIntegerModelIso F _ (normFiniteDescendedModelIso F E G N P e hext hP hstable hUnram hN)

end Langlands.GroupScheme.IntegralModel

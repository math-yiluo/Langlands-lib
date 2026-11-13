import Langlands.GroupScheme.IntegralModel.FiniteUnramifiedRecovery
import Langlands.GroupScheme.IntegralModel.SmoothHomExtension
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof

/-! # The strictly Henselian extension input on maximal-unramified integers -/

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

/-- An actual compatible coefficient recovery of a smooth model reflects
smoothness to the original integral model through its fpqc coefficient map. -/
theorem isSmooth_of_coefficientIso
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {A L : Type u} [CommRing A] [IsDomain A] [Field L]
    [Algebra R A] [Algebra A L] [IsFractionRing A L]
    [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
    [Flat (Spec.algebraMap R A)] [Surjective (Spec.algebraMap R A)]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {H : GroupScheme (Spec (CommRingCat.of L))}
    (N : IntegralModel R K G) (P : IntegralModel A L H)
    {f : (GroupScheme.baseChange (Spec.algebraMap K L)).obj G ≅ H}
    (e : (N.baseChange A L).Iso P f) (hP : P.IsSmooth) : N.IsSmooth := by
  let : Smooth P.group.X.hom := hP
  have hs : Smooth (pullback.snd N.group.X.hom (Spec.algebraMap R A)) := by
    change Smooth (N.baseChange A L).group.X.hom
    rw [← Over.w e.iso.hom.hom.hom]
    infer_instance
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := N.group.X.hom) (g := Spec.algebraMap R A)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hs

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward false in
private theorem fixedField_residueSepClosed
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    IsSepClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) := by
  have h := fixedFieldResidueIsAlgClosure F
  let := (residueToFixedField F).toAlgebra
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) := h.isAlgClosed
  infer_instance

/-- The proved arithmetic of inertia integers discharges every ring
hypothesis of the strictly Henselian extension statement. The extension
statement itself remains an explicit premise. -/
theorem fixedField_hasSmoothHomExtension (hext : SmoothHomExtensionStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    HasSmoothHomExtension (R := fixedFieldIntegers F) (L := inertiaFixedField F) := by
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    (separableUnramifiedArithmetic F).2.2.2.1
  let : HenselianLocalRing (fixedFieldIntegers F) :=
    (separableUnramifiedArithmetic F).2.2.2.2
  let : IsSepClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) := fixedField_residueSepClosed F
  intro G H f N P hN hpoints
  exact hext (fixedFieldIntegers F) (inertiaFixedField F) G H f N P hN hpoints

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
local instance fixedExtensionNormedField : NontriviallyNormedField F := localNormedField F
local instance fixedExtensionUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance fixedExtensionComplete : CompleteSpace F := localNormedField_complete F
variable (E : IntermediateField F (SeparableClosure F)) [hEinertia : Fact (E ≤ inertiaFixedField F)]
local notation "hE" => hEinertia.out
local instance fixedExtensionFieldAlgebra : Algebra E (inertiaFixedField F) :=
  (IntermediateField.inclusion hE).toAlgebra
local instance fixedExtensionFieldTower : IsScalarTower F E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance fixedExtensionIntegerAlgebra : Algebra (extensionIntegers F E) (fixedFieldIntegers F) :=
  (spectralIntegerInclusion F E hE).toAlgebra
local instance fixedExtensionGenericAlgebra : Algebra (extensionIntegers F E) (inertiaFixedField F) :=
  ((IntermediateField.inclusion hE).toRingHom.comp (algebraMap (extensionIntegers F E) E)).toAlgebra
local instance fixedExtensionGenericTower : IsScalarTower (extensionIntegers F E) E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance fixedExtensionIntegralTower :
    IsScalarTower (extensionIntegers F E) (fixedFieldIntegers F) (inertiaFixedField F) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact spectralIntegerInclusion_inertia F E hE x
local instance fixedExtensionCoefficientFlat :
    Flat (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E hE).2.1
local instance fixedExtensionCoefficientSurjective :
    Surjective (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E hE).1

variable [FiniteDimensional F E] [IsGalois F E]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (N : IntegralModel (extensionIntegers F E) E (baseChanged F E G))
  (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G))
  (e : (N.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).Iso P
    (finiteInertiaGenericIso F E G))
  (hext : SmoothHomExtensionStatement.{u}) (hP : P.IsSmooth)
  (hstable : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
    ∀ g ∈ P.integralPoints, rationalConjugate F (inertiaFixedField F) G σ g ∈ P.integralPoints)
  (hUnram : ArithmeticUnramified F E)

/-- A supplied finite coefficient recovery and the general strictly Henselian
extension statement give the full descended model over the given integers. -/
def modelOfFiniteRecovery : IntegralModel ↥𝒪[F] F G :=
  givenFiniteDescendedModel F E G N P e (fixedField_hasSmoothHomExtension hext F)
    hP hstable hUnram (isSmooth_of_coefficientIso N P e hP)

theorem modelOfFiniteRecovery_smooth :
    (modelOfFiniteRecovery F E G N P e hext hP hstable hUnram).IsSmooth :=
  givenFiniteDescendedModel_smooth F E G N P e (fixedField_hasSmoothHomExtension hext F)
    hP hstable hUnram (isSmooth_of_coefficientIso N P e hP)

def modelOfFiniteRecoveryIso :
    (modelOfFiniteRecovery F E G N P e hext hP hstable hUnram).baseChangeUnramified.Iso P
      (CategoryTheory.Iso.refl _) :=
  givenFiniteDescendedModelIso F E G N P e (fixedField_hasSmoothHomExtension hext F)
    hP hstable hUnram (isSmooth_of_coefficientIso N P e hP)

end Langlands.GroupScheme.IntegralModel

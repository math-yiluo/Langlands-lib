import Langlands.GroupScheme.IntegralModel.FixedFieldExtension
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescent

/-! # Existential finite recovery and the final descent assembly -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped ValuativeRel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000

namespace Langlands.GroupScheme.IntegralModel
open Descent Descent.FiniteUnramified GaloisPointComparison

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance recoveryExistsNormedField : NontriviallyNormedField F := localNormedField F
local instance recoveryExistsUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance recoveryExistsComplete : CompleteSpace F := localNormedField_complete F

section AtField

variable (E : IntermediateField F (SeparableClosure F))
  [hEinertia : Fact (E ≤ inertiaFixedField F)]
local notation "hE" => hEinertia.out
local instance recoveryExistsFieldAlgebra : Algebra E (inertiaFixedField F) :=
  (IntermediateField.inclusion hE).toAlgebra
local instance recoveryExistsFieldTower : IsScalarTower F E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance recoveryExistsIntegerAlgebra :
    Algebra (extensionIntegers F E) (fixedFieldIntegers F) :=
  (spectralIntegerInclusion F E hE).toAlgebra
local instance recoveryExistsGenericAlgebra :
    Algebra (extensionIntegers F E) (inertiaFixedField F) :=
  ((IntermediateField.inclusion hE).toRingHom.comp
    (algebraMap (extensionIntegers F E) E)).toAlgebra
local instance recoveryExistsGenericTower :
    IsScalarTower (extensionIntegers F E) E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance recoveryExistsIntegralTower :
    IsScalarTower (extensionIntegers F E) (fixedFieldIntegers F) (inertiaFixedField F) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact spectralIntegerInclusion_inertia F E hE x

variable (G : GroupScheme (Spec (CommRingCat.of F)))
  (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G))

/-- Existence of a finite coefficient model with its prescribed exact recovery.
The field's finiteness, Galois and unramified properties are separate. -/
def HasFiniteRecoveryAt : Prop :=
  ∃ N : IntegralModel (extensionIntegers F E) E (baseChanged F E G),
    Nonempty ((N.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).Iso P
      (finiteInertiaGenericIso F E G))

/-- Consume an existential recovery only after abstracting its finite field. -/
theorem descent_of_finiteRecoveryAt [FiniteDimensional F E] [IsGalois F E]
    (hext : SmoothHomExtensionStatement.{u}) (hP : P.IsSmooth)
    (hstable : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      ∀ g ∈ P.integralPoints,
        rationalConjugate F (inertiaFixedField F) G σ g ∈ P.integralPoints)
    (hUnram : ArithmeticUnramified F E) (hrec : HasFiniteRecoveryAt F E G P) :
    ∃ M : IntegralModel ↥𝒪[F] F G, M.IsSmooth ∧
      Nonempty (M.baseChangeUnramified.Iso P (CategoryTheory.Iso.refl _)) := by
  obtain ⟨N, ⟨e⟩⟩ := hrec
  exact ⟨modelOfFiniteRecovery F E G N P e hext hP hstable hUnram,
    modelOfFiniteRecovery_smooth F E G N P e hext hP hstable hUnram,
    ⟨modelOfFiniteRecoveryIso F E G N P e hext hP hstable hUnram⟩⟩

end AtField

variable (G : GroupScheme (Spec (CommRingCat.of F)))
  (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G))

/-- Existential finite unramified recovery, with the actual inclusion maps
fixed in `HasFiniteRecoveryAt`. This definition asserts no existence theorem. -/
def HasFiniteUnramifiedRecovery : Prop :=
  ∃ (E : IntermediateField F (SeparableClosure F))
    (hE : Fact (E ≤ inertiaFixedField F)),
    FiniteDimensional F E ∧ IsGalois F E ∧ ArithmeticUnramified F E ∧
      @HasFiniteRecoveryAt F _ _ _ _ E hE G P

/-- The complete descent conclusion from the two still-supplied inputs. -/
theorem descent_of_finiteUnramifiedRecovery
    (hext : SmoothHomExtensionStatement.{u}) (hP : P.IsSmooth)
    (hstable : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      ∀ g ∈ P.integralPoints,
        rationalConjugate F (inertiaFixedField F) G σ g ∈ P.integralPoints)
    (hrec : HasFiniteUnramifiedRecovery F G P) :
    ∃ M : IntegralModel ↥𝒪[F] F G, M.IsSmooth ∧
      Nonempty (M.baseChangeUnramified.Iso P (CategoryTheory.Iso.refl _)) := by
  obtain ⟨E, hE, hfin, hgal, hUnram, hrec⟩ := hrec
  let : Fact (E ≤ inertiaFixedField F) := hE
  let : FiniteDimensional F E := hfin
  let : IsGalois F E := hgal
  exact descent_of_finiteRecoveryAt F E G P hext hP hstable hUnram hrec

/-- Internal finite-coefficient existence interface. No proof is supplied here. -/
def FiniteUnramifiedRecoveryStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G)),
    P.IsSmooth → HasFiniteUnramifiedRecovery F G P

/-- Conditional assembly, not a proof of the unconditional public statement. -/
theorem unramifiedSmoothModelDescent_of_extension_of_finiteRecovery
    (hext : SmoothHomExtensionStatement.{u})
    (hfinite : FiniteUnramifiedRecoveryStatement.{u}) :
    UnramifiedSmoothModelDescentStatement.{u} := by
  intro F _ _ _ _ G P hP hstable
  exact descent_of_finiteUnramifiedRecovery F G P hext hP hstable
    (hfinite F G P hP)

end Langlands.GroupScheme.IntegralModel

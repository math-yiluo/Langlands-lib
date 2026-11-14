import Langlands.GroupScheme.IntegralModel.FiniteUnramifiedIntegralDatum
import Langlands.GroupScheme.IntegralModel.InnerSemilinearCoefficientRecovery
import Langlands.GroupScheme.IntegralModel.FixedFieldExtension
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof

/-! # Finite integral descent data for inner-twisted coefficients -/

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

local instance finiteInnerDatumNormedField : NontriviallyNormedField F := localNormedField F
local instance finiteInnerDatumUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance finiteInnerDatumComplete : CompleteSpace F := localNormedField_complete F

variable (E : IntermediateField F (SeparableClosure F)) [hEinertia : Fact (E ≤ inertiaFixedField F)]

local instance finiteInnerDatumFieldAlgebra : Algebra E (inertiaFixedField F) :=
  (IntermediateField.inclusion (show E ≤ inertiaFixedField F from hEinertia.out)).toAlgebra
local instance finiteInnerDatumFieldTower : IsScalarTower F E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance finiteInnerDatumIntegerAlgebra :
    Algebra (extensionIntegers F E) (fixedFieldIntegers F) :=
  (spectralIntegerInclusion F E (show E ≤ inertiaFixedField F from hEinertia.out)).toAlgebra
local instance finiteInnerDatumIntegerFieldAlgebra :
    Algebra (extensionIntegers F E) (inertiaFixedField F) :=
  ((IntermediateField.inclusion (show E ≤ inertiaFixedField F from hEinertia.out)).toRingHom.comp
    (algebraMap (extensionIntegers F E) E)).toAlgebra
local instance finiteInnerDatumGenericTower :
    IsScalarTower (extensionIntegers F E) E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance finiteInnerDatumIntegralTower :
    IsScalarTower (extensionIntegers F E) (fixedFieldIntegers F) (inertiaFixedField F) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact spectralIntegerInclusion_inertia F E (show E ≤ inertiaFixedField F from hEinertia.out) x
local instance finiteInnerDatumCoefficientFlat :
    Flat (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E (show E ≤ inertiaFixedField F from hEinertia.out)).2.1
local instance finiteInnerDatumCoefficientSurjective :
    Surjective (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E (show E ≤ inertiaFixedField F from hEinertia.out)).1

variable (G : GroupScheme (Spec (CommRingCat.of F)))
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

/-- The proved strictly Henselian extension theorem constructs the upstairs
integral twist with exactly the recovered conjugator. -/
def finiteInnerUpstairsIso (σ : E ≃ₐ[F] E) :
    (P.twist (fixedIntegerBaseAut F (liftAutomorphism F E (show E ≤ inertiaFixedField F from hEinertia.out) σ))
      (galoisBaseMap F (inertiaFixedField F) (liftAutomorphism F E (show E ≤ inertiaFixedField F from hEinertia.out) σ))
      (fixedIntegerBaseAut_generic F (liftAutomorphism F E (show E ≤ inertiaFixedField F from hEinertia.out) σ))).Iso P
        (innerGaloisDescentIso F G (liftAutomorphism F E (show E ≤ inertiaFixedField F from hEinertia.out) σ)
          (relativeRationalExtend F E (inertiaFixedField F) G (d σ))) :=
  innerGaloisTwistIso F G P (liftAutomorphism F E (show E ≤ inertiaFixedField F from hEinertia.out) σ)
    (relativeRationalExtend F E (inertiaFixedField F) G (d σ))
    (fixedIntegerBaseAut F (liftAutomorphism F E (show E ≤ inertiaFixedField F from hEinertia.out) σ))
    (fixedIntegerBaseAut_generic F (liftAutomorphism F E (show E ≤ inertiaFixedField F from hEinertia.out) σ))
    (fixedField_hasSmoothHomExtension smoothHomExtension F) hP
    (by simpa only [hrec σ] using hstable (liftAutomorphism F E (show E ≤ inertiaFixedField F from hEinertia.out) σ))
    (by simpa only [hrec σ] using hstable' (liftAutomorphism F E (show E ≤ inertiaFixedField F from hEinertia.out) σ))

/-- Actual coefficient recovery descends the integral inner twist to the finite
model and preserves the specified finite generic map. -/
def finiteInnerIntegralSemilinearIso (σ : E ≃ₐ[F] E) :
    (N.twist (Spec.map (CommRingCat.ofHom (integerAut F E σ).toRingHom))
      (galoisBaseMap F E σ) (finiteIntegerBaseAut_generic F E σ)).Iso N
        (innerGaloisDescentIso F G σ (d σ)) :=
  innerSemilinearIsoFromCoefficients F E (inertiaFixedField F) G
    (finiteInertiaFieldTower F E) σ (liftAutomorphism F E (show E ≤ inertiaFixedField F from hEinertia.out) σ)
    (liftAutomorphism_fieldSquare F E (show E ≤ inertiaFixedField F from hEinertia.out) σ) (d σ)
    (extensionIntegers F E) (fixedFieldIntegers F) N P e
    (Spec.map (CommRingCat.ofHom (integerAut F E σ).toRingHom))
    (fixedIntegerBaseAut F (liftAutomorphism F E (show E ≤ inertiaFixedField F from hEinertia.out) σ))
    (finiteIntegerBaseAut_generic F E σ)
    (fixedIntegerBaseAut_generic F (liftAutomorphism F E (show E ≤ inertiaFixedField F from hEinertia.out) σ))
    (liftAutomorphism_integerSquare F E (show E ≤ inertiaFixedField F from hEinertia.out) σ)
    (finiteInnerUpstairsIso F E G P c d hrec hP hstable hstable' σ)

/-- The recovered finite integral map has the exact inner-twisted generic law. -/
theorem finiteInnerIntegralSemilinearIso_generic (σ : E ≃ₐ[F] E) :
    N.GenericSemilinearCompatible
      (Spec.map (CommRingCat.ofHom (integerAut F E σ).toRingHom))
      (galoisBaseMap F E σ) (finiteIntegerBaseAut_generic F E σ)
      (finiteInnerIntegralSemilinearIso F E G N P e c d hrec hP hstable hstable' σ).iso
      (innerGaloisDescentIso F G σ (d σ)) :=
  Hom.twist_generic_comm N _ _ _
    (finiteInnerIntegralSemilinearIso F E G N P e c d hrec hP hstable hstable' σ).toHom

variable [FiniteDimensional F E] [IsGalois F E]
  (hd : ∀ σ τ : E ≃ₐ[F] E, d (σ * τ) =
    d σ * rationalConjugate F E G σ (d τ))

/-- The recovered finite conjugators yield actual integral descent data on the
canonical finite unramified overlap cover. -/
def finiteInnerIntegralDatum (hUnram : ArithmeticUnramified F E) :
    Datum (integerMap F E) N.group :=
  datumOfGenericSemilinear N (integerMap F E) (integerComponent F E hUnram)
    (integerBaseAut F E) (fun i => galoisBaseMap F E (galoisIndexEquiv F E i))
    (integerComponent_fst F E hUnram) (integerComponent_snd F E hUnram)
    (integerIndexMul F E) (integerBaseAut_comp F E) (finiteFieldBaseAut_comp F E)
    (fun i => finiteIntegerBaseAut_generic F E (galoisIndexEquiv F E i))
    (fun i => (finiteInnerIntegralSemilinearIso F E G N P e c d hrec hP
      hstable hstable' (galoisIndexEquiv F E i)).iso)
    (fun i => innerGaloisDescentIso F G (galoisIndexEquiv F E i) (d (galoisIndexEquiv F E i)))
    (fun i => finiteInnerIntegralSemilinearIso_generic F E G N P e c d hrec hP
      hstable hstable' (galoisIndexEquiv F E i))
    (fun i j => innerGaloisDescentIso_tower F E G
      (galoisIndexEquiv F E i) (galoisIndexEquiv F E j)
      (galoisIndexEquiv F E (integerIndexMul F E i j))
      (finiteFieldBaseAut_comp F E i j)
      (d (galoisIndexEquiv F E i)) (d (galoisIndexEquiv F E j))
      (d (galoisIndexEquiv F E (integerIndexMul F E i j)))
      (by simpa only [galoisIndexEquiv_integerIndexMul] using
        hd (galoisIndexEquiv F E i) (galoisIndexEquiv F E j)))

/-- Each actual overlap component recovers the constructed finite integral twist. -/
theorem pullIso_finiteInnerIntegralDatum (hUnram : ArithmeticUnramified F E)
    (i : Fin (Module.finrank F E)) :
    pullIso (integerComponent F E hUnram i) (integerComponent_fst F E hUnram i)
        (integerComponent_snd F E hUnram i)
        (finiteInnerIntegralDatum F E G N P e c d hrec hP hstable hstable' hd hUnram).overlap =
      semilinearComponent N.group
        (finiteInnerIntegralSemilinearIso F E G N P e c d hrec hP hstable hstable'
          (galoisIndexEquiv F E i)).iso :=
  pullIso_datumOfGenericSemilinear N (integerMap F E) (integerComponent F E hUnram)
    (integerBaseAut F E) (fun j => galoisBaseMap F E (galoisIndexEquiv F E j))
    (integerComponent_fst F E hUnram) (integerComponent_snd F E hUnram)
    (integerIndexMul F E) (integerBaseAut_comp F E) (finiteFieldBaseAut_comp F E)
    (fun j => finiteIntegerBaseAut_generic F E (galoisIndexEquiv F E j)) _ _ _ _ i

end Langlands.GroupScheme.IntegralModel

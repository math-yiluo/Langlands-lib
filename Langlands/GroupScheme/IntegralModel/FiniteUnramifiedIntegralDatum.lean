import Langlands.GroupScheme.Descent.FiniteUnramifiedAutomorphismLift
import Langlands.GroupScheme.IntegralModel.SemilinearCoefficientDescent
import Langlands.GroupScheme.IntegralModel.SemilinearCoherence

/-! # Integral descent data on a supplied finite unramified model -/

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

local instance finiteDatumNormedField : NontriviallyNormedField F := localNormedField F
local instance finiteDatumUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance finiteDatumComplete : CompleteSpace F := localNormedField_complete F

variable (E : IntermediateField F (SeparableClosure F)) [hEinertia : Fact (E ≤ inertiaFixedField F)]
local notation "hE" => hEinertia.out

local instance finiteDatumFieldAlgebra : Algebra E (inertiaFixedField F) :=
  (IntermediateField.inclusion hE).toAlgebra
local instance finiteDatumFieldTower : IsScalarTower F E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance finiteDatumIntegerAlgebra :
    Algebra (extensionIntegers F E) (fixedFieldIntegers F) :=
  (spectralIntegerInclusion F E hE).toAlgebra
local instance finiteDatumIntegerFieldAlgebra :
    Algebra (extensionIntegers F E) (inertiaFixedField F) :=
  ((IntermediateField.inclusion hE).toRingHom.comp
    (algebraMap (extensionIntegers F E) E)).toAlgebra
local instance finiteDatumGenericTower :
    IsScalarTower (extensionIntegers F E) E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance finiteDatumIntegralTower :
    IsScalarTower (extensionIntegers F E) (fixedFieldIntegers F) (inertiaFixedField F) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact spectralIntegerInclusion_inertia F E hE x
local instance finiteDatumCoefficientFlat :
    Flat (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E hE).2.1
local instance finiteDatumCoefficientSurjective :
    Surjective (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E hE).1

/-- The actual field inclusion tower commutes. -/
theorem finiteInertiaFieldTower :
    Spec.algebraMap E (inertiaFixedField F) ≫ baseMap F E = baseMap F (inertiaFixedField F) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1

variable (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The canonical generic comparison of the finite model's coefficient
extension with the original inertia-base group. -/
def finiteInertiaGenericIso :
    (GroupScheme.baseChange (Spec.algebraMap E (inertiaFixedField F))).obj (baseChanged F E G) ≅
      baseChanged F (inertiaFixedField F) G :=
  pullbackComparison (baseMap F E) (Spec.algebraMap E (inertiaFixedField F))
    (baseMap F (inertiaFixedField F)) (finiteInertiaFieldTower F E) G

/-- Canonical generic semilinearity of this exact comparison for any chosen lift. -/
theorem finiteInertiaGenericIso_semilinear (σ : E ≃ₐ[F] E) :
    (GroupScheme.baseChange (galoisBaseMap F (inertiaFixedField F)
        (liftAutomorphism F E hE σ))).map (finiteInertiaGenericIso F E G).hom ≫
          (galoisDescentIso F (inertiaFixedField F) G (liftAutomorphism F E hE σ)).hom =
      (squareComparison (Spec.algebraMap E (inertiaFixedField F))
        (galoisBaseMap F (inertiaFixedField F) (liftAutomorphism F E hE σ))
        (galoisBaseMap F E σ) (Spec.algebraMap E (inertiaFixedField F))
        (liftAutomorphism_fieldSquare F E hE σ) (baseChanged F E G)).hom ≫
          (GroupScheme.baseChange (Spec.algebraMap E (inertiaFixedField F))).map
            (galoisDescentIso F E G σ).hom ≫ (finiteInertiaGenericIso F E G).hom := by
  rw [galoisDescentIso_hom_eq, galoisDescentIso_hom_eq]
  exact pullbackComparison_semilinear (baseMap F E) (Spec.algebraMap E (inertiaFixedField F))
    (baseMap F (inertiaFixedField F)) (finiteInertiaFieldTower F E)
    (galoisBaseMap F E σ) (galoisBaseMap_over F E σ)
    (galoisBaseMap F (inertiaFixedField F) (liftAutomorphism F E hE σ))
    (galoisBaseMap_over F (inertiaFixedField F) (liftAutomorphism F E hE σ))
    (liftAutomorphism_fieldSquare F E hE σ) G

variable
  (N : IntegralModel (extensionIntegers F E) E (baseChanged F E G))
  (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G))
  (e : (N.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).Iso P
    (finiteInertiaGenericIso F E G))
  (hext : HasSmoothHomExtension (R := fixedFieldIntegers F) (L := inertiaFixedField F))
  (hP : P.IsSmooth)
  (hstable : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
    ∀ g ∈ P.integralPoints, rationalConjugate F (inertiaFixedField F) G σ g ∈ P.integralPoints)

/-- The original upstairs point stability supplies an actual compatible
semilinear isomorphism of the finite coefficient model. -/
def finiteIntegralSemilinearIso (σ : E ≃ₐ[F] E) :
    (N.twist (Spec.map (CommRingCat.ofHom (integerAut F E σ).toRingHom))
      (galoisBaseMap F E σ) (finiteIntegerBaseAut_generic F E σ)).Iso N
        (galoisDescentIso F E G σ) :=
  semilinearIsoFromCoefficients N (fixedFieldIntegers F) (inertiaFixedField F)
    (Spec.map (CommRingCat.ofHom (integerAut F E σ).toRingHom))
    (galoisBaseMap F E σ) (finiteIntegerBaseAut_generic F E σ)
    (fixedIntegerBaseAut F (liftAutomorphism F E hE σ))
    (galoisBaseMap F (inertiaFixedField F) (liftAutomorphism F E hE σ))
    (fixedIntegerBaseAut_generic F (liftAutomorphism F E hE σ))
    (liftAutomorphism_integerSquare F E hE σ) (liftAutomorphism_fieldSquare F E hE σ)
    P (finiteInertiaGenericIso F E G) e (galoisDescentIso F E G σ)
    (galoisDescentIso F (inertiaFixedField F) G (liftAutomorphism F E hE σ))
    (galoisTwistIso F G P (liftAutomorphism F E hE σ)
      (fixedIntegerBaseAut F (liftAutomorphism F E hE σ))
      (fixedIntegerBaseAut_generic F (liftAutomorphism F E hE σ)) hext hP
      (hstable _) (hstable _))
    (finiteInertiaGenericIso_semilinear F E G σ)

/-- Its exact generic law is the finite canonical semilinear law. -/
theorem finiteIntegralSemilinearIso_generic (σ : E ≃ₐ[F] E) :
    N.GenericSemilinearCompatible
      (Spec.map (CommRingCat.ofHom (integerAut F E σ).toRingHom))
      (galoisBaseMap F E σ) (finiteIntegerBaseAut_generic F E σ)
      (finiteIntegralSemilinearIso F E G N P e hext hP hstable σ).iso
      (galoisDescentIso F E G σ) :=
  Hom.twist_generic_comm N _ _ _
    (finiteIntegralSemilinearIso F E G N P e hext hP hstable σ).toHom

variable [FiniteDimensional F E] [IsGalois F E]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] hEinertia in
/-- The actual field base maps obey the same finite index multiplication as
the integer base maps. -/
theorem finiteFieldBaseAut_comp (i j : Fin (Module.finrank F E)) :
    galoisBaseMap F E (galoisIndexEquiv F E i) ≫
        galoisBaseMap F E (galoisIndexEquiv F E j) =
      galoisBaseMap F E (galoisIndexEquiv F E (integerIndexMul F E i j)) := by
  rw [galoisIndexEquiv_integerIndexMul]
  exact (galoisBaseMap_mul F E _ _).symm

/-- Actual finite unramified Čech data obtained from the original upstairs
stable-point hypothesis and its compatible finite model recovery. -/
def finiteIntegralDatum (hUnram : ArithmeticUnramified F E) : Datum (integerMap F E) N.group :=
  datumOfGenericSemilinear N (integerMap F E) (integerComponent F E hUnram)
    (integerBaseAut F E) (fun i => galoisBaseMap F E (galoisIndexEquiv F E i))
    (integerComponent_fst F E hUnram) (integerComponent_snd F E hUnram)
    (integerIndexMul F E) (integerBaseAut_comp F E) (finiteFieldBaseAut_comp F E)
    (fun i => finiteIntegerBaseAut_generic F E (galoisIndexEquiv F E i))
    (fun i => (finiteIntegralSemilinearIso F E G N P e hext hP hstable
      (galoisIndexEquiv F E i)).iso)
    (fun i => galoisDescentIso F E G (galoisIndexEquiv F E i))
    (fun i => finiteIntegralSemilinearIso_generic F E G N P e hext hP hstable
      (galoisIndexEquiv F E i))
    (fun i j => galoisDescentIso_tower F G (galoisIndexEquiv F E i) (galoisIndexEquiv F E j)
      (galoisIndexEquiv F E (integerIndexMul F E i j)) (finiteFieldBaseAut_comp F E i j))

/-- The finite datum has precisely the constructed semilinear components. -/
theorem pullIso_finiteIntegralDatum (hUnram : ArithmeticUnramified F E)
    (i : Fin (Module.finrank F E)) :
    pullIso (integerComponent F E hUnram i) (integerComponent_fst F E hUnram i)
        (integerComponent_snd F E hUnram i)
        (finiteIntegralDatum F E G N P e hext hP hstable hUnram).overlap =
      semilinearComponent N.group
        (finiteIntegralSemilinearIso F E G N P e hext hP hstable (galoisIndexEquiv F E i)).iso :=
  pullIso_datumOfGenericSemilinear N (integerMap F E) (integerComponent F E hUnram)
    (integerBaseAut F E) (fun j => galoisBaseMap F E (galoisIndexEquiv F E j))
    (integerComponent_fst F E hUnram) (integerComponent_snd F E hUnram)
    (integerIndexMul F E) (integerBaseAut_comp F E) (finiteFieldBaseAut_comp F E)
    (fun j => finiteIntegerBaseAut_generic F E (galoisIndexEquiv F E j)) _ _ _ _ i

end Langlands.GroupScheme.IntegralModel

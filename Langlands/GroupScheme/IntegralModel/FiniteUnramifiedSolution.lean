import Langlands.GroupScheme.IntegralModel.FiniteUnramifiedIntegralDatum
import Langlands.GroupScheme.IntegralModel.SemilinearGenericSolution

/-! # Effective finite unramified descent with generic recovery -/

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

local instance finiteSolutionNormedField : NontriviallyNormedField F := localNormedField F
local instance finiteSolutionUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance finiteSolutionComplete : CompleteSpace F := localNormedField_complete F

variable (E : IntermediateField F (SeparableClosure F)) [hEinertia : Fact (E ≤ inertiaFixedField F)]
local notation "hE" => hEinertia.out

local instance finiteSolutionFieldAlgebra : Algebra E (inertiaFixedField F) :=
  (IntermediateField.inclusion hE).toAlgebra
local instance finiteSolutionFieldTower : IsScalarTower F E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance finiteSolutionIntegerAlgebra :
    Algebra (extensionIntegers F E) (fixedFieldIntegers F) :=
  (spectralIntegerInclusion F E hE).toAlgebra
local instance finiteSolutionIntegerFieldAlgebra :
    Algebra (extensionIntegers F E) (inertiaFixedField F) :=
  ((IntermediateField.inclusion hE).toRingHom.comp
    (algebraMap (extensionIntegers F E) E)).toAlgebra
local instance finiteSolutionGenericTower :
    IsScalarTower (extensionIntegers F E) E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance finiteSolutionIntegralTower :
    IsScalarTower (extensionIntegers F E) (fixedFieldIntegers F) (inertiaFixedField F) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact spectralIntegerInclusion_inertia F E hE x
local instance finiteSolutionCoefficientFlat :
    Flat (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E hE).2.1
local instance finiteSolutionCoefficientSurjective :
    Surjective (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E hE).1


local instance finiteSolutionIntegerFpqcFlat : Flat (integerMap F E) := (integerMap_fpqc F E).2.1
local instance finiteSolutionIntegerFpqcSurjective : Surjective (integerMap F E) := (integerMap_fpqc F E).1

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

/-- The actual affine fpqc solution of the constructed finite integer datum. -/
def finiteIntegralSolution : Solution (finiteIntegralDatum F E G N P e hext hP hstable hUnram) := by
  let : IsAffine N.group.X.left := isAffine_of_isAffineHom N.group.X.hom
  exact (finiteIntegralDatum F E G N P e hext hP hstable hUnram).affineSolution

instance finiteIntegralSolution_isAffine :
    IsAffine (finiteIntegralSolution F E G N P e hext hP hstable hUnram).obj.X.left := by
  let : IsAffine N.group.X.left := isAffine_of_isAffineHom N.group.X.hom
  exact Datum.affineSolution_isAffine _

omit hEinertia [FiniteDimensional F E] [IsGalois F E] in
/-- The finite integer automorphism is over the original integer base. -/
theorem finiteIntegerBaseAut_over (σ : E ≃ₐ[F] E) :
    Spec.map (CommRingCat.ofHom (integerAut F E σ).toRingHom) ≫ integerMap F E = integerMap F E := by
  change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro x
  exact (integerAut F E σ).commutes x

/-- The finite solution comparison respects every canonical generic Galois map. -/
theorem finiteIntegralSolution_genericCompatible (hN : N.IsSmooth) :
    SolutionGenericGaloisCompatible (finiteIntegralSolution F E G N P e hext hP hstable hUnram) hN := by
  intro σ
  let i := (galoisIndexEquiv F E).symm σ
  have hi : galoisIndexEquiv F E i = σ := (galoisIndexEquiv F E).apply_symm_apply σ
  have hcomponent := pullIso_finiteIntegralDatum F E G N P e hext hP hstable hUnram i
  have hgeneric := finiteIntegralSemilinearIso_generic F E G N P e hext hP hstable
    (galoisIndexEquiv F E i)
  dsimp only [GenericSemilinearCompatible] at hgeneric
  have hs :=
    solutionGenericComparison_semilinear_of_component
      (finiteIntegralSolution F E G N P e hext hP hstable hUnram) hN
      (integerBaseAut F E i) (finiteIntegerBaseAut_over F E (galoisIndexEquiv F E i))
      (galoisBaseMap F E (galoisIndexEquiv F E i))
      (galoisBaseMap_over F E (galoisIndexEquiv F E i))
      (finiteIntegerBaseAut_generic F E (galoisIndexEquiv F E i))
      (finiteIntegralSemilinearIso F E G N P e hext hP hstable (galoisIndexEquiv F E i)).iso
      (integerComponent F E hUnram i) (integerComponent_fst F E hUnram i)
      (integerComponent_snd F E hUnram i) hcomponent
      (by
        rw [galoisDescentIso_hom_eq] at hgeneric
        exact hgeneric)
  rw [hi] at hs
  exact hs

/-- The effective finite datum yields a smooth model over the norm integer
presentation of the original field, with its original generic group. -/
def finiteDescendedModel (hN : N.IsSmooth) : IntegralModel (baseIntegers F) F G :=
  ofGaloisCompatibleSolution (finiteIntegralSolution F E G N P e hext hP hstable hUnram)
    hN (finiteIntegralSolution_genericCompatible F E G N P e hext hP hstable hUnram hN)

theorem finiteDescendedModel_smooth (hN : N.IsSmooth) :
    (finiteDescendedModel F E G N P e hext hP hstable hUnram hN).IsSmooth :=
  isSmooth_ofGaloisCompatibleSolution (finiteIntegralSolution F E G N P e hext hP hstable hUnram)
    hN (finiteIntegralSolution_genericCompatible F E G N P e hext hP hstable hUnram hN)

/-- The finite coefficient extension recovers the supplied finite model over
the identity of its given generic group. -/
def finiteDescendedModelIso (hN : N.IsSmooth) :
    ((finiteDescendedModel F E G N P e hext hP hstable hUnram hN).baseChange
      (extensionIntegers F E) E).Iso N (CategoryTheory.Iso.refl _) :=
  isoOfGaloisCompatibleSolution (finiteIntegralSolution F E G N P e hext hP hstable hUnram)
    hN (finiteIntegralSolution_genericCompatible F E G N P e hext hP hstable hUnram hN)

end Langlands.GroupScheme.IntegralModel

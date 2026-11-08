import Langlands.Representation.Families.ActualLeviUnramifiedParameters
import Langlands.Representation.Jacquet.CoefficientScalarRestriction
import Langlands.Representation.Compact.CoefficientSpecialization
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.Plancherel.UnramifiedNormalizedInducedSpecialization
import Langlands.Representation.Plancherel.UnramifiedRationalNormalizedInducedFinitenessProof
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility

/-! # The actual unramified normalized induced family for a rational Levi -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal TensorProduct

namespace Langlands.Renard.AlgebraicFamily.ActualLevi

section Restriction

universe uB uH uX uW

variable {B : Type uB} [CommRing B] [Algebra ℂ B]
  {H : Type uH} [Group H]
  {X : Type uX} [AddCommGroup X] [Module B X] [Module ℂ X] [IsScalarTower ℂ B X]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (τ : Representation B H X) (π : Representation ℂ H W)
  (e : B →+* ℂ) (he : ∀ c : ℂ, e (algebraMap ℂ B c) = c)
  (T : X →ₛₗ[e] W) (hT : ∀ (g : H) (x : X), T (τ g x) = π g (T x))

/-- A semilinear evaluation intertwiner, viewed as a complex intertwiner out of the
complex restriction of the coefficient representation. -/
def restrictedIntertwining :
    (Jacquet.CoefficientRestriction.complexRepresentation τ).IntertwiningMap π where
  toFun := T
  map_add' := T.map_add
  map_smul' c x := by
    change T (c • x) = c • T x
    rw [← algebraMap_smul B c x, T.map_smulₛₗ, he]
  isIntertwining' g := LinearMap.ext fun x => hT g x

@[simp] theorem restrictedIntertwining_apply (x : X) :
    restrictedIntertwining τ π e he T hT x = T x := rfl

/-- The restricted intertwiner keeps the evaluation scalar law. -/
theorem restrictedIntertwining_smul (b : B) (x : X) :
    letI : Algebra B ℂ := e.toAlgebra
    restrictedIntertwining τ π e he T hT (b • x) =
      algebraMap B ℂ b • restrictedIntertwining τ π e he T hT x :=
  T.map_smulₛₗ b x

/-- Its coefficient scalar extension is the scalar extension of the semilinear map. -/
theorem restrictedIntertwining_bijective
    (hbij : letI : Algebra B ℂ := e.toAlgebra
      Function.Bijective (Plancherel.scalarExtensionOfSemilinear T)) :
    letI : Algebra B ℂ := e.toAlgebra
    Function.Bijective
      (Compact.CoefficientSpecialization.scalarExtension B
        (Jacquet.CoefficientRestriction.complexRepresentation τ) π
        (restrictedIntertwining τ π e he T hT)
        (restrictedIntertwining_smul τ π e he T hT)) :=
  hbij

end Restriction

open GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic
open Langlands.Plancherel

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]

local instance familyAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

local instance familyActualLeviPointTopology : TopologicalSpace (rationalPoints M) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))

/-- Regular coefficients on the full transported unramified parameter group. -/
abbrev coefficientAlgebra :=
  unramifiedRegularFunctions (normFamily p l hp hl)

/-- The original representation on the literal Levi image. -/
abbrev imageRepresentation (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) :=
  SmoothRep.pullback (leviPointsEquiv p l hp hl).symm ρ

local instance tensorGroup (V : Type*) [AddCommGroup V] [Module ℂ V] :
    AddCommGroup (coefficientAlgebra p l hp hl ⊗[ℂ] V) :=
  TensorProduct.addCommGroup

/-- The full native coefficient-valued induced carrier. -/
abbrev UniversalCarrier (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) :=
  UnramifiedNormalized.UniversalInduced (normFamily p l hp hl)
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (imageRepresentation p l hp hl ρ).representation

instance universalCarrierModule (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    Module (coefficientAlgebra p l hp hl) (UniversalCarrier p l r hp hl hr hmul ρ) :=
  Submodule.module _

instance universalCarrierComplexModule (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    Module ℂ (UniversalCarrier p l r hp hl hr hmul ρ) :=
  Module.restrictScalars ℂ (coefficientAlgebra p l hp hl) _

instance universalCarrierSMul (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    SMul (coefficientAlgebra p l hp hl) (UniversalCarrier p l r hp hl hr hmul ρ) :=
  (universalCarrierModule p l r hp hl hr hmul ρ).toSMul

instance universalCarrierScalarTower (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    IsScalarTower ℂ (coefficientAlgebra p l hp hl)
      (UniversalCarrier p l r hp hl hr hmul ρ) :=
  IsScalarTower.restrictScalars ℂ (coefficientAlgebra p l hp hl) _

/-- The universal normalized induced family as an actual complex smooth representation. -/
def universalFamily (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    SmoothRep.{0, u, max u v} ℂ (rationalPoints G) :=
  SmoothRep.of
    (Jacquet.CoefficientRestriction.complexRepresentation
      (UnramifiedNormalized.universalInducedRepresentation (normFamily p l hp hl)
        (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
        (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
        (imageRepresentation p l hp hl ρ).representation))
    (UnramifiedNormalized.isSmooth_universalInducedRepresentation _ _ _ _)

instance universalFamilyModule (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    Module (coefficientAlgebra p l hp hl) (universalFamily p l r hp hl hr hmul ρ) :=
  universalCarrierModule p l r hp hl hr hmul ρ

instance universalFamilySMul (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    SMul (coefficientAlgebra p l hp hl) (universalFamily p l r hp hl hr hmul ρ) :=
  (universalFamilyModule p l r hp hl hr hmul ρ).toSMul

instance universalFamilyScalarTower (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    IsScalarTower ℂ (coefficientAlgebra p l hp hl) (universalFamily p l r hp hl hr hmul ρ) :=
  universalCarrierScalarTower p l r hp hl hr hmul ρ

instance universalFamily_hasCompatibleCoefficients
    (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    HasCompatibleCoefficients (coefficientAlgebra p l hp hl)
      (universalFamily p l r hp hl hr hmul ρ).representation where
  map_smul b g x :=
    (UnramifiedNormalized.universalInducedRepresentation (normFamily p l hp hl)
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      (imageRepresentation p l hp hl ρ).representation g).map_smul b x

/-- The exact fiber appearing in the induced-irreducibility statement. -/
abbrev fiber (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (ψ : unramifiedCharacters (fun χ : rationalCharacters M =>
      (rationalNormCharacters M χ).toMul)) :
    SmoothRep.{0, u, max u v} ℂ (rationalPoints G) := by
  letI := leviPoints_nonarchimedeanGroup p l hp hl
  exact (leviInductionFunctor p l r hp hr hl hmul).obj
    (ρ.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ))

/-- Compact fixed modules in the actual universal family are finite free
when the inducing representation is admissible and the parabolic quotient is compact. -/
theorem universalFamily_fixed_finite_free
    (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) (hρ : ρ.IsAdmissible)
    [CompactSpace (Induction.LeftQuotient (pointImage p))]
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G))) :
    Module.Finite (coefficientAlgebra p l hp hl)
      (fixedVectors (universalFamily p l r hp hl hr hmul ρ).representation K.toSubgroup) ∧
    Module.Free (coefficientAlgebra p l hp hl)
      (fixedVectors (universalFamily p l r hp hl hr hmul ρ).representation K.toSubgroup) := by
  have hπ : (imageRepresentation p l hp hl ρ).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv ρ.representation (leviPointsEquiv p l hp hl).symm hρ
  have hff := RationalNormalized.universalInduced_fixed_finite_free (normFamily p l hp hl)
    (continuous_normFamily p l hp hl)
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (continuous_projection_pointImage p l r hp hl hr hmul)
    (imageRepresentation p l hp hl ρ) hπ
    (isClosed_pointImage p hp.isClosedSubgroup) K hK
  have := hff.1
  have := hff.2
  let e := Jacquet.CoefficientRestriction.complexFixedVectorsEquiv
    (UnramifiedNormalized.universalInducedRepresentation (normFamily p l hp hl)
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      (imageRepresentation p l hp hl ρ).representation) K.toSubgroup
  exact ⟨Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm⟩

/-- Evaluation of the universal family at a parameter, with target the literal fiber. -/
def specializationEvaluation (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (ψ : unramifiedCharacters (fun χ : rationalCharacters M =>
      (rationalNormCharacters M χ).toMul)) :
    (universalFamily p l r hp hl hr hmul ρ).representation.IntertwiningMap
      (fiber p l r hp hl hr hmul ρ ψ).representation :=
  restrictedIntertwining _ _
    (UnramifiedNormalized.evaluation (normFamily p l hp hl) (parameterEquiv p l hp hl ψ))
    (UnramifiedNormalized.evaluation_algebraMap _ _)
    (UnramifiedNormalized.inducedEvaluation (normFamily p l hp hl)
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      (imageRepresentation p l hp hl ρ).representation (parameterEquiv p l hp hl ψ))
    (UnramifiedNormalized.inducedEvaluation_action _ _ _ _ _)

theorem specializationEvaluation_apply (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (ψ : unramifiedCharacters (fun χ : rationalCharacters M =>
      (rationalNormCharacters M χ).toMul))
    (x : universalFamily p l r hp hl hr hmul ρ) :
    specializationEvaluation p l r hp hl hr hmul ρ ψ x =
      UnramifiedNormalized.inducedEvaluation (normFamily p l hp hl)
        (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
        (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
        (imageRepresentation p l hp hl ρ).representation (parameterEquiv p l hp hl ψ) x :=
  rfl

/-- Evaluation is semilinear along evaluation of regular coefficients at the
transported parameter. -/
theorem specializationEvaluation_smul (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (ψ : unramifiedCharacters (fun χ : rationalCharacters M =>
      (rationalNormCharacters M χ).toMul))
    (b : coefficientAlgebra p l hp hl) (x : universalFamily p l r hp hl hr hmul ρ) :
    letI : Algebra (coefficientAlgebra p l hp hl) ℂ :=
      (UnramifiedNormalized.evaluation (normFamily p l hp hl)
        (parameterEquiv p l hp hl ψ)).toAlgebra
    specializationEvaluation p l r hp hl hr hmul ρ ψ (b • x) =
      algebraMap (coefficientAlgebra p l hp hl) ℂ b •
        specializationEvaluation p l r hp hl hr hmul ρ ψ x :=
  restrictedIntertwining_smul _ _ _ _ _ _ b x

/-- Full scalar specialization of the universal family at a parameter is the literal
fiber. No admissibility is needed for this comparison. -/
theorem universalFamily_specialization (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (ψ : unramifiedCharacters (fun χ : rationalCharacters M =>
      (rationalNormCharacters M χ).toMul))
    [CompactSpace (Induction.LeftQuotient (pointImage p))] :
    letI : Algebra (coefficientAlgebra p l hp hl) ℂ :=
      (UnramifiedNormalized.evaluation (normFamily p l hp hl)
        (parameterEquiv p l hp hl ψ)).toAlgebra
    ∃ (f : (universalFamily p l r hp hl hr hmul ρ).representation.IntertwiningMap
        (fiber p l r hp hl hr hmul ρ ψ).representation)
      (hf : ∀ (b : coefficientAlgebra p l hp hl) (x : universalFamily p l r hp hl hr hmul ρ),
        f (b • x) = algebraMap (coefficientAlgebra p l hp hl) ℂ b • f x),
      Function.Bijective
        (Compact.CoefficientSpecialization.scalarExtension (coefficientAlgebra p l hp hl)
          (universalFamily p l r hp hl hr hmul ρ).representation
          (fiber p l r hp hl hr hmul ρ ψ).representation f hf) :=
  ⟨specializationEvaluation p l r hp hl hr hmul ρ ψ,
    specializationEvaluation_smul p l r hp hl hr hmul ρ ψ,
    restrictedIntertwining_bijective _ _ _ _ _ _
      (UnramifiedNormalized.Specialization.inducedScalarExtension_bijective
        (normFamily p l hp hl)
        (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
        (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
        (imageRepresentation p l hp hl ρ).representation (parameterEquiv p l hp hl ψ)
        (isClosed_pointImage p hp.isClosedSubgroup) (continuous_normFamily p l hp hl)
        (continuous_projection_pointImage p l r hp hl hr hmul))⟩

end Langlands.Renard.AlgebraicFamily.ActualLevi

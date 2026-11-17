import Langlands.Representation.Category.Twist
import Langlands.Representation.Plancherel.DynamicOppositeConjugationScalar

/-! # Actual unramified twists under rational conjugation -/

noncomputable section

set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualConjugateLeviTwist

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining

section SchemeTransport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H J : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [IsAffine J.X.left]

local instance schemeTransportTopH : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology F H.X
local instance schemeTransportTopJ : TopologicalSpace (rationalPoints J) :=
  rationalPointTopology F J.X

private theorem characterTransport_map_apply (e : H ≅ J)
    (z : unramifiedCharacters (fun ψ => (rationalNormCharacters H ψ).toMul))
    (y : rationalPoints H) :
    (rationalUnramifiedCharacterTransport e z).val (rationalPoints.map e.hom y) = z.val y :=
  congrArg (fun c : unramifiedCharacters (fun ψ => (rationalNormCharacters H ψ).toMul) =>
    c.val y) (rationalUnramifiedCharacterRestrict_transport e z)

end SchemeTransport

section PullbackTwist

variable {M N : Type u} [Group M] [Group N] [TopologicalSpace M] [TopologicalSpace N]

private def pullbackTwistEquiv (e : N ≃ₜ* M) (A : SmoothRep.{0, u, uV} ℂ M)
    (α : M →* ℂˣ) (β : N →* ℂˣ)
    (hα : IsOpen (α.ker : Set M)) (hβ : IsOpen (β.ker : Set N))
    (h : ∀ m, β m = α (e m)) :
    (SmoothRep.pullback e (A.twist α hα)).representation.Equiv
      ((SmoothRep.pullback e A).twist β hβ).representation where
  toLinearEquiv := LinearEquiv.refl ℂ A
  isIntertwining' m := by
    ext v
    change (α (e m) : ℂ) • A.representation (e m) v =
      (β m : ℂ) • A.representation (e m) v
    rw [h]

end PullbackTwist

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2


variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (g : RationalPoint F G.X)

set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso g).hom)

/-- Transport in the full actual rational-character parameter algebra. -/
def conjugateParameter : unramifiedCharacters (normCharacters χ) →ₜ*
    unramifiedCharacters (normCharacters χg) :=
  rationalUnramifiedCharacterTransport (parameterConjugationIso χ g)

omit [LocallyOfFiniteType G.X.hom] in
private theorem parameterTransport_apply
    (z : unramifiedCharacters (normCharacters χ)) (m : levi χ) :
    (parameterTransport χ z).val m = z.val ((parameterHomeomorph χ).symm m) := rfl

/-- The scheme parameter transport gives exactly the inverse-conjugate
character on the literal target Levi. -/
theorem conjugateParameter_apply (z : unramifiedCharacters (normCharacters χ))
    (m : levi χg) :
    (parameterTransport χg (conjugateParameter χ g z)).val m =
      (parameterTransport χ z).val ((leviConjugation χ g).symm m) := by
  let y := (parameterHomeomorph χ).symm ((leviConjugation χ g).symm m)
  have hm : parameterHomeomorph χg
      (GroupScheme.rationalPoints.map (parameterConjugationIso χ g).hom y) = m :=
    (parameterHomeomorph_parameterConjugationIso χ g y).trans
      ((congrArg (leviConjugation χ g)
        ((parameterHomeomorph χ).apply_symm_apply _)).trans
          ((leviConjugation χ g).apply_symm_apply m))
  have hy : (parameterHomeomorph χg).symm m =
      GroupScheme.rationalPoints.map (parameterConjugationIso χ g).hom y :=
    (congrArg (parameterHomeomorph χg).symm hm.symm).trans
      ((parameterHomeomorph χg).symm_apply_apply _)
  have hc : (conjugateParameter χ g z).val
      (GroupScheme.rationalPoints.map (parameterConjugationIso χ g).hom y) = z.val y :=
    characterTransport_map_apply (parameterConjugationIso χ g) z y
  have hz : (parameterTransport χ z).val ((leviConjugation χ g).symm m) = z.val y :=
    parameterTransport_apply χ z ((leviConjugation χ g).symm m)
  exact (parameterTransport_apply χg (conjugateParameter χ g z) m).trans
    ((congrArg (conjugateParameter χ g z).val hy).trans (hc.trans hz.symm))

/-- Conjugation commutes with the actual full unramified twist, with the
identity on the original representation carrier. -/
def conjugateTwistEquiv (z : unramifiedCharacters (normCharacters χ))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) :
    (conjugateRepresentation χ g
      (A.twist (parameterTransport χ z).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χ)
          (parameterTransport χ z)))).representation.Equiv
      ((conjugateRepresentation χ g A).twist
        (parameterTransport χg (conjugateParameter χ g z)).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χg)
          (parameterTransport χg (conjugateParameter χ g z)))).representation :=
  pullbackTwistEquiv (leviConjugation χ g).symm A
    (parameterTransport χ z).val.toMonoidHom
    (parameterTransport χg (conjugateParameter χ g z)).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker _ _) (unramifiedCharacter_isOpen_ker _ _)
    (conjugateParameter_apply χ g z)

end Langlands.Plancherel.ActualConjugateLeviTwist

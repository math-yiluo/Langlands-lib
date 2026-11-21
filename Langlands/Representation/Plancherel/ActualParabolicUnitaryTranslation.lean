import Langlands.Representation.Plancherel.ActualParabolicTranslation
import Langlands.Representation.Plancherel.ActualConjugateLeviV3Statement

/-! # Unitary restriction of the actual parabolic coefficient translation -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualParabolicUnitaryTranslation

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition
open ActualCommonLeviTensor ActualConjugateLeviTwist ActualCommonLeviCoherence
open ActualConjugateLeviV3 ActualParabolicTranslation
open ActualCommonLeviV3 (unitaryParameter)

section Restriction

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H J : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [IsAffine J.X.left]

local instance sourceTopology : TopologicalSpace (rationalPoints H) := rationalPointTopology F H.X
local instance targetTopology : TopologicalSpace (rationalPoints J) := rationalPointTopology F J.X

private theorem restrict_unitary_inclusion (e : H ≅ J)
    (z : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters H ψ).toMul)) :
    (⟨(rationalUnitaryUnramifiedCharacterRestrict e.inv z).val,
       (rationalUnitaryUnramifiedCharacterRestrict e.inv z).property.1⟩ :
        unramifiedCharacters (fun ψ => (rationalNormCharacters J ψ).toMul)) =
      rationalUnramifiedCharacterTransport e ⟨z.val, z.property.1⟩ :=
  Subtype.ext (rationalUnitaryUnramifiedCharacterRestrict_coe e.inv z)

end Restriction

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (g : RationalPoint F G.X)

set_option hygiene false in
set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso g).hom)
set_option hygiene false in
local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)
set_option hygiene false in
local notation "zg" => unitaryConjugateParameter χ g

omit [LocallyOfFiniteType G.X.hom] in
/-- Unitary parameter conjugation is the restriction of full conjugation. -/
theorem unitaryParameter_conjugation (z : Xu) :
    unitaryParameter χg (zg z) = conjugateParameter χ g (unitaryParameter χ z) :=
  restrict_unitary_inclusion (parameterConjugationIso χ g) z

variable (A : SmoothRep.{0, u, uV} ℂ (levi χ))

set_option hygiene false in
local notation "Ag" => conjugateRepresentation χ g A

/-- The same-carrier conjugate-twist comparison at the transported unitary point. -/
def unitaryTwistEquiv (z : Xu) :
    (conjugateRepresentation χ g (twistObject χ (unitaryParameter χ z) A)).representation.Equiv
      (twistObject χg (unitaryParameter χg (zg z)) Ag).representation :=
  Eq.rec (motive := fun w _ =>
      (conjugateRepresentation χ g
        (twistObject χ (unitaryParameter χ z) A)).representation.Equiv
        (twistObject χg w Ag).representation)
    (conjugateTwistEquiv χ g (unitaryParameter χ z) A)
    (unitaryParameter_conjugation χ g z).symm

variable (K K' : OpenSubgroup (RationalPoint F G.X))
  (hKK' : RationalDynamicSource.conjugateCompact g K = K')
  (P : ParabolicPresentation χ K)
  (hG : IsConnectedReductive G)
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hK' : IsCompact (K' : Set (RationalPoint F G.X)))

set_option hygiene false in
local notation "Pg" => conjugatePresentation χ g K K' hKK' P

/-- Restrict the actual source-to-conjugate-source translation to the full
unitary subgroup, with the target expressed at its own unitary parameter. -/
def unitaryTranslation (z : Xu) :
    (fiber χ A K P z).representation.Equiv (fiber χg Ag K' Pg (zg z)).representation :=
  Eq.rec (motive := fun w _ =>
      (fiber χ A K P z).representation.Equiv
        (coefficientFiber χg (Pg).cocharacter (Pg).centralizer_eq Ag w).representation)
    (translatedCoefficient χ g K K' hKK' P hG A hK hK' (unitaryParameter χ z))
    (unitaryParameter_conjugation χ g z).symm

variable (Q : ParabolicPresentation χg K')

/-- Actual source and target coefficient fibers of a translated family. -/
abbrev UnitaryComparisonFamily :=
  ∀ z : Xu, (fiber χ A K P z).representation.IntertwiningMap
    (fiber χg Ag K' Q (zg z)).representation

/-- The translated unitary family obtained from the particular same-Levi
family on the target side and the specified actual translation. -/
def ofCommonLevi
    (T : ActualCommonLeviV3.UnitaryComparisonFamily χg Ag
      (Pg).cocharacter (Pg).centralizer_eq Q.cocharacter Q.centralizer_eq) :
    UnitaryComparisonFamily χ g A K K' P Q :=
  fun z => (T (zg z)).comp
    (unitaryTranslation χ g A K K' hKK' P hG hK hK' z).toIntertwiningMap

end Langlands.Plancherel.ActualParabolicUnitaryTranslation

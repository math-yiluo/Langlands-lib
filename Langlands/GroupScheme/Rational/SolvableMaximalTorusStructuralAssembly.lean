import Langlands.GroupScheme.Rational.SolvableMaximalTorusAssembly
import Langlands.GroupScheme.Rational.TorusGeneratedSplitGeometricRadicalQuotient
import Langlands.GroupScheme.Rational.SplitTorusDominatedSolvableQuotientReduction
import Langlands.GroupScheme.Rational.SplitUnipotentStableVectorProof

/-! # Rational maximal-torus conjugacy using the proved stable-vector theorem -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitGeometricRadicalTorusQuotient

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- A section of the stored torus quotient over the original field, using the
proved stable-vector and torus-action linearization theorems. -/
def sectionHom (D : SplitGeometricRadicalTorusQuotient G) :
    D.quotientData.quotient ⟶ G := by
  let hi := D.isGeometricUnipotentRadical.1
  let : Smooth D.radical.X.hom := hi.smooth
  let : ConnectedSpace D.radical.X.left := hi.connectedSpace
  let : IsClosedImmersion D.inclusion.hom.hom.left := hi.isClosedSubgroup
  let : Mono D.inclusion.hom.hom := Over.mono_of_mono_left _
  exact D.isTorus.splitUnipotentExtensionSection
    D.inclusion D.quotientData.projection D.quotientData.isFppfQuotient
    hi.isUnipotent D.isSplitUnipotent
    RelativeRoot.splitUnipotentStableVectorSubgroup
    RelativeRoot.torusVectorActionLinearization

/-- The section uses the projection and target already stored with the radical. -/
theorem sectionHom_comp (D : SplitGeometricRadicalTorusQuotient G) :
    D.sectionHom ≫ D.quotientData.projection = 𝟙 D.quotientData.quotient := by
  let hi := D.isGeometricUnipotentRadical.1
  let : Smooth D.radical.X.hom := hi.smooth
  let : ConnectedSpace D.radical.X.left := hi.connectedSpace
  let : IsClosedImmersion D.inclusion.hom.hom.left := hi.isClosedSubgroup
  let : Mono D.inclusion.hom.hom := Over.mono_of_mono_left _
  exact D.isTorus.splitUnipotentExtensionSection_comp
    D.inclusion D.quotientData.projection D.quotientData.isFppfQuotient
    hi.isUnipotent D.isSplitUnipotent
    RelativeRoot.splitUnipotentStableVectorSubgroup
    RelativeRoot.torusVectorActionLinearization

/-- The actual split radical and its retained torus quotient suffice for
rational maximal-torus conjugacy, with no further structural premise. -/
theorem maximalToriAreConjugate (D : SplitGeometricRadicalTorusQuotient G) :
    MaximalToriAreConjugate G := by
  let hi := D.isGeometricUnipotentRadical.1
  let : Smooth D.radical.X.hom := hi.smooth
  let : ConnectedSpace D.radical.X.left := hi.connectedSpace
  exact maximalToriAreConjugate_of_splitUnipotent_torus_section
    RelativeRoot.splitUnipotentStableVectorSubgroup
    RelativeRoot.torusVectorActionLinearization
    D.inclusion hi.isClosedSubgroup hi.isUnipotent D.isSplitUnipotent
    D.quotientData.projection D.quotientData.isFppfQuotient
    D.sectionHom D.sectionHom_comp D.isTorus

end SplitGeometricRadicalTorusQuotient

/-- Discharge the stable-vector premise of the earlier three-input assembly. -/
theorem solvableMaximalTorusConjugacy_of_splitGeometricRadical_and_torusQuotient
    (hrad : TorusGeneratedSplitGeometricRadicalStatement.{u})
    (hquot : SolvableTorusQuotientStatement.{u}) :
    SolvableMaximalTorusConjugacyStatement.{u} :=
  solvableMaximalTorusConjugacy_of_structuralStatements
    hrad hquot RelativeRoot.splitUnipotentStableVectorSubgroup

/-- Retaining the descended quotient removes the separate absolute quotient
premise; the initial dominated quotient and splitness criterion remain explicit. -/
theorem solvableMaximalTorusConjugacy_of_splitTorusDominatedQuotient
    (hquot : SplitTorusDominatedSolvableQuotientStatement.{u})
    (hsplit : UnipotentSplitTorusDominationStatement.{u}) :
    SolvableMaximalTorusConjugacyStatement.{u} := by
  intro k _ G _ _ _ hG
  let E := smoothTorusGeneratedEnvelope G
  let : Smooth E.group.X.hom := smoothTorusGeneratedEnvelope_smooth G
  let : ConnectedSpace E.group.X.left :=
    smoothTorusGeneratedEnvelope_connectedSpace G
  let : IsAffineHom E.group.X.hom := E.isAffineHom
  have hsolv : IsSolvableGroupScheme E.group := E.isSolvableGroupScheme hG
  let D := E.isTorusGenerated.splitGeometricRadicalTorusQuotientOfStructuralStatements
    hquot hsplit RelativeRoot.splitUnipotentStableVectorSubgroup hsolv
  exact E.maximalToriAreConjugate D.maximalToriAreConjugate

/-- The absolute quotient statement and domination splitness criterion suffice,
without a separate geometric-radical or stable-vector premise. -/
theorem solvableMaximalTorusConjugacy_of_torusQuotient_and_dominationSplitness
    (hquot : SolvableTorusQuotientStatement.{u})
    (hsplit : UnipotentSplitTorusDominationStatement.{u}) :
    SolvableMaximalTorusConjugacyStatement.{u} :=
  solvableMaximalTorusConjugacy_of_splitTorusDominatedQuotient
    (splitTorusDominatedSolvableQuotient_of_solvableTorusQuotient hquot) hsplit

end Langlands.GroupScheme

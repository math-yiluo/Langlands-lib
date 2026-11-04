import Langlands.GroupScheme.Rational.SmoothTorusGeneratedEnvelope
import Langlands.GroupScheme.Rational.TorusGeneratedSplitGeometricRadicalStatement
import Langlands.GroupScheme.Rational.GeometricRadicalTorusQuotient
import Langlands.GroupScheme.Rational.SplitUnipotentExtensionSection
import Langlands.GroupScheme.Rational.TorusQuotientMaximalConjugacy
import Langlands.GroupScheme.Rational.TorusVectorLinearizationProof
import Langlands.GroupScheme.Rational.SolvableMaximalTorusStatement

/-! # Assembly of rational maximal-torus conjugacy from structural prerequisites -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- An actual torus quotient by the specified geometric radical, together with
a homomorphic section over the original field. -/
structure SectionedGeometricRadicalTorusQuotient
    {k : Type u} [Field k]
    {U G : GroupScheme (Spec (CommRingCat.of k))} (i : U ⟶ G)
    extends GeometricRadicalTorusQuotient i where
  sectionHom : quotient ⟶ G
  sectionHom_comp : sectionHom ≫ projection = 𝟙 quotient

/-- Construct the actual quotient and its section from a supplied split
geometric radical, retaining the absolute quotient and stable-vector inputs. -/
def LeviSubgroup.IsGeometricUnipotentRadical.sectionedTorusQuotient
    (hquot : SolvableTorusQuotientStatement.{u})
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    {k : Type u} [Field k]
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : U ⟶ G} (hi : LeviSubgroup.IsGeometricUnipotentRadical i)
    (hsplit : RelativeRoot.IsSplitUnipotent U) (hG : IsSolvableGroupScheme G) :
    SectionedGeometricRadicalTorusQuotient i := by
  let : Smooth U.X.hom := hi.1.smooth
  let : ConnectedSpace U.X.left := hi.1.connectedSpace
  let : IsClosedImmersion i.hom.hom.left := hi.1.isClosedSubgroup
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let D := hi.torusQuotient hquot hG
  have hQ : IsTorus D.quotient := D.isTorus
  let s := hQ.splitUnipotentExtensionSection i D.projection
    D.isFppfQuotient hi.1.isUnipotent hsplit hstable
    RelativeRoot.torusVectorActionLinearization
  have hs : s ≫ D.projection = 𝟙 D.quotient :=
    hQ.splitUnipotentExtensionSection_comp i D.projection
    D.isFppfQuotient hi.1.isUnipotent hsplit hstable
    RelativeRoot.torusVectorActionLinearization
  exact {
    toGeometricRadicalTorusQuotient := D
    sectionHom := s
    sectionHom_comp := hs
  }

/-- A supplied split geometric radical gives rational maximal-torus conjugacy,
subject to the absolute quotient and stable-vector statements. -/
theorem maximalToriAreConjugate_of_splitGeometricUnipotentRadical
    (hquot : SolvableTorusQuotientStatement.{u})
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    {k : Type u} [Field k]
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (i : U ⟶ G) (hi : LeviSubgroup.IsGeometricUnipotentRadical i)
    (hsplit : RelativeRoot.IsSplitUnipotent U) (hG : IsSolvableGroupScheme G) :
    MaximalToriAreConjugate G := by
  let : Smooth U.X.hom := hi.1.smooth
  let : ConnectedSpace U.X.left := hi.1.connectedSpace
  let D := hi.sectionedTorusQuotient hquot hstable hsplit hG
  exact maximalToriAreConjugate_of_splitUnipotent_torus_section
    hstable RelativeRoot.torusVectorActionLinearization
    i hi.1.isClosedSubgroup hi.1.isUnipotent hsplit
    D.projection D.isFppfQuotient D.sectionHom D.sectionHom_comp
    D.toGeometricRadicalTorusQuotient.isTorus

/-- The exact rational maximal-torus conjugacy statement follows from the three
remaining structural prerequisites, with no geometric-maximality premise. -/
theorem solvableMaximalTorusConjugacy_of_structuralStatements
    (hrad : TorusGeneratedSplitGeometricRadicalStatement.{u})
    (hquot : SolvableTorusQuotientStatement.{u})
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u}) :
    SolvableMaximalTorusConjugacyStatement.{u} := by
  intro k _ G _ _ _ hG
  let D := smoothTorusGeneratedEnvelope G
  let : Smooth D.group.X.hom := smoothTorusGeneratedEnvelope_smooth G
  let : ConnectedSpace D.group.X.left :=
    smoothTorusGeneratedEnvelope_connectedSpace G
  let : IsAffineHom D.group.X.hom := D.isAffineHom
  have hsolv : IsSolvableGroupScheme D.group := D.isSolvableGroupScheme hG
  obtain ⟨U, i, hi, hsplit⟩ :=
    hrad k D.group hsolv D.isTorusGenerated
  exact D.maximalToriAreConjugate
    (maximalToriAreConjugate_of_splitGeometricUnipotentRadical
      hquot hstable i hi hsplit hsolv)

end Langlands.GroupScheme

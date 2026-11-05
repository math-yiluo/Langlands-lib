import Langlands.GroupScheme.Rational.SolvableMaximalTorusStructuralAssembly
import Langlands.GroupScheme.Rational.SplitTorusDominationProof

/-! # Rational maximal-torus conjugacy from quotient existence alone -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Retain the split geometric radical and its actual torus quotient using
only the initial dominated-quotient statement as a structural input. -/
def IsTorusGenerated.splitGeometricRadicalTorusQuotientOfDominatedQuotient
    (hquot : SplitTorusDominatedSolvableQuotientStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsTorusGenerated G) (hsolv : IsSolvableGroupScheme G) :
    SplitGeometricRadicalTorusQuotient G :=
  hG.splitGeometricRadicalTorusQuotientOfStructuralStatements
    hquot unipotentSplitTorusDomination
    RelativeRoot.splitUnipotentStableVectorSubgroup hsolv

/-- Absolute torus-quotient existence supplies the same retained radical and
quotient data over the original field, without a further structural premise. -/
def IsTorusGenerated.splitGeometricRadicalTorusQuotientOfTorusQuotient
    (hquot : SolvableTorusQuotientStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsTorusGenerated G) (hsolv : IsSolvableGroupScheme G) :
    SplitGeometricRadicalTorusQuotient G :=
  hG.splitGeometricRadicalTorusQuotientOfDominatedQuotient
    (splitTorusDominatedSolvableQuotient_of_solvableTorusQuotient hquot) hsolv

/-- Initial dominated-quotient existence is the sole remaining structural
premise for the exact arbitrary-field maximal-torus conjugacy target. -/
theorem solvableMaximalTorusConjugacy_of_dominatedQuotient
    (hquot : SplitTorusDominatedSolvableQuotientStatement.{u}) :
    SolvableMaximalTorusConjugacyStatement.{u} :=
  solvableMaximalTorusConjugacy_of_splitTorusDominatedQuotient
    hquot unipotentSplitTorusDomination

/-- Absolute quotient existence suffices for the exact arbitrary-field
maximal-torus conjugacy target, with all other structural inputs discharged. -/
theorem solvableMaximalTorusConjugacy_of_torusQuotient
    (hquot : SolvableTorusQuotientStatement.{u}) :
    SolvableMaximalTorusConjugacyStatement.{u} :=
  solvableMaximalTorusConjugacy_of_torusQuotient_and_dominationSplitness
    hquot unipotentSplitTorusDomination

end Langlands.GroupScheme

import Langlands.GroupScheme.Dynamic.SeparablyClosedCase
import Langlands.GroupScheme.PseudoParabolicQuotientSeparableReduction
import Langlands.GroupScheme.PseudoParabolicQuotientReductionStatement
import Langlands.CommutativeAlgebra.SeparablyClosedRationalPointProof
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientProof
import Langlands.GroupScheme.PseudoParabolicQuotientReductionProof
import Langlands.GroupScheme.Reductive.PseudoReductiveSeparableExtensionProof
import Langlands.GroupScheme.Reductive.PseudoReductiveRationalUnipotentPointProof
import Langlands.GroupScheme.Dynamic.FlagQuotientProof

/-! # CGP Proposition C.1.6 from its separately stated inputs

The pseudo-completeness of pseudo-parabolic quotients follows from the following inputs:
- the pseudo-reductive reduction (CGP 2.2.10);
- separable base change of pseudo-reductivity (CGP 1.1.9(1));
- the triviality of rational unipotent points that become radical;
- proper dynamic flag quotients.

The unipotent radical statements are applied through their Library proofs
`unipotentRadicalExistence` and `unipotentRadicalQuotient`. Rational points of geometrically
reduced algebras over separably closed fields come from
`CommutativeAlgebra.SeparablyClosedRationalPointProof.separablyClosedRationalPoint`.
The first three inputs are then discharged by their Library proofs. Finally the flag
quotient input is discharged by the Library proof `dynamicFlagQuotientExistence`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Corepresented

/-- **CGP Proposition C.1.6, conditional form.** -/
theorem pseudoParabolicQuotientPseudoComplete_of_statements
    (hred : PseudoParabolicQuotientPseudoReductiveReductionStatement.{u})
    (hsep : PseudoReductiveSeparableExtensionStatement.{u})
    (hc : PseudoReductiveRationalUnipotentPointStatement.{u})
    (hflag : DynamicFlagQuotientExistenceStatement.{u}) :
    PseudoParabolicQuotientPseudoCompleteStatement.{u} :=
  pseudoParabolicQuotientPseudoComplete_of_dynamic hred
    (dynamicParabolicQuotientDVRLifting_of_isSepClosed hsep fun k _ _ =>
      dynamicParabolicQuotientDVRLifting_of_corepresented
        (corepresentedDynamicParabolicQuotientDVRLifting_of_isSepClosed unipotentRadicalExistence
          unipotentRadicalQuotient hflag hsep hc k fun R =>
            CommutativeAlgebra.SeparablyClosedRationalPointProof.separablyClosedRationalPoint.{u, u}
              k R))

/-- **CGP Proposition C.1.6, from proper dynamic flag quotients.** The other inputs of
`pseudoParabolicQuotientPseudoComplete_of_statements` are discharged by their Library proofs. -/
theorem pseudoParabolicQuotientPseudoComplete_of_flagQuotientExistence
    (hflag : DynamicFlagQuotientExistenceStatement.{u}) :
    PseudoParabolicQuotientPseudoCompleteStatement.{u} :=
  pseudoParabolicQuotientPseudoComplete_of_statements
    pseudoParabolicQuotientPseudoReductiveReduction pseudoReductiveSeparableExtension
    pseudoReductiveRationalUnipotentPoint hflag

/-- **CGP Proposition C.1.6.** Let `P` be a pseudo-parabolic subgroup of a smooth connected
affine group `G` over a field `k`. Let `q : G → Q` be smooth, surjective and quasi-compact,
with `Q` separated, quasi-compact and locally of finite type, and with fibers the `P`-cosets
on all test points. Then `Q` is pseudo-complete. -/
theorem pseudoParabolicQuotientPseudoComplete :
    PseudoParabolicQuotientPseudoCompleteStatement.{u} :=
  pseudoParabolicQuotientPseudoComplete_of_flagQuotientExistence dynamicFlagQuotientExistence

end Langlands.GroupScheme

# CGP Proposition C.1.6 from its separately stated inputs

This module chains together the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6, stated in the
Library as `PseudoParabolicQuotientPseudoCompleteStatement`. The first theorem
takes four published Library statements as explicit hypotheses. The second
theorem discharges three of them with their Library proofs and keeps
`DynamicFlagQuotientExistenceStatement` as a hypothesis. The third theorem,
`pseudoParabolicQuotientPseudoComplete`, discharges that last hypothesis with
its Library proof. It proves the target statement with no hypotheses.

## `pseudoParabolicQuotientPseudoComplete_of_statements`

Hypotheses, each a published Library statement:
- `hred : PseudoParabolicQuotientPseudoReductiveReductionStatement.{u}`
  (CGP 2.2.10 with 2.1.9);
- `hsep : PseudoReductiveSeparableExtensionStatement.{u}` (CGP 1.1.9(1),
  separable algebraic case);
- `hc : PseudoReductiveRationalUnipotentPointStatement.{u}`;
- `hflag : DynamicFlagQuotientExistenceStatement.{u}`.

The unipotent radical statements are not hypotheses. The proof applies their
Library proofs `unipotentRadicalExistence` and `unipotentRadicalQuotient`.
The Library statement `SeparablyClosedRationalPointStatement` is not a
hypothesis either. The proof applies its Library proof
`CommutativeAlgebra.SeparablyClosedRationalPointProof.separablyClosedRationalPoint`
(module `Langlands.CommutativeAlgebra.SeparablyClosedRationalPointProof`) at
equal universes `.{u, u}`.

Conclusion: `PseudoParabolicQuotientPseudoCompleteStatement.{u}`.

Proof. The chain is:
1. `pseudoParabolicQuotientPseudoComplete_of_dynamic` with `hred` reduces to
   `DynamicParabolicQuotientDVRLifting k` for every field `k`.
2. Worker 254's `dynamicParabolicQuotientDVRLifting_of_isSepClosed` with `hsep`
   reduces this to separably closed fields. It uses base change to a separable
   closure and descent of the DVR lifting property along algebraic extensions.
3. Worker 254's `dynamicParabolicQuotientDVRLifting_of_corepresented` reduces to
   corepresented groups.
4. That case is `corepresentedDynamicParabolicQuotientDVRLifting_of_isSepClosed`,
   applied to `unipotentRadicalExistence`, `unipotentRadicalQuotient`, `hflag`,
   `hsep`, `hc` and `separablyClosedRationalPoint.{u, u} k`.

## `pseudoParabolicQuotientPseudoComplete_of_flagQuotientExistence`

Hypothesis: `hflag : DynamicFlagQuotientExistenceStatement.{u}`.

Conclusion: `PseudoParabolicQuotientPseudoCompleteStatement.{u}`.

Proof. Apply `pseudoParabolicQuotientPseudoComplete_of_statements` to these
Library proofs:
- `pseudoParabolicQuotientPseudoReductiveReduction` for `hred` (module
  `Langlands.GroupScheme.PseudoParabolicQuotientReductionProof`);
- `pseudoReductiveSeparableExtension` for `hsep` (module
  `Langlands.GroupScheme.Reductive.PseudoReductiveSeparableExtensionProof`);
- `pseudoReductiveRationalUnipotentPoint` for `hc` (module
  `Langlands.GroupScheme.Reductive.PseudoReductiveRationalUnipotentPointProof`);
- the hypothesis `hflag`.

## `pseudoParabolicQuotientPseudoComplete`

Statement: `PseudoParabolicQuotientPseudoCompleteStatement.{u}`, with no
hypotheses. Let `k` be a field, `G` a smooth connected affine `k`-group and
`P` a pseudo-parabolic subgroup in the sense of `IsPseudoParabolicSubgroup`.
Let `q : G → Q` be smooth, surjective and quasi-compact, with `Q` separated,
quasi-compact and locally of finite type over `k`. Assume that for every test
object `T`, two points `g, h ∈ G(T)` have the same image in `Q` exactly when
`g⁻¹ h ∈ P(T)`. Then `Q` is pseudo-complete (`IsPseudoComplete Q`). This is
CGP Proposition C.1.6.

Proof. Apply `pseudoParabolicQuotientPseudoComplete_of_flagQuotientExistence`
to the Library proof `dynamicFlagQuotientExistence :
DynamicFlagQuotientExistenceStatement.{u}` (module
`Langlands.GroupScheme.Dynamic.FlagQuotientProof`).

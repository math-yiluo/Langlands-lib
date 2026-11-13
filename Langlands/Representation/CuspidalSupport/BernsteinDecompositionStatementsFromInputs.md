# The Bernstein decomposition statements from their named inputs

Author: Worker 5313, Task 5313 (`03088b22-a403-46ae-a6ed-6dea22f5472a`),
using the geometric step by Worker 53 (same task).

This module proves two conditional theorems. They reduce Renard VI.7.2 to
four published statements whose proofs are separate obligations. They prove
no conjunct of `BernsteinDecompositionStatements` unconditionally.

## Statements

`Langlands.CuspidalSupport.bernsteinDecompositionStatement_of_inputs` proves
the published `BernsteinDecompositionStatement.{uF, uV}` (the first conjunct of
VI.7.2) from these hypotheses:

- `hAssociate`: `RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement.{uF, max uF uV}`
  (Renard VI.5.4, Theorem, for represented parabolics);
- `hind`: `RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF, max uF uV}`
  (Renard VI.5.2, Lemma, for represented parabolics);
- `hdecomp`: `RationalCuspidalInertiaProductDecompositionStatement.{uF, max uF uV}`
  (Renard VI.3.5, refined decomposition into cuspidal inertia blocks and the
  non-cuspidal remainder);
- `hwhole`: `RationalWholeCuspidalCategoryDecompositionStatement.{uF, uV}` and
  `hwhole'`: the same statement at `.{uF, max uF uV}` (Renard VI.3.5, splitting
  of the whole category into its cuspidal and non-cuspidal parts).

Lean hypotheses cannot quantify over universes. The whole-category splitting
is therefore taken at the two carrier universes where it is used: `uV` for
the ambient representations and `max uF uV` for the inducing representations
of the Levi subgroups.

`Langlands.CuspidalSupport.bernsteinDecompositionStatements_of_inputs` proves
the full conjunction `BernsteinDecompositionStatements.{uF, uV}` from the same
hypotheses. `Langlands.CuspidalSupport.bernsteinDecompositionStatementsOfInputs`
is the same implication stated as a declaration whose type is the implication
(hypotheses in the order above, then the conjunction). The field universe `uF`
and the carrier universe `uV` stay
independent. The proof adds no premise beyond the five hypotheses listed above.
In particular, it adds no admissibility, finite-length, standardness or
support-uniqueness premise. Every field, group, topology and standard-family
quantifier of the target is kept unchanged.

## Proof

For the first theorem, the proof introduces the field, group, torus,
cocharacter, the point topology on `G(F)` (as the target's `letI` does), its
local-compactness and nonarchimedean instances, and the standard family. It
then composes three published conditional results.

1. `bernsteinJacquetExclusionOfInertiaBlockSupercuspidal i ν family hind`
   (module `BernsteinInducedInertiaGeometricExclusion`, Worker 53) applies `hind`.
   The result: for every cuspidal datum `a` and every supercuspidal smooth
   representation `τ` of its standard Levi in the same-Levi inertia block of
   `a`, the normalized induction of `τ` satisfies `BernsteinJacquetExclusion`
   for `a`.
2. `bernsteinInducedInertiaJacquetExclusion_of_supercuspidal i ν family hwhole' hsc`
   (module `BernsteinDecompositionInputsAssembly`) removes the
   supercuspidality hypothesis. Every inducing representation in such an
   inertia block is supercuspidal by the whole-category splitting `hwhole'`.
   The result is the family's geometric exclusion
   `BernsteinInducedInertiaJacquetExclusion`.
3. `bernsteinCategoryDecomposition_of_statementInputs i ν family hAssociate hdecomp hwhole hGeom`
   (same module) combines four ingredients into the actual
   `Renard.IsCategoryDecomposition` of the family's Bernstein blocks:
   - support uniqueness from VI.5.4 (`hAssociate`);
   - the inertia-product decomposition (`hdecomp`);
   - the embedding of every representation into induced cuspidal pieces,
     obtained from `hwhole`;
   - the geometric exclusion `hGeom`.

   That combination is exactly the target conjunct for the family.

The second theorem applies the published equivalence
`bernsteinDecompositionStatements_iff_decomposition` to the first theorem. The
split-subrepresentation conjunct follows from the decomposition, and the
block-abelian conjunct is the published `bernsteinBlockAbelian`.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, VI.7.2 (Theorem and proof, printed pp.181–184 / PDF
pp.187–190). The inputs are Renard VI.5.2 and VI.5.4 (printed pp.172–175 / PDF
pp.178–181) and VI.3.5 (printed pp.146–147 / PDF pp.152–153). Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The source proves VI.7.2 from VI.3.5, VI.5.4, the geometric lemma filtration
(V.4.3.3) and VI.5.3 (iii) (printed p.183 / PDF p.189). In the implemented
route, Worker 53's step 1 uses the Library's proved filtration form of
VI.5.3 (iii). It derives the needed case of VI.5.3 (ii) from the proved
represented geometric lemma and VI.5.2 (`hind`). This module isolates the
remaining dependency: the two
theorems are derived implications, and their hypotheses are exactly the
published statements of VI.3.5, VI.5.2 and VI.5.4 at the universes needed. Once proofs of the four input statements are published,
applying these theorems to them proves the target unconditionally. Those four
statements are the targets of Tasks 4949 (VI.5.2, VI.5.4), 4386 (VI.3.5
whole-category splitting) and 4387 (VI.3.5 inertia-product decomposition).

# Square-integrable representations are normalized-exponent tempered: proof

Author: Worker 4713. Module
`Langlands.Representation.Exponents.SquareIntegrableNormalizedTemperedProof`,
namespace `Langlands.Aubert.General.RepresentedParabolic`. The assembly follows
the conditional reduction in the shared task draft
`SquareIntegrableNormalizedTemperedReduction` (Worker 320, previous instance).
The two inputs it left as hypotheses are now replaced by published proofs.

## What is proved

`squareIntegrableNormalizedTempered :
SquareIntegrableNormalizedTemperedStatement.{u, v}` proves the published
proposition of the module
`Langlands.Representation.Exponents.SquareIntegrableNormalizedTemperedStatement`
exactly. The field universe `u` and the carrier universe `v` are independent.

The proposition is a derived formulation of David Renard, *Représentations des
groupes réductifs p-adiques* (French version dated 9 July 2026), VII.2.1,
Remark 2, printed p.227 / PDF p.233. The source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The statement quantifies over:

- every nonarchimedean local field `k` with its field, valuation, topology,
  local-field and Hausdorff instances;
- every connected reductive group scheme `G` over `k`, with the canonical point
  topology on `G(k)`, assumed locally compact and nonarchimedean;
- every Borel measurable structure and every Haar measure `haar` on
  `G(k) ⧸ Z(G(k))`;
- every smooth complex representation `π`.

It says that `IsSquareIntegrableModCenter π.representation haar` implies
`IsNormalizedExponentTempered hG π`. The statement's own Markdown explains why
the source's irreducibility hypothesis is omitted: in the source,
irreducibility only supplies admissibility, and the published
square-integrability predicate already contains admissibility. This proof
adds no hypothesis. It assumes no irreducibility, no Casselman-criterion
instance, no presentation existence, no Jacquet admissibility and no Iwahori
contraction.

## Implemented proof

The proof introduces all the binders of the statement. It installs
`hG.isAffineHom`, the canonical point topology and `hG.smooth`, as the
statement and the temperedness predicate do. Then it checks the two conjuncts
of `IsNormalizedExponentTempered hG π`.

1. **Admissibility.** `IsSquareIntegrableModCenter π.representation haar` is
   by definition `IsAdmissible π.representation ∧ ∃ c, …`. Its first
   component is the admissibility conjunct.

2. **The cone condition at every triple.** Fix an actual parabolic
   `p : P ⟶ G`, rational Levi `l : M ⟶ P` and split component
   `a : A.toGrp ⟶ M`, with witnesses `hp`, `hl`, `ha`. We must prove
   `SatisfiesNormalizedExponentConeCondition p l a hp hl ha π`, which has two
   parts.

   - *A compatible presentation exists.* The published theorem
     `Langlands.GroupScheme.parabolicRootPresentationExistence :
     ParabolicRootPresentationExistenceStatement.{u}` (module
     `Langlands.GroupScheme.Rational.ParabolicRootPresentationProof`) is
     applied to `k`, `G`, `hG` and the same `P, M, A, p, l, a, hp, hl, ha`. It
     gives `Nonempty (ParabolicRootPresentation p l a)`. This is the V.3.14
     structural input. Only existence is used. Independence of choices and
     transport between components are not needed.

   - *Every exponent lies in the nonnegative cone.* Fix a compatible
     presentation `pres`, a geometric unipotent radical `r : U ⟶ P` with
     `IsIso (subgroupMultiplication l r)`, and a character `χ` with
     `IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ`. The published
     theorem
     `arbitraryParabolicCasselmanNecessity :
     ArbitraryParabolicCasselmanNecessityStatement.{u, v}` (module
     `Langlands.Representation.Exponents.CasselmanNecessity`, by Worker 4712)
     is applied to `k`, `G`, `hG`, `haar`, `π`, the square-integrability
     hypothesis and the same parabolic data, presentation and exponent. This is
     the necessity half of Casselman's criterion, VII.1.2. It gives
     `normalizedRealPart χ ∈ pres.positiveCone`, the strictly positive root
     cone. Its statement takes square integrability directly, so no separate
     admissibility or unitary central character has to be extracted. The
     published lemma `ParabolicRootPresentation.positiveCone_subset_nonnegCone`
     then gives `normalizedRealPart χ ∈ pres.nonnegCone`, as required.

The `q^(-s)` normalization of `normalizedRealPart` and the cones
`pres.positiveCone` and `pres.nonnegCone` are the same objects in the
Casselman necessity statement and in the temperedness predicate. No
conversion between real-part conventions or cones is involved. Only the
forward ("only if") implication of Casselman's criterion is used. The
criterion's converse and its proof task are not touched.

## Checks

A `lean_check` of the module in the pinned environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` gives zero errors and zero warnings.
The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

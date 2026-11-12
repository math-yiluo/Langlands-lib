# Rational conjugacy of minimal parabolic subgroups: proof

Author: Worker 4107. The Lean bodies combine published Library theorems. The
composite terms are adapted from the public note by Worker 15
[Group schemes: unconditional rational lifting and maximal split torus
conjugacy](../../../notes/group-schemes/smooth-split-torus-conjugacy-route.md)
(rows for C.2.2, C.2.4, C.2.5 and `MinimalParabolicConjugacyStatement`). Here
they are instantiated with the proofs now in the Library.

## Result

`Langlands.GroupScheme.minimalParabolicConjugacy` proves exactly the published
proposition `Langlands.GroupScheme.MinimalParabolicConjugacyStatement.{u}` of
`Langlands.GroupScheme.Rational.MinimalParabolicStatement`, at its universe
`u`, with no added premise. Write `S = Spec (CommRingCat.of k)`. Take any field
`k : Type u`, any group scheme `G` over `S` with `IsConnectedReductive G`, and
homomorphisms `j : P ⟶ G` and `j' : P' ⟶ G` with `IsMinimalParabolicSubgroup j`
and `IsMinimalParabolicSubgroup j'`. The theorem gives a rational point
`g : Over.mk (𝟙 S) ⟶ G.X` and a group scheme isomorphism `e : P ≅ P'` with

`j ≫ (G.innerIso g).hom = e.hom ≫ j'`.

This is conjugacy of the actual subgroup schemes, not only of their rational
points. Minimality is the published all-test notion: among parabolic subgroups
over `k`, with ranges compared as subgroup functors on every test scheme. The
field is arbitrary: finite or infinite, of any characteristic, perfect or not.
`G` need not be split. The only axioms used are `propext`, `Classical.choice`
and `Quot.sound`.

The source is Borel and Tits, *Groupes réductifs* (1965), Théorème 4.13(b),
printed p.90. Borel and Tits argue with Bruhat-type structure and treat finite
fields separately. This Lean proof follows another route: Conrad–Gabber–Prasad
(CGP), *Pseudo-reductive groups*, second edition (2015), Theorem C.2.5 for
minimal pseudo-parabolic subgroups, together with Proposition 2.2.9, which says
that for connected reductive groups the pseudo-parabolic subgroups are the
parabolic ones. Both arguments work over every field.

## Declarations

All declarations are in namespace `Langlands.GroupScheme`. The three helper
theorems are in the sub-namespace `MinimalParabolicConjugacyProof`, so they do
not clash with later proofs of the same statements under other names.

- `MinimalParabolicConjugacyProof.splitSolvableIntoPseudoParabolic :
  SplitSolvableIntoPseudoParabolicStatement.{u}` (CGP Lemma C.2.2).
- `MinimalParabolicConjugacyProof.pseudoParabolicMaximalSplitTorusStructure :
  PseudoParabolicMaximalSplitTorusStructureStatement.{u}` (CGP Proposition
  C.2.4, with the maximality observation just before it).
- `MinimalParabolicConjugacyProof.minimalPseudoParabolicConjugacy :
  MinimalPseudoParabolicConjugacyStatement.{u}` (CGP Theorem C.2.5).
- `minimalParabolicConjugacy : MinimalParabolicConjugacyStatement.{u}`, the
  target.

Every structural input below is a published proof. None is a hypothesis of any
of these theorems.

## Step 1: C.2.2, moving a split solvable subgroup into a pseudo-parabolic

`splitSolvableIntoPseudoParabolic` applies the published reduction
`splitSolvableIntoPseudoParabolic_of_components`
(`SplitTorusIntoPseudoParabolicReduction`) to five published proofs:

- `smoothSubgroupQuotientExistence` (`HomogeneousQuotientProof`): quotients
  `G/P` by smooth closed subgroups exist;
- `pseudoParabolicSubgroupStructure` (`PseudoParabolicStructureProof`):
  pseudo-parabolic subgroups are smooth, connected and affine;
- `pseudoParabolicQuotientPseudoComplete`
  (`PseudoParabolicQuotientPseudoCompleteAssembly`): `G/P` is pseudo-complete;
- `splitSolvablePseudoCompleteFixedPoint` (`SplitSolvableFixedPointProof`): a
  split solvable group acting on a pseudo-complete scheme with a rational point
  has a rational fixed point;
- `pseudoParabolicQuotientRationalLifting`
  (`PseudoParabolicQuotientRationalLiftingProof`, CGP Lemma C.2.1): rational
  points of `G/P` lift to `G(k)`.

## Step 2: C.2.4, maximal split tori of a pseudo-parabolic

Take `G` smooth, connected and affine, a pseudo-parabolic `i : P ⟶ G` and a
maximal split torus `s : S.toGrp ⟶ P`.

- The first two clauses are the published
  `pseudoParabolicTorusCentralizerContainment_of_conjugacy`
  (`Rational.PseudoParabolicMaximalSplitTorusStructureReduction`). It is applied
  to `smoothMaximalSplitTorusConjugacy`
  (`Rational.SmoothMaximalSplitTorusConjugacyProof`, CGP Theorem C.2.3). These
  clauses say that `s ≫ i` is a maximal split torus of `G` and that
  `torusCentralizer (s ≫ i) ≤ SubgroupFunctor.range i`.
- Let `U ⟶ P` be a split ground-field unipotent radical. Minimality implies the
  product criterion by the published
  `pseudoParabolicCentralizerProductOfMinimality_of_statements`
  (`Rational.MinimalPseudoParabolicCentralizerProduct`). It is applied to C.2.3,
  `pseudoParabolicSplitRadicalProduct` (`PseudoParabolicSplitRadicalProductProof`)
  and `pseudoParabolicSplitRadicalContainment`
  (`PseudoParabolicSplitRadicalContainmentProof`).
- The converse is the published
  `pseudoParabolicMinimalityOfCentralizerProduct_of_statements`
  (`Rational.PseudoParabolicMinimalityCriterionReduction`). It is applied to
  C.2.3, `pseudoParabolicSplitSolvableEnvelope`
  (`Rational.PseudoParabolicSplitSolvableEnvelopeProof`) and the C.2.2 theorem
  of Step 1.

## Step 3: C.2.5, conjugacy of minimal pseudo-parabolics

`minimalPseudoParabolicConjugacy` applies the published assembly
`minimalPseudoParabolicConjugacy_of_structure`
(`Rational.MinimalPseudoParabolicConjugacyAssembly`) to five inputs:

- `pseudoParabolicSubgroupStructure`;
- `SplitUnipotentRadicalExistence.splitUnipotentRadicalExistence`
  (`Reductive.SplitUnipotentRadicalExistenceProof`);
- `pseudoParabolicSplitSolvableEnvelope`;
- the C.2.2 theorem of Step 1;
- the C.2.4 theorem of Step 2.

The assembly follows CGP's proof of C.2.5. Let `i : P ⟶ G` and `j : Q ⟶ G` be
the two minimal pseudo-parabolics.

1. Take a maximal split torus `s` of `P` and a split ground-field unipotent
   radical `U` of `P`. The envelope statement gives a split solvable subgroup
   `H` of `P` representing the product of `s` and `U`.
2. C.2.2 gives `g ∈ G(k)` that conjugates `H` into `Q`. Write `j'` for the
   conjugate of `j` by `g⁻¹`. It is again minimal pseudo-parabolic, and it
   contains the images of `H`, of `s` and of `U` on every test.
3. C.2.4 for `P` says that `s ≫ i` is maximal split in `G`. It lifts to a
   maximal split torus of `j'`. C.2.4 for `j'` then puts
   `torusCentralizer (s ≫ i)` inside the range of `j'`.
4. Since `P` is minimal, the C.2.4 criterion presents `P` as the product of
   that centralizer and `U`. So the range of `i` is contained in the range of
   `j'`.
5. Minimality of `j'` turns this inclusion into actual subgroup conjugacy
   (`SubgroupConjugate`) of `i` and `j'`. Composing with the conjugation by `g`
   gives `SubgroupConjugate i j`.

## Step 4: from pseudo-parabolic to parabolic

`minimalParabolicConjugacy` applies the published
`minimalParabolicConjugacyStatement_of_pseudoParabolic`
(`Rational.ReductivePseudoParabolicComparison`) to three inputs:

- `parabolicDynamic` (`Absolute.ParabolicDynamicProof`, Milne 25.1): a closed
  subgroup of a connected reductive group is parabolic exactly when its range is
  `Dynamic.parabolic χ` for a cocharacter `χ` over `k`;
- `fun _ _ _ hG => hG.hasTrivialUnipotentRadical`, the published
  `IsConnectedReductive.hasTrivialUnipotentRadical`
  (`Reductive.ToPseudoReductive`): a connected reductive group has trivial
  ground-field unipotent radical;
- the C.2.5 theorem of Step 3.

With these inputs, that reduction shows that a minimal parabolic `j` is a
minimal pseudo-parabolic. A parabolic is `P(χ)`, which is the represented fppf
product of `P(χ)` and the trivial radical. Conversely, a pseudo-parabolic has
trivial radical factor, so its range is `P(χ)`, and it is parabolic by
`parabolicDynamic`. The minimality conditions therefore agree. C.2.5 for `j` and
`j'` gives the rational point `g` and the isomorphism `e`. The smoothness,
connectedness and affineness hypotheses of C.2.5 come from
`IsConnectedReductive G`.

## Dependency direction

No theorem used here takes `RelativeWeylGroupRestrictStatement`,
`RationalBruhatStatement`, `StandardParabolicClassificationStatement`, a
relative-root-system statement or a relative Tits-system statement as a
premise. The module's transitive import closure does not contain the proof
modules `Rational.RationalBruhatProof`,
`Rational.StandardParabolicClassificationProof` or
`Rational.RelativeRootSystemProof`. Some modules in that closure define those
statements, or state conditional theorems about them, but the proof does not
use them. The target had no proof before this module, so no input depends on
it.

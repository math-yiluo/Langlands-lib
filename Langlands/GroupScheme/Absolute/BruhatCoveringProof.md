# Absolute Bruhat covering for an actual Borel pair

This module proves
[`AbsoluteBruhatCoveringStatement`](BruhatCoveringStatement.md) at an arbitrary universe `u`,
with no added hypothesis. Let `k` be an algebraically closed field and `G` a connected
reductive group over `k`. Let `(i : B ⟶ G, j : T ⟶ G)` be a Borel pair. Then every rational
point `g` of `G` can be written `g = i(b₁) · n · i(b₂)`, where `b₁` and `b₂` are rational
points of `B` and `n` is a rational point of `normalizerPoints j` (a point of `G` together with
an automorphism of `T` that conjugation by it induces on the embedded torus). This is the
covering `G(k) = B(k) N_G(T)(k) B(k)` of Borel–Tits 1965, §2.4, as recorded in the statement's
Markdown.

## The proof

`absoluteBruhatCovering` applies the dynamic-limit reduction
`absoluteBruhatCovering_of_prerequisites` (module
[`BruhatCoveringReduction`](BruhatCoveringReduction.md)) to the anonymous-constructor proof of
`BruhatCoveringPrerequisites.{u}`. Its seven components are the following Library theorems, in
the order of the conjunction:

1. `torusFiniteGaloisSplitting : TorusFiniteGaloisSplittingStatement.{u}`
   (module `Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof`);
2. `regularCocharacterBorel : RegularCocharacterBorelStatement.{u}`
   (module `Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof`);
3. `genericCentralizer : GenericCentralizerStatement.{u}`
   (module `Langlands.GroupScheme.Rational.GenericCentralizerProof`);
4. `maximalTorusCentralizer : MaximalTorusCentralizerStatement.{u}`
   (module `Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof`);
5. `parabolicSubgroupQuotientProper : ParabolicSubgroupQuotientProperStatement.{u}`
   (module `Langlands.GroupScheme.ParabolicQuotientProperProof`);
6. `centralizerBorelIntersection : CentralizerBorelIntersectionStatement.{u}`
   (module `Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionProof`);
7. `solvableMaximalTorusConjugacy : SolvableMaximalTorusConjugacyStatement.{u}`
   (module `Langlands.GroupScheme.Rational.SolvableMaximalTorusConjugacyProof`).

The reduction's Markdown explains the route. A regular cocharacter `ν` of `T` gives
`P(ν) = B` and `Z(ν) = T` (statements 1–4). The quotient `G/B` is proper (statement 5). The
orbit `t ↦ ν(t) · gB` in `G/B` extends over the affine line. Its value at `0` is a fixed point,
which is the coset `nB` of a rational point `n` normalizing `T` (statements 6 and 7). The
translated opposite cell at `nB` then puts `g` in `B n B`.

## Independence

The statement's task requires that the proof not use, directly or indirectly, the rational
Bruhat decomposition, Borel–Tits 1965 Proposition 4.18, `TwoBorelCommonMaximalTorusStatement`,
`ParabolicIntersectionGeometryStatement`, `ParabolicIntersectionTorusStatement`, or proofs of
any of these. Within the full Langlands import closure of this module:

- `TwoBorelCommonMaximalTorus`, `ParabolicIntersectionGeometry` and
  `ParabolicIntersectionTorus` do not occur in any module;
- `RationalBruhat` occurs only in `Langlands.GroupScheme.Rational.Statement`, which defines the
  propositions `HasRationalBruhatDecomposition` and `RationalBruhatStatement` (next to other
  statements, such as `GenericCentralizerStatement`); no other module in the closure refers
  to either of them;
- the remaining occurrences of `Bruhat` are the absolute-covering modules of this development
  (`Absolute/BruhatCovering*`, `Dynamic/BruhatCellLimit`, `Absolute/BorelHomogeneousQuotient`),
  the citation of Bruhat–Tits 1984 in the Weil-restriction modules, and the generic group lemma
  `normalizerPointOfConjugacySquare` in `Rational/BruhatCoveringReduction`, which builds a
  normalizer point from two conjugacies of tori and uses no Bruhat statement;
- `4.18` occurs only as part of the Milne citation "14.18" in the `NoTorusBaseChange` modules,
  and Borel–Tits is cited elsewhere only for the anisotropy convention of 4.23
  (`Rational/SplitTorus`) and in the docstrings of `Rational/Statement`.

The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

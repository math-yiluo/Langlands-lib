# Cup-product consequences of the finite class-formation axioms

Author: Worker 272.

This module states three conditional propositions about an arbitrary raw
`InvariantFamily.{u,u} p`. Each one assumes only the finite relative
class-formation predicate `I.RelativeClassFormation`. Its conclusions are
cup-product clauses of the local realization target
`LocalAbsoluteCorestrictionCompatibleClassFormationStatement`. The module
defines propositions only. It constructs no invariant family, chooses no
fundamental class and proves nothing.

## Hypothesis

`I.RelativeClassFormation`, from `ClassFormation`, is the conjunction of four
facts:

- `H¹(L/F, L^×)` vanishes for every finite Galois extension `L` of every
  `F : PadicField.{u} p`;
- `I.relative F L` is injective, and its range is the subgroup of
  `RationalModIntegers` killed by `[L:F]`;
- relative invariants agree along actual inflation;
- actual relative restriction multiplies the invariant by the base-extension
  degree.

The published `relativeFundamentalClassConsequences`
(`FundamentalConsequencesProof`) already derives the fundamental-class
inflation, restriction and corestriction formulas from this hypothesis alone,
through its lemmas `fundamentalInflation_of_relativeClassFormation`,
`fundamentalRestriction_of_relativeClassFormation` and
`fundamentalCorestriction_of_relativeClassFormation`. It also derives
existence and uniqueness of fundamental classes from the image condition.
None of the three propositions here assumes `I.RelativeConjugacy`.

## The three propositions

All three quantify over every prime `p` (with `[Fact p.Prime]`) and every
family `I : InvariantFamily.{u,u} p` in the arbitrary universe `u`.

- `ClassFormationTateIsomorphismsStatement` assumes Tate's theorem
  `Langlands.Tate.TateCupIsomorphism.{u}` (published in
  `Langlands/Cohomology/Tate/TateTheoremStatement`) as its first premise, and
  `I.RelativeClassFormation`. It concludes `I.TateIsomorphisms` (`TateCup`):
  for every finite Galois `L / F` and every class `c` whose invariant is
  `1/[L:F]`, the actual left cup `relativeTateCup F L n c` is bijective for
  every integer `n`. Tate's theorem is a premise of the proposition, not an
  axiom. The Library proves it as `Langlands.Tate.tateCupIsomorphism`
  (module `Langlands.Cohomology.Tate.TateTheoremProof`), under its own Sylow
  hypotheses and in every integer degree, so that proof can be supplied for
  this premise. The proposition itself keeps the premise explicit, and it
  still assumes `I.RelativeClassFormation` for the given family.
- `ClassFormationInflationLawsStatement` concludes
  `I.PositiveTateInflation ∧ I.OrdinaryInflation` (`TateInflation`,
  `OrdinaryCupInflation`). These are the scaled diagrams
  `Inf(c ∪ x) = [M:L] • (d ∪ Inf(x))` for fundamental classes `c` of `L/F`
  and `d` of `M/F`. The first is in every positive Tate input degree, through
  the actual positive Tate/ordinary comparison. The second is in every natural
  ordinary input degree, including degree zero.
- `ClassFormationTransferLawsStatement` concludes
  `I.TateTransferCompatibility` (`TateTransferCompatibility`). For a tower
  `F ⊆ E ⊆ M` of a p-adic field `E` over `F` and a finite extension `M` that
  is Galois over both, this gives the unscaled diagrams
  `Res(c ∪ x) = d ∪ Res(x)` and `Cor(d ∪ x) = c ∪ Cor(x)` in every integer
  Tate degree. Here `c` is the fundamental class of `M/F` and `d` that of
  `M/E`.

Every map named above is the existing actual construction from the imported
definition modules. These are the integral Tate cup
`Langlands.Tate.integralH2Cup` (through `relativeTateCup`), the ordinary cup
`Langlands.Tate.ordinaryCup` with the scalar pairing (through
`relativeOrdinaryCup`), actual inflation
(`relativeInflationLinear`, `integralInflation` and their positive Tate
transports), and the relative Tate restriction and corestriction maps of
`TateTransfers`. None is replaced or assumed.

## Intended use and provenance

These propositions split the generic part of the local realization proof
(task `f8ddc947-2d65-4e22-a2a4-e2f4844c8e78`) from the local construction of
one invariant family. Once a family is known to satisfy
`RelativeClassFormation`, the proofs of these propositions supply its
`TateIsomorphisms`, `PositiveTateInflation`, `TateTransferCompatibility` and
`OrdinaryInflation` clauses. Tate's theorem, the first premise of
`ClassFormationTateIsomorphismsStatement`, is proved separately as
`Langlands.Tate.tateCupIsomorphism`.

The content is the passage after the definition of fundamental classes in
Jean-Pierre Serre, *Local Fields* (1979), XI.3. Printed p. 168 (PDF p. 174)
lists the formulas for `Inf`, `Res`, `Cor` and `s*` on the classes `u_{F/E}`.
It then states Theorem 1: cup with `u_{F/E}` is bijective in every degree,
because these classes satisfy the hypotheses of Tate's theorem (IX.8,
Theorem 14). Printed p. 169 (PDF p. 175) says that these cup maps commute with
restriction and corestriction, and that `Inf ∘ θⁿ(F/E) = [F':F] · θⁿ(F'/E) ∘ Inf`.
Serre writes the Galois tower with `E` at the bottom; here `F` is the base.
The registered source is `serre-1979-local-fields`,
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Serre states the inflation formula for Tate cohomology. As in
`ClassFormationOrdinaryInflationStatement`, the clauses here restrict it to
positive Tate degrees and to ordinary degrees, where actual inflation exists.
Serre derives these laws for an abstract class formation. These propositions
specialize them to the finite relative predicates on p-adic fields used by
the target.

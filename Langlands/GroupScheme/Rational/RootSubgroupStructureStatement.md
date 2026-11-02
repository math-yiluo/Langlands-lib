# Relative-root kernel, realization, uniqueness and vector quotient targets

This file states unproved propositions for the actual functors constructed in
`RootSubgroup`. Every field and scheme universe is arbitrary. No split or
quasi-split hypothesis on the ambient connected reductive group is imposed.
The hypotheses specify a maximal split torus, allowing nonreduced relative
root systems and imperfect fields in every characteristic.

The normative sources are Kaletha–Prasad (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, §2.6.3 and §2.6.8 (printed
pp.94–95; PDF pp.125–126), and Proposition 2.11.9 with its proof and
Proposition 2.11.14 (printed pp.133–135; PDF pp.164–166); and
Conrad–Gabber–Prasad, second edition (2015), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, Proposition 3.3.6 and Lemma 3.3.8
(printed pp.109–112; PDF pp.135–138). The registered KP corrections of
1 November 2024 were checked at PDF p.25; the Section 2.11 notation changes
do not alter these assertions. KP's quasi-split Assumption 2.6.10 follows
§2.6.8, so it does not restrict the root-group structure stated here.

The supporting predicates use actual test-scheme geometry. A vector group of
dimension n has, naturally on every scheme T, point group the additive group
of n global functions on T. This is the Yoneda description of the additive
affine n-space group scheme; the predicate does not identify vector groups
merely by their rational points. `IsSplitUnipotent` requires a finite normal
series of smooth connected closed subgroup schemes with represented Ga
quotients and the trivial group as endpoint. These are internal formulations
of the standard vector-group and split-unipotent notions in the cited source.

`IsFppfQuotient N q` requires q to be flat, surjective and locally of finite
presentation and identifies its actual kernel functor with N on all tests.
An fppf cover gives local lifts of quotient points, so this specifies the
represented quotient as an fppf sheaf. It makes no claim that U(T) → V(T) is
surjective for every original test T, or that V(T) is U(T)/N(T). The finite
series and the two-step quotient both use this sheaf formulation.

`HasLieImage F W` compares the tangent image of F with W by testing the
actual dual-number identity-kernel points in G(k[ε]). This avoids choosing a
representative or a differential in the definition. For an actual monomorphic
representative it is the usual image of its Lie algebra in Lie(G).
`positiveWeightSpan` takes every positive integral multiple n·a, with no
reducedness restriction; `integralWeightSpan` includes all integer multiples,
including zero. The weight spaces are the Library's actual adjoint weight
spaces tested on all coefficient algebras.

The focused targets are:

- `CharacterFpqcStatement`: every nonzero character of a split torus is a
  quasi-compact flat surjection onto Gm. This is the quotient S/ker(a) ≅ Gm
  of KP §2.6.3; a is not required to be primitive.
- `KernelCentralizerStructureStatement`: for a smooth affine group over a
  field and a split torus acting by conjugation, the all-test kernel
  centralizer has a smooth closed representative, with Lie image all integral
  multiples of a. Connectedness is not asserted for this centralizer. This
  is the multiplicative-type fixed-locus fact used explicitly in the proof
  of CGP Proposition 3.3.6 and KP Proposition 2.11.9.
- `QuotientActionComparisonStatement`: given a closed representative and an
  fpqc character map, the direct functor is the image of the dynamic
  identity-limit functor for the constructed descended Gm action. The
  comparison works over any base; the representation and fpqc assumptions
  are explicit prerequisites of this comparison, while the final realization
  statement has neither as a hypothesis.
- `RootSubgroupRealizationStatement`: for each actual relative root a,
  the already defined functor Uₐ has a smooth connected closed representative
  which is unipotent and split, stable under the torus, with Lie image the
  full positive integral a-weight span. All existence and geometry occur in
  the conclusion.
- `RootSubgroupUniquenessStatement`: a smooth connected closed subgroup
  stable under S and with that precise Lie image has the same all-test
  functor as Uₐ. Connectedness is retained explicitly from CGP Proposition
  3.3.6; the target does not claim uniqueness among disconnected subgroups.
- `RootSubgroupVectorStatement`: if 2a is absent, every representative of
  Uₐ is a vector group. If 2a is present, U₂ₐ is contained in Uₐ, its points
  commute with every point of Uₐ on all tests, and every representative of
  Uₐ admits a represented fppf quotient by U₂ₐ which is a vector group.

`RootSubgroupStructureStatement` is the conjunction of these six targets.
The file supplies statements and their exact supporting predicates, with no
proof of the substantive conclusions. The independent general fixed-locus
representability, relative-root-system, and Levi-conjugation proof tasks
retain their existing owners. The kernel specialization and comparison here
are additional consumers of those prerequisites, not replacements for them.

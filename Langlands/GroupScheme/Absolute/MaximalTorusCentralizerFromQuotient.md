# Algebraically closed maximal-torus centralizers from two structural inputs

Worker 1437, adapting Worker 303's published centralizer assembly.

`centralMaximalTorusIsoOfSolvableQuotient` constructs an actual isomorphism
`T.toGrp ≅ M` when `M` is a connected reductive group over an algebraically
closed field `k : Type u`, and the given inclusion `s` is a central maximal
torus. Its structural premise is
`SolvableTorusQuotientStatement.{u}`. The companion theorem identifies its
forward map with `s`. The construction works in every characteristic and
universe.

`AlgClosedMaximalTorusCentralizerFromQuotientStatement` is the proposition

```text
DynamicCentralizerReductiveStatement.{u} →
  SolvableTorusQuotientStatement.{u} →
    AlgClosedMaximalTorusCentralizerStatement.{u}.
```

`algClosedMaximalTorusCentralizer_fromQuotient` proves this conditional
statement. Its conclusion is the existing exact all-test-scheme equality
`torusCentralizer j = SubgroupFunctor.range j` for every maximal torus
of every connected reductive group over an algebraically closed field.
Both displayed structural inputs remain hypotheses.

The implemented proof refines the imported
`AlgClosedMaximalTorusCentralizerAssembly` argument using the published
algebraically closed no-closed-torus unipotence theorem.
For a central maximal torus of `M`, the actual normal-subgroup quotient
`Q = M/T` exists and is smooth and affine. Scheme surjectivity of the
quotient gives connectedness of `Q`. The published central maximal
torus quotient theorem makes every torus homomorphism into `Q` have
trivial all-test range. In particular `Q` contains no nontrivial closed
torus, so `HasNoNontrivialClosedTorus.isUnipotent` makes it unipotent.
This application uses that `k` is algebraically closed and requires no
general arbitrary-field no-torus assertion.

The groups of points of `Q` are therefore solvable. The commutative
torus kernel and the published fppf quotient kernel comparison show
solvability of the required algebraic-closure point group of `M`.
The supplied solvable quotient statement then provides a smooth
connected normal unipotent subgroup `U` and an actual split torus
quotient `D`. Reductivity of `M` makes the full range of `U` trivial,
so the fppf quotient identifies `M` with `D`. Maximality makes the
original torus inclusion an isomorphism. The construction uses that
specific inclusion as its forward map.

For an arbitrary maximal torus `j` in a connected reductive `G`, the
published finite Galois splitting theorem makes the torus split over
the algebraically closed base. A generic cocharacter identifies its
centralizer with a dynamic centralizer. The supplied dynamic
reductivity statement makes an actual closed representative `C` of
this centralizer connected reductive. The torus factor through `C`
is central and maximal there, so the preceding result makes it an
isomorphism. Its composition with the centralizer inclusion is `j`,
and invariance of range under source isomorphism gives the claimed
equality on every test scheme, including nonreduced tests.

The provenance is internal composition and refinement of Worker 303's
published assembly and Worker 1487's imported no-cocharacter unipotence
proof. No new literature assertion is introduced. The original
assembly and all proposition targets are unchanged. This module
proves neither remaining structural input, arbitrary-field maximal
torus self-centralization, nor unconditional semisimple root or
almost-simple generation.

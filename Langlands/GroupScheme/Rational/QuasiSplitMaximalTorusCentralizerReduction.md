# Reduction to one maximal split torus with a torus centralizer

This internal supporting module isolates the remaining geometric existence input
for the published `QuasiSplitMaximalTorusCentralizerStatement.{u}`. Its provenance
is that arbitrary-field target and the existing maximal split torus
conjugacy, all-test centralizer transport, and maximal torus comparison interfaces.
It asserts no new structural existence theorem.

`QuasiSplitTorusCentralizerExistenceStatement.{u}` is a proposition definition.
For every field `k : Type u` and every `IsQuasiSplit G`, it asks for some
commutative group scheme `A` and actual map `a : A.toGrp → G` which is an
ambient maximal split torus, together with a group scheme `C` and actual map
`j : C → G` satisfying all three conditions:

- `j` represents the entire subgroup functor `torusCentralizer a`.
- `j` is a closed subgroup inclusion.
- `C` is a torus.

The torus source and the representative are existentially quantified. The
statement imposes no perfection or characteristic assumption, and retains the
published geometric quasi-split predicate. Representation includes every test
scheme and every refinement in the centralizer definition. The geometric
existence proposition is not proved in this module.

`quasiSplitMaximalTorusCentralizer_of_exists_torusCentralizer` proves the exact
published centralizer proposition under two explicit universal premises:
`QuasiSplitTorusCentralizerExistenceStatement.{u}` and
`MaximalSplitTorusConjugacyStatement.{u}`. The latter includes split-rank
independence; this reduction uses only its ordinary conjugacy component.

For the supplied `G`, the first premise gives `a₀ : A₀ → G` and a closed torus
representative `j₀ : C → G` of its centralizer. The reductivity field of
`IsQuasiSplit G` allows the second premise to conjugate `a₀` to the arbitrary
supplied maximal split torus `a : A → G`. It gives a rational point `g` and an
actual source isomorphism `e : A₀ ≅ A` with
`a₀ ≫ (G.innerIso g).hom = e.hom ≫ a`.

The published `torusCentralizer_of_iso_square` transports representation to
`j₀ ≫ (G.innerIso g).hom`. Its source remains the same torus `C`, and
`IsClosedSubgroup.comp_iso` preserves closedness. Finally the published
`IsMaximalTorus.isRepresentedBy_torusCentralizer_of_isTorus` applies to the
original supplied maximal torus inclusion `i : T → G`, its original map
`f : A → T`, and the equation `f ≫ i = a`. It proves that this actual `i`
represents the entire centralizer of `a`, as required by the target.

Both structural premises remain visible. This supporting statement and
conditional reduction leave the target and all its imports unchanged and
do not prove the unconditional theorem. The Library proves it as
`quasiSplitMaximalTorusCentralizer` (module
`Rational.QuasiSplitMaximalTorusCentralizerProof`), by this reduction.

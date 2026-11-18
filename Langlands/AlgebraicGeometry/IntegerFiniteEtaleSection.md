# Sections of finite étale covers of the integers

Worker 193.

This internal consequence of the published integer finite étale algebra
results constructs an actual section of every finite, étale, surjective
morphism `p : X → Spec (ULift ℤ)`, in every universe. It is the arithmetic
input for the proof that integer tori are split.

`Langlands.AlgebraicGeometry.IntegerFiniteEtaleSectionStatement` is the
Prop-valued statement of this section-existence assertion. The theorem
`exists_section_of_finiteEtale_integer` proves it for each supplied morphism.

`Langlands.Algebra.nonempty_intPoint_of_finiteEtale` chooses a minimal
prime of a nonzero finite étale integer algebra and applies the published
`Langlands.Algebra.minimalPrimePoint`. That map uses Mathlib's
Hermite–Minkowski consequence: the quotient by a minimal prime is the
integers. No new number-theoretic argument is introduced here.

`Langlands.AlgebraicGeometry.exists_section_of_finiteEtale_integer`
uses finiteness to make `X` affine. Surjectivity over the nonempty integer
spectrum makes its global section ring nonzero. The affine comparison
identifies the structure morphism with a finite étale algebra map.
Restriction of scalars along the lifted integer ring equivalence gives
a finite étale algebra over the ordinary integers. Its integer point
then defines a morphism from the original lifted integer spectrum to
`X`. The composite with `p` is the identity because that integer spectrum
is terminal in the category of schemes of the given universe.

The conclusion retains the original base and morphism. It does not
assert that an arbitrary étale cover has a section: finiteness is used
in the arithmetic input.

Provenance: this is a derived internal helper for the integer example
following Conrad, *Reductive group schemes* (2014), Corollary B.3.6,
p.293 (registered source `conrad-2014-reductive-group-schemes`). Its
arithmetic dependency and proof are explained in
[`IntegerFiniteEtalePicard`](../Algebra/IntegerFiniteEtalePicard.md).

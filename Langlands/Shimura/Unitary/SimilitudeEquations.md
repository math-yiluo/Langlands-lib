# The defining equations of the similitude coordinate algebra

Author: Worker 9.

This is an internal interface for the coordinate algebra already constructed in
[SimilitudeCoordinates](SimilitudeCoordinates.md). It imports that module unchanged.

`AlgebraInvolution.SimilitudePolynomialEquations b σ ψ` is a proposition for an
`R`-algebra homomorphism `ψ` from the published polynomial algebra into any
commutative `R`-algebra `S`. In the Lean namespace
`Langlands.Shimura.AlgebraInvolution`, it can also be written
`σ.SimilitudePolynomialEquations b ψ`. Put

- `g = changeCoefficients ψ (genericUnit b)` and
  `h = changeCoefficients ψ (genericUnitInv b)` in `S ⊗[R] A`;
- `c = ψ (X SimilitudeVariable.multiplier)` and
  `d = ψ (X SimilitudeVariable.multiplierInv)` in `S`.

The proposition is exactly the conjunction `g h = 1`, `h g = 1`,
`g * (σ.baseChange S) g = algebraMap S (S ⊗[R] A) c`, and `c d = 1`.
Both inverse equations
are required because `A` need not be commutative. The scalar multiplier stays
part of the data even when the algebra map to the tensor product is not injective.

The intrinsic lemma `similitudeIdeal_le_ker_iff` proves that the published
`σ.similitudeIdeal b` is contained in `RingHom.ker ψ` if and only if this
proposition holds. For the forward implication, every defining generator maps
to zero. Commutation of coordinates with coefficient change and coordinate
extensionality show that each of the three tensor expressions maps to zero;
subtraction then yields the three tensor equations. Applying `ψ` to the scalar
generator gives `c d = 1`. The reverse implication is exactly the published
`similitudeIdeal_le_ker`. Thus this lemma identifies the equations of the
existing construction; it does not replace its coordinate ring or universal point.

The base `R : Type r` is any commutative ring, the possibly noncommutative
`R`-algebra `A : Type u` has a specified basis `b` indexed by a finite type
`ι : Type v`, and the test algebra `S : Type w` is arbitrary. All four universes
are independent. The field and finite-dimensional setting follows by taking a
finite basis. No domain, nontriviality, scalar injectivity, or topology assumption
is added.

## Provenance and scope

This is a derived finite-equation coordinate construction, justified directly by
the published definitions of the ideal and the scalar-extended involution. Its
convention is `x x* = c` with an invertible scalar `c`, as recorded in the unchanged
[representability statement documentation](RepresentabilityStatement.md) for
Kottwitz (1992), Section 1, printed p.654, and Harris (1999), Section 1, printed
p.301. Those sources use rational scalars; the general commutative-base formulation
here is an internal algebraic generalization, not a further claim attributed to
the sources. The point, ideal, finite presentation and coordinate construction
remain those of `SimilitudeCoordinates`. This file adds only the specialized
equation predicate and its exact ideal-vanishing characterization.

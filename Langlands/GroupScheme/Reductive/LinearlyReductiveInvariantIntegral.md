# Normalized invariant integration for linearly reductive groups

This module constructs
`Langlands.GroupScheme.invariantIntegralOfLinearReductivity H hss :
CoordinateIntegration.InvariantIntegral H`.
Here `H` is an affine group scheme over an arbitrary field `k : Type u`.
The hypothesis `hss` says that for every natural number `m` and every
`σ : MatrixRepresentation H (Fin m)`, the supremum of the nonzero simple
`σ.IsStableSubspace` subspaces is the whole coordinate space. Stability includes
every commutative coefficient algebra and every linear coefficient functional.
No finite-type, smoothness, connectedness, reducedness or characteristic
hypothesis is imposed.

The resulting object consists of a `k`-linear functional on the coordinate
algebra, taking `1` to `1`, whose scalar extension is invariant under left
translation by every point over every commutative `k`-algebra. This is the existing
`CoordinateIntegration.InvariantIntegral` interface.

## Internal provenance and construction

This is an internal extension of the published coordinate-algebra construction
in `CharZeroInvariantIntegral`. It does not identify an additional theorem from
the literature. That module's local-to-global integral argument is reused here,
replacing its characteristic-zero fixed-dual-vector input by the given simple-span
hypothesis. Importing that module supplies generic bialgebra, antipode and
coordinate-coproduct lemmas; its characteristic-zero assumptions are not
assumptions of this construction.

In `MatrixRepresentation`, `dual_coefficient_pairing` proves that evaluation
against a fixed vector `v` is invariant on the dual: applying a coefficient
functional `ℓ` to an affine translate of a covector `c` changes its pairing with
`v` to `ℓ(1)` times the original pairing. This follows from the inverse-transpose
formula and the fact that the inverse group element fixes `v`.

`exists_dual_fixed_of_simple_span` assumes only that the dual of the particular
representation is a sum of simple subrepresentations. Evaluation at a nonzero
fixed vector is a nonzero linear functional `q`. Choose a simple dual
subrepresentation `W` not contained in `ker q`; such a `W` exists because the
supremum of the simple subrepresentations is the whole space. The intersection
`W ∩ ker q` is stable, so simplicity and the choice of `W` imply that it is zero.
For `c ∈ W` with `q(c) ≠ 0`, every linear coefficient of a translate of `c`,
minus `ℓ(1)c`, lies in this intersection. Linear functionals separate coordinate
algebra elements, so `c` is fixed at the universal affine point, and hence at all
tests. Scaling `c` gives a fixed covector pairing to one with `v`.

In `AffineLinearEmbedding`,
`exists_right_integral_of_linearReductivity` takes the finite-dimensional regular
span of a finite set of coordinates together with `1`. A basis identifies it with
an actual matrix representation of the group. The coordinates of `1` form a
nonzero fixed vector. Applying the previous lemma to the dual supplies a linear
combination of the extended coordinate functionals which is a normalized right
integral on the requested finite set.

`exists_left_integral_finset_of_linearReductivity` applies the right-integral
construction to the antipodes of the requested coordinates and then composes
with the antipode. The generic antipode identities turn this into a normalized
left integral on the finite set.
`exists_left_integral_of_linearReductivity` uses the existing uniqueness and
gluing lemma to obtain a single normalized left integral on the whole coordinate
algebra. Finally `invariantIntegralOfLinearReductivity` packages it using the
coordinate-coproduct criterion, which gives invariance over all coefficient
algebras.

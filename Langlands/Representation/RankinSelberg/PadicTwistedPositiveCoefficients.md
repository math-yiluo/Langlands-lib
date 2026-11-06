# Positive normalized coefficient pairs at a contragredient twist

This internal construction specializes the twisted conjugate-coefficient
identity to the actual residue-normalized determinant characters over a
p-adic field. The topological data `T`, the field universe and the two carrier
universes are arbitrary and independent.

`HasPadicTwistedPositiveCoefficients T π σ ψ u ℓ` is a proposition about a
specified standard Whittaker functional `ℓ` on `π`. It asserts the existence
of a real number `t` for which

`τ = realPowerTwist (T.determinantNorm (n+1)) t π`

is unitarizable, and a fixed nonzero inverse-standard Whittaker functional
`m` on `σ`. For every vector `v` of `π`, there is a vector `w` of `σ` such
that, at every actual matrix-group element `g`,

`|det(g)|^(-u) * (Wπ(ℓ,v)(g) * Wσ(m,w)(g)) = ‖ℓ(τ(g)v)‖²`.

The determinant absolute value is the published residue-cardinality-normalized
one, and the nonnegative real squared norm on the right is embedded in
the complex numbers. The same `t` and `m` work for all vectors and group
elements.

`hasPadicTwistedPositiveCoefficients_of_contragredient_twist` proves this
property when `π` is irreducible and supercuspidal, `σ` is admissible, there
is an actual equivalence

`twist (T.determinantComplexPower (n+1) (-u)) π ≃ smoothContragredient σ`,

and `ℓ` is nonzero. The proof obtains a real unitarizing twist and an
invariant positive form from `supercuspidalRealUnitarization`. Both the
complex-power character and this real-power character have open kernels and
are trivial on the upper unipotent subgroup, whose determinant is one.
Admissibility is preserved by the real-power twist. The published compact-open
cofinality result supplies the remaining topological premise of
`exists_twisted_conjugate_functional`. Its coefficient identity has an inverse
complex-power factor; multiplication by the normalized determinant weight
cancels that factor.

`HasPadicTwistedPositiveCoefficients.exists_identity_pos` shows that a
nonzero `ℓ` gives some `v,w` with strictly positive real coefficient product
at the identity, for a nonzero inverse-standard `m`. Choose `v` with
`ℓ(v) ≠ 0` and use the package's paired vector. The determinant weight and
the action of `τ` at the identity are both one, leaving `‖ℓ(v)‖² > 0`.

The provenance is the composition of the imported real unitarization,
admissibility under twisting, normalized determinant-character and
twisted-conjugate coefficient results. Existence of the initial nonzero
Whittaker functional is a supplied premise. These results are pointwise:
they make no claim about convergence, integration, a residue, or the
denominator of an L-factor.

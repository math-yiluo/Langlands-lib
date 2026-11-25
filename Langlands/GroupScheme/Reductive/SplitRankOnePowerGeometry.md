# Geometry of positive power maps on rank-one cells

This derived supporting module proves that a positive coordinate power map on the
additive line over any field is finite and surjective as a morphism of schemes.
It does not require the exponent to be a characteristic power.

The polynomial substitution `MvPolynomial.expand q` sends each variable to its
`q`th power and fixes constants. Each variable is integral over the source ring:
its `q`th power is in the image, and integrality descends from a positive power.
Polynomial induction proves integrality of every polynomial. In finitely many
variables, finite type follows by factoring the ground-ring algebra map through
the substitution; integral and finite type imply finite.

The scheme map `RootCell.gaPower q` agrees with the relative spectrum of this
substitution, as checked using its universal coordinate and naturality of the
global-sections comparison for spectra. The finite ring map gives a finite
scheme map. Injectivity of positive-power substitution and lying over give
surjectivity on scheme points. These assertions concern the actual scheme maps,
including their possibly nonreduced fibres.

At a characteristic-power exponent `p^e`, with `ExpChar k p`, the previously
proved preservation of addition and zero defines the actual group-scheme
morphism `gaPowerHom p e`. Naturality is associativity of composition.
Evaluating its points formula at the identity shows that its underlying
scheme map is exactly `gaPower (p^e)`.

For commutative group schemes `T`, `T'` over `k`, the coordinate map
`powerCell t q` is the product of `gaPower q`, the underlying map of `t`,
and `gaPower q`. Equality is checked by the three product projections.
Products of finite maps are finite, and products of surjective scheme maps
are surjective, by stability under base change and composition. Thus a
finite middle map gives `powerCell_isFinite`, and a surjective middle map
gives `powerCell_surjective`, in both cases for every positive `q`.
Surjectivity here means surjectivity on the underlying scheme points,
without asserting surjectivity on points over each test algebra.

The provenance is derived from the published vector-group coordinates and
power-cell construction, together with Mathlib's polynomial substitution,
integrality, spectrum and base-change APIs. The polynomial integrality
assertion allows any commutative coefficient ring and any type of variables
in independent universes; the finite assertion requires finitely many variables.
The group-scheme assertions allow every universe and every field.
These results do not establish isogeny geometry for the glued rank-one
homomorphism or the general split reductive isogeny theorem.

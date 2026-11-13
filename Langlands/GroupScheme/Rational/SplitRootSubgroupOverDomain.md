# Actual smooth connected root groups over a domain

This internal construction extends the existing field argument to a commutative
domain `R` in arbitrary universe `u`. Let `S` be a split torus over `Spec R`,
let `G` be an affine group scheme over `Spec R`, and let `i : S → G` be any
homomorphism. No closed immersion hypothesis on `i` is imposed.

For any character `a` of `S`, `Domain.kernelAction` is conjugation restricted
to its full scheme-theoretic kernel and reparametrized by the existing
isomorphism with `D(X*(S)/ℤa)`. The relation retains torsion, so the acting
kernel need not be smooth. The fixed-subgroup functor is exactly the existing
`kernelCentralizer i a` on all scheme tests and refinements.
`Domain.centralizer` and `Domain.centralizerHom` are the existing actual
diagonalizable fixed scheme and its closed inclusion for this action.
The resulting centralizer is affine, and is smooth if `G` is smooth. This uses
`CharacterAction.schemeFixedGroupScheme` and its proved arbitrary-ring
smoothness, including finite presentation of the actual fixed quotient.
There is no noetherian assumption.

For a nonzero character `a`, `characterFpqc_overDomain` proves that its actual
map to `Gm` is quasi-compact, flat and surjective. The proof chooses split
coordinates and uses the existing character-lattice equivalence over a domain.
It identifies the character with the diagonalizable map induced by the
injective lattice map `n ↦ n • m`, where `m` is its nonzero exponent vector.
The existing faithfully-flat group-algebra result supplies flatness and
surjectivity; the affine coordinate map supplies quasi-compactness. The
pointwise comparison follows the published field proof, using identities that
are already valid over domains.

If `G` is smooth, the final theorem constructs an actual group scheme `U` and
map `j : U → G` representing the existing root subgroup functor `subgroup i a`
on every scheme test. The map is a closed immersion, and `U` is affine and
smooth with geometrically connected fibres. It applies `RootSubgroupOverRing`
to the constructed centralizer and the fpqc character. Its identity-limit
construction uses the actual descended action; no representative, centralizer,
quotient action or connectedness theorem is a new hypothesis.

The provenance is internal: the construction composes the published kernel
isomorphism, arbitrary-ring diagonalizable fixed-scheme construction,
character-lattice and group-algebra results, and the ring-level root construction.
It supplies a relative root scheme once an integral split torus and ambient
smooth affine group are available. It does not construct that integral torus,
identify the root scheme's generic fibre, prove a valuation-filtration point
comparison, or prove the parahoric-model existence theorem.

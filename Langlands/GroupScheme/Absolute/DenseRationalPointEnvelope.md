# Dense rational points in a subgroup envelope

This internal API constructs the schematic envelope of a rational subgroup over
an arbitrary field. It is derived from the published `RationalPointClosure`
quotient construction and Mathlib's formula for the closure of a subset of a
prime spectrum. It adds the dense lifted subgroup needed for the abstract-group
semisimplicity reduction. It does not assume characteristic zero or algebraic
closedness.

## Corepresented construction

For a group-valued algebra functor `F` corepresented by `B`, and a subgroup
`Gamma` of `F(k)`, `envelope e Gamma` is the published cut group scheme for the
ideal of elements of `B` vanishing on every element of `Gamma`.
`subgroupToCut`, `affineLift`, and `rationalLift` are group homomorphisms
lifting the original subgroup to that cut functor, to its affine test points,
and to its actual rational points, respectively. The last step uses the
canonical isomorphism between the relative spectrum of the ground field and
the base test scheme.

`affineLift_eq` and `rationalLift_eq` identify these points with spectra of
the quotient evaluations. `affineLift_factor` proves that the cut inclusion
returns the original point under the corepresentation equivalence.

`dense_family_of_separating` proves that any family of evaluations `B -> k`
that separates elements has dense union of point images in `Spec B`. The
index type has an arbitrary universe. Its proof shows that the vanishing
ideal of the classified prime points is zero, applies the prime-spectrum
closure formula, and observes that each classified point lies in its
rational point's image. Evaluations by the original subgroup separate the
quotient by its vanishing ideal, so `dense_rationalLift` follows.

The envelope is affine. Its coordinate ring is reduced by the published
`isReduced_quotient` theorem. If the original corepresented group is locally
of finite type, so is its envelope, since the inclusion is a closed immersion.

## Actual group schemes

`exists_dense_envelope` takes an affine group scheme `G` locally of finite
type over a field and a subgroup `Delta` of its actual rational point group.
It returns a group scheme `H` with:

- reduced underlying scheme, affine structure morphism, and locally finite
  type structure morphism;
- a group-scheme homomorphism `i : H -> G`;
- a homomorphism `alpha : Delta -> H(k)` whose point images have dense union;
- the equality `alpha gamma` followed by `i` equals the original point
  `gamma` of `G`.

The proof chooses an affine coordinate model of `G`, transports `Delta` to
its affine-point functor, and applies the corepresented construction. The
transport to the image subgroup is surjective, so composing the dense lift
with it preserves density. The final factorization is the corepresentation
factorization transported back along the chosen model isomorphism.

This file supplies a prerequisite API, not the characteristic-zero tensor
semisimplicity theorem. It is implementation-derived content: its proofs use
the existing Library quotient and affine-corepresentation APIs rather than a
new translation of an original source statement.

The identity-test comparison uses `PointTopology.ringTestSelfIso` for the ground field.

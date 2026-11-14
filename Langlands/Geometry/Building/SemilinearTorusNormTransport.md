# Torus norms in a square of coefficient field isomorphisms

This module constructs transport between the rational-point sources of two
norm maps and proves that coefficient extension preserves their bounded norm
images. It is a derived helper for Galois transport of zero subgroups.

The fields `k`, `K`, `L`, and `M` lie in the same arbitrary universe. The
algebra structures form two scalar towers `k → K → M` and `k → L → M`.
The horizontal maps are `k → K` and `L → M`. No splitting hypothesis on the
group is used: `T` is any affine commutative group scheme over `k`.

## Constructions

For a tower `k → L → M`, `commTowerRationalEquiv` identifies points of the
iterated base change of `T` with points of its direct base change to `M`.
It first passes from rational points to coefficient points, removes the
intermediate base change, and returns to rational points. The theorem
`commTowerRationalEquiv_apply` identifies this equivalence with the point map
of the existing `towerBaseChangeIso`.

The homomorphism `squareRationalExtend` first extends points of `T_L`
from `L` to `M`, then uses the two tower equivalences to obtain points of
`(T_K)_M`. These constructions require only the fields, algebra structures,
and the two scalar-tower compatibilities.

## Norm comparison

`rationalNorm_iso_square` assumes that all five field extensions
`k → K`, `k → L`, `k → M`, `K → M`, and `L → M` are finite dimensional
and Galois. It also assumes that `k → K` is surjective and that
`Module.finrank L M = 1`. For every point `x` of `T_L`, it proves

```text
N_(M/K)(squareRationalExtend(x)) = extend_(K/k)(N_(L/k)(x)).
```

The proof first shows that the norm for a surjective field map is injective:
its automorphism group is trivial, so extension after norm is the identity.
Norm after extension is also the identity for an extension of dimension one.
The existing transitivity theorem identifies both tower norms with `N_(M/k)`.
Applying the injective `N_(K/k)` reduces the displayed identity to those two
transitivity identities and the dimension-one identities.

The existing `GaloisPointComparison.rationalExtend_hom_eq_baseChangeSectionHom`
from [RingEquivBaseChange](../../GroupScheme/Rational/RingEquivBaseChange.md)
identifies coefficient extension with the scheme section map. Consumers use
its symmetric equality when the section map is on the left.

## Bounded norm images

Let `vL` and `vM` be valuations in arbitrary linearly ordered commutative
groups with zero. In addition to the norm-comparison hypotheses, assume
`vL.HasExtension vM` and that `vM` is invariant under `Aut_L(M)`.
Then `map_torusNormIwahori_le_iso_square` proves

```text
map extend_(K/k) (torusNormIwahori k L vL T)
  ≤ torusNormIwahori K M vM T_K.
```

The finite Galois character-valuation extension theorem carries a point of
the `vL` character kernel into the `vM` character kernel. Both tower
comparisons preserve that kernel because they come from group-scheme
isomorphisms. The norm identity then carries its norm into the target
bounded norm image. This proves an inclusion; this module asserts no
converse inclusion under the displayed hypotheses.

## Provenance and scope

These are derived constructions from the published Library definitions of
rational-point norms, their tower-transitivity proofs, functoriality of
character-valuation kernels, and their finite Galois extension theorem.
The module does not introduce a replacement norm or bounded subgroup. It
is not a proof of the full `UnramifiedZeroDescentStatement`: constructing
the Galois-conjugated datum and comparing its ambient subgroup remain
separate obligations.

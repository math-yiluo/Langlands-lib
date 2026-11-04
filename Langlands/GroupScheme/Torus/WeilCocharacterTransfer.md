# Transfer of a cocharacter through a finite Galois extension

This is an internal construction for affine commutative group schemes. Let `k`
and `K` be fields in an arbitrary common universe, with a `k`-algebra structure
on `K`, and let `Z` be a commutative group scheme over `k`. Write `Z_K` for the
actual scheme base change. A cocharacter in this file is an actual group-scheme
homomorphism `nu : Gm_K ⟶ Z_K`.

For a commutative `K`-algebra `A`, with its compatible `k`-algebra structure,
`cocharacterValue` sends a unit to its `Gm_K` point, composes with `nu`, and
applies `Lie.affineBaseChangeEquiv` to obtain an actual `Z(A)` point.
`cocharacterValue_naturality` proves compatibility with every `K`-algebra map.
These two declarations require neither finiteness of `K/k` nor affineness of `Z`.

For the remaining declarations, assume `K/k` is finite dimensional and Galois,
and that `Z` is affine. On every commutative `k`-algebra `A`, `transferPoint` is
the group homomorphism

```
(K tensor_k A)^units -> Z(K tensor_k A) -> Z(A).
```

The first map is `cocharacterValue` and the second is the conjugate-product norm
`TensorGaloisPoint.norm`. There is no reducedness, nontriviality, smoothness,
finite type or field assumption on the test algebra `A`.
`transferPoint_naturality` combines the two component naturality identities.
`transferNat` assembles these maps into a natural transformation from the
Weil-restriction point functor to `AffineCoordinates.functor Z.toGrp`.

`cocharacterTransfer` reconstructs the actual group-scheme homomorphism
`Res_{K/k}(Gm) ⟶ Z` through the existing affine corepresentation, then composes
with its comparison isomorphism to `Z`. The theorem
`cocharacterTransfer_affinePoints` identifies its action on every actual affine
point with `transferPoint`, using the standard unit-valued point equivalence
for the Weil restriction.

The proofs use the published `Gm` point equivalence, its naturality, the actual
scheme-pullback point equivalence, the tensor norm, and the affine Yoneda
reconstruction interface. This is derived infrastructure, with no external
literature assertion being translated. No no-torus or unipotence theorem enters
the construction. This file makes no nonvanishing or descent assertion for the
transfer; those require an additional argument.

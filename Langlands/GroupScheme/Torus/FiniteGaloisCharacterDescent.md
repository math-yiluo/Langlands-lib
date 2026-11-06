# Finite Galois descent of equivariant character maps

Author: Worker 1548.

This is internal supporting infrastructure for the induced-torus Weil
decomposition proof. Its provenance is a derivation from the published
canonical Čech descent, finite Galois tensor decomposition, split-torus
character reconstruction and fpqc isomorphism reflection APIs. It does not
assert the induced-torus classification or a permutation-basis construction.

All fields and schemes lie in arbitrary universe `u`. The final descent
theorems use fields `k` and `L`, an algebra structure `k → L`, and
`[FiniteDimensional k L] [IsGalois k L]`. They hold in every characteristic
and impose no positive-rank condition.

## Construction and compatibility

`galoisHomTransport σ f` conjugates an actual homomorphism between two
base-changed commutative groups by their canonical Galois descent
isomorphisms. For `a = Spec σ` and canonical transports `d_T : a* T_L ≅ T_L`,
its formula is

```text
galoisHomTransport σ f = d_T.inv ≫ a*(f) ≫ d_T'.hom.
```

`galoisHomTransport_comp` states that its composition with the transported
character `σ χ` is `σ(f ≫ χ)`. The proof unfolds transport of characters,
uses functoriality of base change and cancels the adjacent canonical
isomorphism and its inverse.

`galoisHomTransport_eq` shows that equivariance of character pullback implies
`galoisHomTransport σ f = f` when the target is split over `L`. Characters
separate homomorphisms into that target, and the Galois operator on its
character lattice is surjective, because it belongs to a group
representation. The source need not be split.

`Descent.compatible_of_galois` tests canonical descent compatibility of a
homomorphism on the finite Galois components of the double overlap. On each
component, the first projection is the identity and the second is a Galois
automorphism. `Descent.pullIso_canonicalOverlap_eq` identifies the pulled-back
canonical overlap with the identity-pullback comparison followed by inverse
canonical Galois transport. Naturality of the identity comparison reduces
the local compatibility equation to the assumed Galois commutation.
`FiniteComponents.groupHom_ext` then gives the full overlap equation.

`compatible_of_equivariant_characterPullback` combines these arguments to
deduce canonical descent compatibility for an actual homomorphism from
equivariance of its character pullback.

## Reconstruction and isomorphisms

`IsSplitTorus.existsUnique_hom_of_equivariant_characterMap` has source an
arbitrary actual commutative group scheme `T` over `k`, and target `T'`
split over `L`. Given an additive map

```text
F : X*(T'_L) →+ X*(T_L)
```

commuting with the actual Galois representations, it produces a unique
`a : T ⟶ T'` such that

```text
(baseChange k L).map a ≫ χ = F χ
```

for every actual character `χ` of `T'_L`. The published split-torus
`homOfCharacterMap` first reconstructs `f : T_L ⟶ T'_L`. Its pullback is
`F`, hence is equivariant, so the previous compatibility lemma applies.
`Descent.FpqcHomDescent.hom` descends `f`, since a field extension is fpqc.
Its recovery equation proves the asserted character identity. Uniqueness
first uses separation by target characters over `L`, then uniqueness of
fpqc homomorphism descent.

`IsSplitTorus.exists_iso_of_equivariant_characterEquiv` assumes both `T_L`
and `T'_L` split, and starts from an equivariant additive equivalence
`X*(T'_L) ≃+ X*(T_L)`. The preceding theorem produces a ground-field
homomorphism. Its pullback on characters over `L` is bijective, so
`isoOfBijectiveCharacterPullback` makes its base change an actual
isomorphism. `isIso_of_baseChange` reflects this isomorphism along the fpqc
field extension. The result is an isomorphism `T ≅ T'` with exactly the
prescribed character pullback over `L`.

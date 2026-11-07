# Actual rational-point comparison for affine Weil restriction

For fields `F`, `E : Type u` with an algebra structure and
`FiniteDimensional F E`, and an actual affine group scheme `G/E` locally of
finite type, `AffineWeil.rationalPointsEquiv F E G` is a multiplicative
equivalence

```text
(Res(E/F) G)(F) ≃* G(E).
```

The restriction is the existing actual `AffineWeil.groupScheme F E G`,
and both point groups are the Library's actual `rationalPoints` groups.
No topology, local-field assumption, separability or Galois hypothesis is
required. The finite-dimensional field extension provides the finite
projective algebra needed by the existing affine restriction.

The construction composes the existing
`GaloisPointComparison.rationalCoeffEquiv` over `F`, the existing
`AffineWeil.basePointsEquiv`, and the inverse rational/coefficient comparison
over `E`. The middle equivalence is the actual restriction point comparison
followed by the tensor-unit coefficient isomorphism `E ⊗[F] F ≃ₐ[E] E`.

The theorem `basePointsEquiv_map` proves that this middle comparison commutes
with any actual homomorphism `f : G ⟶ H` between affine group schemes locally
of finite type over `E`. It first applies the existing
`AffineWeil.map_affinePoints`, then uses naturality of the original actual
point map under the tensor-unit coefficient change.

The theorem `rationalPointsEquiv_map` combines this with the existing
rational/coefficient naturality. Consequently the equivalence identifies
the rational-point homomorphism of `AffineWeil.map F E f` with the original
rational-point homomorphism of `f`. This is a comparison of the actual
restricted morphism and its actual section map.

The provenance is internal composition of the existing restriction and
coefficient comparisons. This unit supplies no statement about restriction
of parabolics, geometric unipotent radicals or dynamic subgroups, and proves
no Kneser–Tits theorem.

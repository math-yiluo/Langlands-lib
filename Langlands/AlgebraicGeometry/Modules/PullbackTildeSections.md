# Canonical sections of an actual associated-sheaf pullback

Let `R` be a commutative ring, let `C` be any `R`-module, and let
`p : X ⟶ Spec R` be any scheme morphism. This internal module supplies canonical
global generators and affine tensor comparisons for the actual pulled-back
module sheaf `p*(tilde C)`. There is no finite-projective, flatness,
compactness or noetherian hypothesis.

`pullbackTildeGlobalSections p C` is an actual `R`-linear map from `C` to the
relative global section module of the actual pullback. It composes the
standard associated-sheaf global-section isomorphism `tilde.isoTop` with
`moduleSpecΓFunctor` applied to the actual pullback adjunction unit. Its
underlying value is therefore precisely the actual pullback of the global
associated-sheaf section defined by `c`. The theorem
`pullbackTildeGlobalSections_restrict` computes its restriction to any open
as `sectionPullbackLE` of the original associated-sheaf generator.

For an actual affine open `U` of `X`, the definition
`pullbackTildeSectionsEquiv p C U` is a `Γ(X,U)`-linear equivalence

```text
Γ(X,U) ⊗[R] C ≃ Γ(p*(tilde C), U).
```

The base algebra on `Γ(X,U)` is the existing `algebraOfHom p U` induced by
`p`. To construct this equivalence, `pullbackTildeScalarIso` first compares
scalar extension directly from `R` with extension from the actual global
section ring of `Spec R`. It uses `tilde.isoTop`, scalar-extension
composition and the scalar-extension/restriction counit for the inverse
`ΓSpecIso` ring isomorphism. The existing canonical affine pullback tensor
map is bijective because the associated sheaf is quasi-coherent. Its
isomorphism then completes the comparison with actual sections.

The scalar-extension unit and counit generator formulas prove
`pullbackTildeScalarIso_one_tmul`. The canonical affine pullback tensor map
therefore gives `pullbackTildeSectionsEquiv_one_tmul`: `1 ⊗ c` maps to the
restriction of the stated canonical actual global generator. Linearity
gives `pullbackTildeSectionsEquiv_tmul` for arbitrary `a ⊗ c`.

`pullbackTildeSectionsEquiv_restrict` proves compatibility for every tensor
with restriction from one affine open to a smaller affine open. On the
coefficient side it uses the existing actual section restriction algebra
homomorphism. Tensor induction, the pure-tensor formula, semilinearity of
module-sheaf restrictions and composition of restrictions prove the
identity.

The provenance is internal: the construction packages the existing actual
pullback unit, associated-sheaf global sections, scalar extension and
canonical affine pullback tensor comparison while retaining their
specified generators. It contains no group orbit, Grassmannian
classification or kernel identification.

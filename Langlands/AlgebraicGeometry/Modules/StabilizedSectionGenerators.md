# Actual stabilized global generators and affine tensor maps

Let `p : X ⟶ Spec R` be any scheme morphism, `M` an actual module sheaf on
`X`, and `C` any `R`-module. Supply an actual `R`-linear family
`q : E →ₗ[R] (relativeGlobalSections p).obj M`. This module combines it with
the canonical global family of the actual pulled-back associated sheaf
`p*(tilde C)` in the genuine categorical biproduct

```text
M ⊞ (Scheme.Modules.pullback p).obj (tilde C).
```

`globalFamilyRestriction` restricts the supplied global family to any open,
using the canonical `R`-action through `algebraOfHom p U` on its actual
section module. Its linearity follows from the given global linearity,
semilinearity of actual sheaf restrictions and the actual base section
maps. `globalFamilyTensorMap` extends it to a `Γ(X,U)`-linear map from
`Γ(X,U) ⊗[R] E`. Its pure-tensor formula is exactly
`a ⊗ e ↦ a • restriction (q e)`. Tensor induction gives compatibility
with restriction for every tensor.

`stabilizedGlobalGenerator` is the actual `R`-linear family from `E × C`
into the relative global sections of the genuine biproduct. It uses the
actual biproduct inclusions applied through `relativeGlobalSections p`,
adding the image of `q` on the first factor to the canonical pulled-back
associated-sheaf global generator on the second. The theorem
`stabilizedGlobalGenerator_product` proves that the actual biproduct
section projections recover precisely the two prescribed global families.

`stabilizedTensorMap` is the coefficient tensor extension of this actual
combined global family over every affine open. Its pure-tensor formula
retains that global family. The theorem `stabilizedTensorMap_product`
computes it on every tensor: after the standard tensor/product linear
equivalence and the actual biproduct section equivalence, it is the pair
of the original `globalFamilyTensorMap` and the canonical complement
`pullbackTildeSectionsEquiv`. Tensor induction proves this identity;
its pure-tensor step uses actual section restriction compatibility,
biproduct projection identities and the canonical complement generator
formula. `stabilizedTensorMap_restrict` gives compatibility with actual
affine-open restrictions for every tensor.

The provenance is internal: the actual global section functor, genuine
biproduct inclusion/projection identities, canonical pulled-back base
module generators and ordinary coefficient tensor extension supply the
whole construction. No finiteness, projectivity, flatness or
quasi-coherence assumption on `M` or `E` is needed. This module makes no
orbit, Grassmannian classified-kernel or parabolic positivity assertion.
For an identity-jet application its genuine biproduct is definitionally
the actual `IdentityJet.stabilizedModule` with `M = IdentityJet.module G n`
and base sheaf `tilde C`.

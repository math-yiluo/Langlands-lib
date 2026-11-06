# Pullback preserves finite affine sections

This internal helper defines
`Langlands.AlgebraicGeometry.Modules.AffineSections.pullbackEquiv`, the canonical
linear equivalence from the scalar extension
`Γ(X, U) ⊗_{Γ(Y, V)} Γ(M, V)` to the actual sections `Γ(f^*M, U)`.
Here `M` is quasi-coherent, both opens are affine, and `U ⊆ f⁻¹(V)`.
The equivalence is constructed from the published bijectivity of the canonical
pullback tensor map.

It then proves
`Langlands.AlgebraicGeometry.Modules.HasFiniteAffineSections.pullbackObj`.
For any morphism of schemes `f : X ⟶ Y` and quasi-coherent module sheaf `M` on
`Y`, finite generation of `Γ(M, V)` over `Γ(Y, V)` on every affine open `V`
implies the same property for the actual module pullback `f^*M` on `X`.
The schemes share an arbitrary universe. No noetherianity, properness, flatness,
or finite generation condition on the morphism is needed.

The proof first obtains local finite sections. At each point `x` of `X`, it
chooses an affine neighborhood `V` of `f(x)` and then an affine neighborhood `U`
of `x` contained in `f⁻¹(V)`. The published affine pullback comparison identifies
the actual sections of `f^*M` over `U` with the scalar extension
`Γ(X, U) ⊗_{Γ(Y, V)} Γ(M, V)`. Finite generation is preserved by scalar
extension and passes through this linear equivalence, giving finite sections
on `U`. Pullback preserves quasi-coherence, so the published local
finiteness criterion upgrades these neighborhoods to finite sections on every
affine open of `X`.

The provenance is internal: the result combines `pullbackTensorMap_bijective`
from `PullbackAffineSections`, `HasLocallyFiniteSections.finiteAffineSections`
from `CoherentLineBundle`, the pullback quasi-coherence instance, and Mathlib's
finite-module scalar-extension and linear-equivalence results. It supplies a finiteness
input for the proper adic cohomology argument; it does not prove the uniform
boundary-lifting bound or the stable-image theorem.

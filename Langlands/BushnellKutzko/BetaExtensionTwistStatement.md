# Intertwining of `κ ⊗ ξ` (V3)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), Proposition (5.3.2), printed p. 176 (PDF p. 188). This is statement V3 of Task 7427.

`BetaExtensionTwistStatement` quantifies, as in V1 and V2, over `F`, `V` (independent universes), `ψF` with `IsBKAdditiveCharacter`, a simple stratum `S = [𝔄, n, 0, β]` with `S.r = 0`, `S.IsSimple`, a defining-sequence choice `q`, `θ ∈ C(𝔄, 0, β)`, a representation `η` of `J^1` lying over `θ`, a `β`-extension `κ` of `η`, and a finite-dimensional irreducible representation `ξ` of `J = J(β, 𝔄)` that is trivial on `J^1`. BK93 takes `ξ` to be the inflation to `J` of an irreducible representation of `J/J^1 = U(𝔅_β)/U^1(𝔅_β)`; a representation of `J` trivial on `J^1` is exactly such an inflation. Carriers are in arbitrary universes. It asserts:

- (i) `I_G(κ ⊗ ξ) = J · I_{B^×}(ξ | U(𝔅_β)) · J`: `representationSelfIntertwining (κ.tprod ξ)` is the pointwise product of `J`, the set of `y ∈ B_β^× = centralizerUnitGroup S.b` that intertwine the restriction of `ξ` to `U(𝔅_β) = relativeUnitFiltration S.chain S.b 0`, and `J`.
- (ii) for every `y ∈ B_β^×`, the intertwining spaces `I_y(κ ⊗ ξ)` and `I_y(ξ)` (`intertwiningSpace`, definition 1) have the same `ℂ`-dimension (`Module.finrank`).
- (iii) `κ ⊗ ξ` is irreducible.

The intertwining spaces use the direction of definition 1 (`Hom(ρ^y, ρ)` on `y⁻¹Jy ∩ J`); BK93 (5.1.7) uses `Hom(ρ, ρ^y)`. For the smooth finite-dimensional representations here, both directions give spaces of the same dimension and the same intertwining sets, by complete reducibility over the compact group `y⁻¹Jy ∩ J`. This is the proposition only; its proof is a separate task.

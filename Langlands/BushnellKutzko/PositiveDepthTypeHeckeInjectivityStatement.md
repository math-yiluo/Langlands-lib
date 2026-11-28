# Injectivity of the Hecke operators of a simple type of kind (a)

The module `Langlands.BushnellKutzko.PositiveDepthTypeHeckeInjectivityStatement` defines a
normalized Hecke operator on spaces of intertwiners and states that, for a simple type of
kind (a), the Hecke operators attached to elements of `B_β^×` and nonzero intertwiners are
injective.

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln` (SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`; PDF page = printed page
+ 12): Main Theorem (5.6.6), printed p. 190, with (5.4.6)(ii) and (5.4.8)–(5.4.9),
printed pp. 179–180, (5.5.11), printed p. 185, (5.5.17), printed p. 187, and the Hecke
algebra formalism of §4.1, printed pp. 143–144 (the anti-isomorphism `H(G, ρ̌) → H(G, ρ)` and
(4.1.1)–(4.1.2)), and (4.2.4), printed p. 148.

## `typeHeckeMean`

For a group `G`, a subgroup `J`, a representation `ρ` of `J` on `W`, a representation `π` of
`G` on `V`, an element `x ∈ G`, a linear map `Θ : W → W` and a linear map `Φ : W → V`,

```lean
typeHeckeMean ρ π x Θ Φ =
  Compact.orbitMean (Representation.linHom ρ (π.comp J.subtype)) (π x ∘ₗ Φ ∘ₗ Θ)
```

is the mean of the orbit of `π(x) ∘ Φ ∘ Θ` under the action `j ↦ π(j) ∘ (-) ∘ ρ(j)⁻¹` of `J`
on `W →ₗ[ℂ] V` (`Compact.orbitMean` is the normalized sum over the distinct elements of the
orbit).

Mathematical meaning. Let `J` be compact open, `ρ` smooth and finite-dimensional, `π` smooth,
`Φ ∈ Hom_J(ρ, π)` and `Θ ∈ I_x(ρ)`, the Library's intertwining space
`intertwiningSpace ρ ρ x`: `Θ ∘ ρ(x h x⁻¹) = ρ(h) ∘ Θ` for `h ∈ x⁻¹Jx ∩ J`. Then
`π(x) ∘ Φ ∘ Θ` is fixed by `J ∩ xJx⁻¹`, its orbit is finite, and its mean is
`[J : J ∩ xJx⁻¹]⁻¹ Σ_{j ∈ J/(J ∩ xJx⁻¹)} π(j) ∘ π(x) ∘ Φ ∘ Θ ∘ ρ(j)⁻¹`: the map
`j ↦ π(j) ∘ π(x) ∘ Φ ∘ Θ ∘ ρ(j)⁻¹` factors through `J/(J ∩ xJx⁻¹)`, and its fibres over the
points of the orbit all have the same size.

This is, up to a positive factor, the action of an element of the Hecke algebra of BK93
(4.1), printed pp. 143–144, whose conventions are as follows. The compactly supported
functions `F : G → End_ℂ(W)` with `F(k₁ g k₂) = ρ(k₁) ∘ F(g) ∘ ρ(k₂)` form the algebra
`H(G, ρ̌)` of the book (the algebra `H(G, ρ)` used in (4.2.4) and (5.6.6) consists of
`End_ℂ(W̌)`-valued functions), and `F ↦ F̌`, `F̌(g) = F(g⁻¹)^∨` (transpose), is an
anti-isomorphism `H(G, ρ̌) → H(G, ρ)` (printed p. 143). By (4.1.1), printed p. 144, at the
element `x⁻¹`, the space `I_x(ρ)` (homomorphisms from the conjugate `h ↦ ρ(x h x⁻¹)` of `ρ` to
`ρ` on `x⁻¹Jx ∩ J`) corresponds to the functions of `H(G, ρ̌)` supported on `J x⁻¹ J`: `Θ` is
the value at `x⁻¹` of a unique such `F`, with `F(k₁ x⁻¹ k₂) = ρ(k₁) ∘ Θ ∘ ρ(k₂)`. Its image
`K = F̌ ∈ H(G, ρ)` is supported on `JxJ` and has `K(x) = Θ^∨`. In the dual-space convention of
(4.2.4), printed p. 148, `K` acts on `Hom_J(ρ, π) = Hom_G(c-Ind_J^G ρ, π)` by
`Φ ↦ ∫_G π(g) ∘ Φ ∘ K(g)^∨ dg = ∫_G π(g) ∘ Φ ∘ F(g⁻¹) dg`. For `g = j x j'` with `j, j' ∈ J`
the integrand is `π(j) ∘ π(x) ∘ Φ ∘ Θ ∘ ρ(j)⁻¹`, so with `vol(J) = 1` the integral is the sum
displayed above without the factor `[J : J ∩ xJx⁻¹]⁻¹`. Hence `typeHeckeMean ρ π x Θ` is the
action of `K` divided by `[J : J ∩ xJx⁻¹]`, and this positive factor does not affect
injectivity.

## `PositiveDepthTypeHeckeInjectivityStatement`

For every nonarchimedean local field `F`, `n > 0`, `ψF : AddChar F ℂ`, every subgroup `J` of
`GL_n(F)` and smooth representation `ρ` of `J` exhibited as a simple type of kind (a) by
`IsSimpleTypeData ψF S q e (glRepresentationToAut ρ)` (BK93 (5.5.10)(a)), every
`x ∈ GL_n(F)` whose image under `Matrix.GeneralLinearGroup.toLin` lies in
`B_β^× = centralizerUnitGroup S.b`, every nonzero `Θ ∈ intertwiningSpace ρ ρ x`, every
smooth complex representation `π` of `GL_n(F)` and every `Φ ∈ Hom_J(ρ, π)`:
if `typeHeckeMean ρ π x Θ Φ = 0` then `Φ = 0`. The universes of the field, of the carrier of
`ρ` and of the carrier of `π` are independent.

## Relation to the source

Let `(J, λ)` be a simple type of kind (a) with centralizer order `𝔅` of period `e`. BK93
(5.6.6) gives an algebra isomorphism `Ψ : H(e, q_E^f) → H(G, λ)` such that, for `w` in the
group `W(𝔅)` of (5.5.9), `Ψ[w]` has support `JwJ`; the double cosets `JwJ` for distinct `w`
are distinct (5.5.17), and by (5.5.11) every element intertwining `λ` lies in `J W(𝔅) J`.
Hence every function of `H(G, λ)` supported on one double coset `JyJ` with `I_y(λ) ≠ 0` is a
scalar multiple of some `Ψ[w]`. The standard basis elements `[w]` of the affine Hecke algebra
are invertible ((5.4.6)(ii), (5.4.8)–(5.4.9)), so every nonzero function of `H(G, λ)`
supported on a single double coset in the support is invertible, and it acts bijectively on
`Hom_J(λ, π)` for every smooth `π`. For nonzero `Θ ∈ I_x(λ)` the function `K = F̌` above is
such a function, supported on `JxJ` with `K(x) = Θ^∨ ≠ 0`; the anti-isomorphism `F ↦ F̌`
carries invertibility between `H(G, λ̌)` and `H(G, λ)`. The proposition records the
injectivity of the action of `K`, expressed through `typeHeckeMean`, for the elements
`x ∈ B_β^×`: those are the elements used
in BK93 (7.3.1), printed p. 222, and in its proof (7.4.1)–(7.4.2), printed pp. 231–232, where
`x` runs through the diagonal group `D(𝔅)`.

The module states the proposition and does not prove it.

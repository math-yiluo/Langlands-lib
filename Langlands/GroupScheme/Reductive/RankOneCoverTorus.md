# The torus isogeny `𝔾ₘ × C ⟶ T` attached to a root and a coroot

Module `Langlands.GroupScheme.Reductive.RankOneCoverTorus`, namespace
`Langlands.GroupScheme.RankOneCoverTorus`. This is an internal supporting module for the
rank-one central cover (`Langlands.GroupScheme.RankOneCentralCoverStatement`).
It builds the torus part of the cover: a split torus `C` and an isogeny
`t : 𝔾ₘ × C ⟶ T` that matches the root and coroot of `SL₂ × C`
(`SpecialLinearTensorCell.χ₀`, `SpecialLinearTensorCell.χv₀`) with a given root `α` and
coroot `αv` of `T`. This is standard lattice algebra: `X_*(T)` contains
`ℤ αv ⊕ ker ⟨α, -⟩` with finite index when `⟨α, αv⟩ = 2`. The module proves it directly,
with no literature source.

## Statements

Throughout, `k` is a field and `T : CommGroupScheme (Spec (CommRingCat.of k))`.

- `exists_cocharacterBasis (hT : IsSplitTorus T.toGrp)`: the cocharacter lattice
  `cocharacterLattice T` has a finite `ℤ`-basis. It is transported from
  `splitTorus.cocharacterLatticeEquiv k I : X_*(𝔾ₘ^I) ≃+ (I → ℤ)` along an isomorphism
  `T ≅ 𝔾ₘ^I`.
- `character_eq_zero (hT) (ψ) (h : ∀ ν, ν ≫ ψ = 0) : ψ = 0`: a character of a split torus
  that vanishes on every cocharacter is zero. Pull `ψ` back to `𝔾ₘ^I`. Its coordinates
  under `splitTorus.characterLatticeEquiv` are the values on the coordinate cocharacters,
  so they are all zero.
- `exists_torusIsogeny (hT : IsSplitTorus T.toGrp) (α : characterLattice T)
  (αv : cocharacterLattice T) (h2 : latticePairing T α αv = 2)`: there exist
  `C : CommGroupScheme (Spec (CommRingCat.of k))` with `IsSplitTorus C.toGrp`, and
  `t : CommGroupScheme.prod (Dt k) C ⟶ T`, such that
  - `IsIsogeny (CommGroupScheme.groupHom t)`,
  - `t ≫ α = χ₀ C`, so `α` pulls back to the character `(τ, c) ↦ τ²`,
  - `χv₀ C ≫ t = αv`, so `s ↦ (s, 1)` maps to `αv`.

  Here `Dt k` is the one-dimensional split torus
  `splitTorus.commGroupScheme _ (ULift (Fin 1))`.

## The implemented proof of `exists_torusIsogeny`

Let `K = ker (latticePairing T α) ⊆ X_*(T)`. A basis of `X_*(T)` and
`Submodule.basisOfPid` give a basis `κ_1, …, κ_n` of `K`. Put
`C = splitTorus.commGroupScheme _ (ULift (Fin n))` and define `t` on the cocharacter side:

`t = prodFst ≫ proj ⟨0⟩ ≫ αv + prodSnd ≫ ∑ⱼ proj j ≫ κ_j`,

that is `t(τ, c) = αv(τ) · ∏ⱼ κ_j(c_j)`.

1. **Root.** `αv ≫ α = 2 • 𝟙` because `⟨α, αv⟩ = 2`, and `κ_j ≫ α = 0` because `κ_j ∈ K`.
   Both use `eq_gmEndEquiv_zsmul` and `latticePairing_apply`. Hence
   `t ≫ α = prodFst ≫ 2 • proj ⟨0⟩ = χ₀ C`.
2. **Coroot.** `prodInl ≫ t = proj ⟨0⟩ ≫ αv` by `prodInl_fst` and `prodInl_snd`. With
   `single_comp_proj` this gives `χv₀ C ≫ t = αv`.
3. **Isogeny.** This applies the Library theorem `splitTorusIsogenyOfLatticeMaps`. It needs
   injectivity of pullback of characters along `t` and of pushforward of cocharacters
   along `t`. The product `𝔾ₘ × C` is split by `IsSplitTorus.tensor`.
   - *Characters.* Suppose `t ≫ ψ = 0`. Then `⟨ψ, αv⟩ = 0` (compose with `χv₀`) and
     `⟨ψ, κ_j⟩ = 0` (compose with `single j ≫ prodInr`, which `t` sends to `κ_j`). So
     `⟨ψ, -⟩` vanishes on `K`. For every cocharacter `ν`, the element
     `2ν − ⟨α, ν⟩ αv` lies in `K`. Hence `2⟨ψ, ν⟩ = 0`, so `⟨ψ, ν⟩ = 0`. Then
     `character_eq_zero` gives `ψ = 0`.
   - *Cocharacters.* Write the coordinates of `ν : 𝔾ₘ ⟶ 𝔾ₘ × C` as integers `a` and `c_j`.
     Then `ν ≫ t = a • αv + ∑ c_j • κ_j`. If this is zero, composing with `α` gives
     `2a = 0`. Linear independence of the basis `κ` then gives `c_j = 0`. Both components
     of `ν` vanish (`splitTorus.cocharacterLatticeEquiv` is injective), so `ν = 0` by
     `prod_decomposition`.

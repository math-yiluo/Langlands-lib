# Unit sections of the cocycle subsheaf are local frames

This helper module supports the proof of
`Langlands.Scheme.Modules.UnitCocycleDescentEffectiveStatement`. It shows that the sheaf
`L = cocycleModule p c` from `UnitCocycleDescent.Submodule` is trivial on every open `W` of
`Y` that carries a cocycle section which is a unit upstairs. The lemmas are internal and
have no separate literature source. Everything lives in the namespace
`Langlands.Scheme.UnitCocycleDescent`.

## Quotients of cocycle sections

`isPairInvariant_mul_inv`: let `σ` and `τ` be sections over `p ⁻¹ᵁ W` that satisfy
`IsCocycleSection p c W`, and suppose `σ` is a unit. Then `τ * σ⁻¹` is pair-invariant
(`IsPairInvariant` from `UnitCocycleDescent.FunctionDescent`). On an open `V` of `U`, write
`C` for the restriction of `c U a b h`. The hypotheses give `C · a^*σ = b^*σ` and
`C · a^*τ = b^*τ`. Pullbacks are ring maps, so `a^*(σ⁻¹) · a^*σ = 1` and
`b^*(σ⁻¹) · b^*σ = 1`. The equation `a^*τ · a^*(σ⁻¹) = b^*τ · b^*(σ⁻¹)` is a linear
combination of these four equations, found by `linear_combination`.

## Local triviality

From now on `p` is quasi-compact, flat and surjective.

`nonempty_restrict_iso_unit`: let `σ` be a section over `p ⁻¹ᵁ W` that satisfies the
cocycle condition and is a unit. Then the restriction of `L` to the open subscheme `W` is
isomorphic to the structure sheaf of `W`.

Proof. Let `M` be the restriction of `L` along the open immersion `W.ι`. Its sections over
an open `V` of `W` are the cocycle sections of `p_* 𝒪_X` over the image `W.ι ''ᵁ V`. Let
`σ₀` be the restriction of `σ` to `p ⁻¹ᵁ (W.ι ''ᵁ ⊤)`. It satisfies the cocycle condition by
`IsCocycleSection.map`, so it is a global section `s` of `M`. The candidate isomorphism is
the morphism `sectionHom M s : 𝒪_W ⟶ M` from the Library (`SectionLocus`), which sends a
function `r` to `r • s`. By `LineBundleDescent.sectionHom_app`, the section
`(sectionHom M s).app V r` is `p.app (W.ι ''ᵁ V) r' * σ_V`. Here `r'` is the function on
`W.ι ''ᵁ V` corresponding to `r` under `(W.ι.appIso V).inv`, and `σ_V` is the restriction
of `σ`. By `Scheme.Modules.Hom.isIso_iff_isIso_app`, it suffices to show that each of these
maps is bijective.

- Injectivity: `σ_V` is a unit, so multiplication by it is injective. `p.app` is injective
  (`app_injective`), and `(W.ι.appIso V).inv` is an isomorphism.
- Surjectivity: let `t` be a cocycle section over `W.ι ''ᵁ V`. By `isPairInvariant_mul_inv`,
  `t * σ_V⁻¹` is pair-invariant. By `exists_app_eq_of_isPairInvariant` it equals
  `p.app (W.ι ''ᵁ V) g` for a function `g`. Then `(W.ι.appIso V).hom g` maps to
  `p.app _ g * σ_V = t`.

The isomorphism is the inverse of `asIso (sectionHom M s)`.

# Monomorphisms of split tori over a field

Let `k` be a field, `𝕊 = Spec k`, and `I`, `J` finite index types. This module proves the
following statements for a homomorphism `f : splitTorus 𝕊 I ⟶ splitTorus 𝕊 J` of split tori
`𝔾_m^I ⟶ 𝔾_m^J` whose underlying morphism `f.hom.hom` is a monomorphism:

- `splitTorus.card_le_of_mono`: `Nat.card I ≤ Nat.card J`;
- `splitTorus.isIso_of_mono`: if moreover `Nat.card J ≤ Nat.card I`, then `f` is an isomorphism
  of group schemes.

The variants `splitTorus.card_le_of_mono_of_iso` and `splitTorus.isIso_of_mono_of_iso` prove the
same statements for a monomorphism `f : H ⟶ K` between group schemes given with isomorphisms
`H ≅ splitTorus 𝕊 I` and `K ≅ splitTorus 𝕊 J`. They conjugate `f` by these isomorphisms
(`splitTorus.mono_conj_of_iso`).

## The integer matrix

`splitTorus.characterMatrix f : J → I → ℤ` sends `j` to the character `f ≫ prⱼ` of `𝔾_m^I`. The
character is read in `ℤ^I` through the Library's `characterLatticeEquiv`. The Library formula for
the points of the character attached to an exponent vector gives `splitTorus.pointsEquiv_comp`:
on `T`-points, `f` sends `(tᵢ)ᵢ` to `(∏ᵢ tᵢ ^ m j i)ⱼ`. `splitTorus.affinePointsEquiv_comp` is
the same formula for points over an affine scheme `Spec R → 𝕊`, with values in `Rˣ`. The rows of
the matrix define the `ℤ`-linear map `splitTorus.characterRows f : ℤ^J → ℤ^I`,
`n ↦ ∑ⱼ nⱼ • mⱼ`.

## The rows span

`splitTorus.characterRows_surjective`: if `f` is a monomorphism, the rows span `ℤ^I`. Let `L` be
the span of the rows, and take the group algebra `k[ℤ^I ⧸ L]` (`testAlgebra`) as a test ring. Its
units `[n]` (`testUnit`) satisfy `[n] = 1` exactly when `n ∈ L` (`testUnit_eq_one_iff`, by
injectivity of `AddMonoidAlgebra.of`), and `∏ᵢ [eᵢ] ^ nᵢ = [n]` (`prod_testUnit_zpow`). The point
`x = ([eᵢ])ᵢ` of `𝔾_m^I` over this ring is sent by `f` to `([mⱼ])ⱼ = 1`, because each row `mⱼ`
lies in `L`. Since `f` is a monomorphism, `x = 1`, so every basis vector `eᵢ` lies in `L`.

Comparing ranks (`LinearMap.finrank_range_le`) gives `card_le_of_mono`.

## Equal ranks

`splitTorus.characterRows_bijective`: when the cardinalities agree, `characterRows f` is a
surjective linear map between free `ℤ`-modules of the same finite rank. It is therefore bijective,
by the Orzech property of the commutative ring `ℤ`
(`OrzechProperty.bijective_of_surjective_of_injective`).

`splitTorus.comp_surjective_of_mono` then shows that `f` is surjective on `T`-points for every
`T` over `𝕊`. Given a target point `y`, write `M` for the additive group of units of `Γ(T)`. Let
`φ : ℤ^J → M` be the linear map sending `eⱼ` to the `j`-th coordinate of `y`, and set
`ψ = φ ∘ (characterRows f)⁻¹`. The point `(ψ(eᵢ))ᵢ` of `𝔾_m^I` maps to `y` by the points formula.

Finally `splitTorus.isIso_of_mono` uses the Library's `isoOfPoints` to build an isomorphism of
group schemes. Its point maps are composition with `f`, which are bijective (injective because
`f` is a monomorphism). The Library's `hom_ext_points` shows that this isomorphism has
underlying homomorphism `f`.

This is a derived helper for maximality arguments about split tori. It was written for the
existence of the split component. It formalizes the standard fact that an injective homomorphism of split tori does not decrease the
rank, and is an isomorphism when the ranks agree. The test-algebra and Orzech-property route is
specific to this formalization.

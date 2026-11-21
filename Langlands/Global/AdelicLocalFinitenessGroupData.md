# Existence of the group data of `Ξ_main` (Bernstein–Lapid §7.2)

Module `Langlands.Global.AdelicLocalFinitenessGroupData`.

Source: J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234 (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`), §7.2, pp.211–212. At the start
of §7.2, BL fix elements `a_α ∈ A_{P_α}^G` with `⟨α, H_0(a_α)⟩ > 0` for each simple root
`α`. When `A_G ≠ 1` they also fix `z_1, …, z_r ∈ A_G` such that `H_0(z_1), …, H_0(z_r)` is a
basis of `𝔞_G`. BL take the existence of these elements for granted.

The Library states these requirements as the predicate
`Langlands.Global.IsLocalFinitenessGroupData iT ν u t z` (module
`Langlands.Global.AdelicLocalFinitenessStatement`). Its Markdown explains how the predicate
matches BL's choices: the subgroup `U_α` is the unipotent radical of `P_α`, and
`a_α = iT(t α)`. The present module proves that such data exist. Its main inputs are published
Library results on reductive groups. It proves no analytic statement.

Provenance: derived. The data are BL's; the constructions below are the standard ones and are
assembled here from Library theorems. Both
`Langlands.Global.UniformGrowthLocalFinitenessStatement` (BL Theorem 7.2) and
`Langlands.Global.EisensteinSystemDominationStatement` take these data as hypotheses.
Applying either result needs a witness, which this module provides.

## Setting

Throughout, `F` is a number field and `G` is a group scheme over `Spec F` with affine
structure morphism. Further, `iT : T → G` is a maximal split torus (`IsMaximalSplitTorus`),
`ν` is a generic cocharacter (`IsGenericCocharacter iT ν`), and
`Δ₀ = simpleRelativeRoots iT ν`. Where stated, `G` is connected reductive
(`IsConnectedReductive G`) and `G.X.left` is affine.

## Values of characters on `A_T`

`A_T = PositiveRealTorus.intrinsicSubgroup F T` is the subgroup of `T(𝔸)` on which every
character takes positive scalar idele values.

- `log_absoluteValue_positiveRealIdele`: for `x ∈ ℝ_{>0}`, the logarithm of the idele norm of
  the positive scalar idele of `x` is `[F : ℚ] log x`.
- `exists_positiveReal_characterValue`: for `g ∈ A_T` and a character `χ` of `T`, there is
  `x > 0` such that `χ(g)` is the positive scalar idele of `x` and
  `characterLog F T g χ = [F : ℚ] log x`.
- `characterValue_eq_one_of_characterLog_eq_zero`: if `g ∈ A_T` and
  `characterLog F T g χ = 0`, then `χ(g) = 1`.
- `exists_one_lt_of_characterLog_pos`: if `g ∈ A_T` and `characterLog F T g χ > 0`, then
  `χ(g)` is the positive scalar idele of some real `x > 1`.
- `cocharacterDual v` (a definition) is the additive map `χ ↦ ⟨1 ⊗ χ, v⟩` from the characters
  of `T` to `ℝ`, for `v ∈ 𝔞_T = X_*(T) ⊗ ℝ`. It is an element of `RealCharacterDual F T`.
  `cocharacterDual_apply` unfolds it.

## The three constructions

- `exists_closed_standardUnipotent_maximal` (requires `G` connected reductive with
  `G.X.left` affine) gives, for every `α ∈ Δ₀`, an affine group scheme `U_α` and a closed
  immersion homomorphism `u α : U_α → G`. The functor of points of its image is
  `standardUnipotent iT ν (Δ₀ \ {α})`. Proof: `standardCocharacter` gives a cocharacter `ζ_α`
  of `T` that is standard for `Δ₀ \ {α}`, and identifies `standardUnipotent iT ν (Δ₀ \ {α})`
  with the dynamic unipotent subgroup of `iT ∘ ζ_α`. Take
  `u α = Dynamic.Affine.unipotentHom (iT ∘ ζ_α)`. The Library shows that this homomorphism
  is a closed immersion (`Dynamic.Affine.isClosedSubgroup_unipotentHom`) and that it represents
  the dynamic unipotent subgroup (`Dynamic.Affine.isRepresentedBy_unipotentHom`). Its source is
  affine because a closed immersion is an affine morphism and `G.X.left` is affine.
- `exists_fundamentalCoweightPoints` (requires `G` connected reductive) gives points `t α` of
  `A_T` with `β(t α) = 1` for every simple root `β ≠ α`, and with `α(t α)` the positive scalar
  idele of a real `x > 1`. They also satisfy `H_G(iT(t α)) = 0`, that is,
  `characterLog F G (map iT (t α)) = 0`. Proof: `relativeRootReflectionExistence` provides the
  root reflection data. With them, `relativeFundamentalWeight` gives fundamental coweights
  `ϖ^∨_α ∈ 𝔞_T` with `⟨α, ϖ^∨_α⟩ = 1` and `⟨β, ϖ^∨_α⟩ = 0` for `β ≠ α`. Each `ϖ^∨_α` lies
  in the annihilator of the restrictions to `T` of the rational characters of `G`. Fix a
  splitting of `T`, and put `t α = PositiveRealTorus.positiveExp (cocharacterDual ϖ^∨_α)`. Its
  logarithm is `cocharacterDual ϖ^∨_α`
  (`PositiveRealTorus.characterLog_full_logParameters`). By the lemmas on `A_T` above, the
  values of `α` and of the other simple roots are as required. `H_G(iT(t α))` is the
  logarithm at `t α` composed with restriction of characters along `iT`
  (`characterLog_map`), and it vanishes because `ϖ^∨_α` lies in the annihilator.
- `exists_centralSplitPoints` (requires `G` connected reductive) gives `r` and points `z j`
  (`j < r`) of `A_T`. Every simple root is `1` on each `z j`, and the vectors
  `H_G(iT(z j))` are linearly independent and span `𝔞_G = RealCharacterDual F G`. Proof:
  `splitComponentStatement` gives the split component `a : A → G`. By `characterRestriction`,
  restriction of rational characters along `a` is injective with image of finite index, so
  `realCharacterDualRestrictionEquiv` is a linear isomorphism `Φ : 𝔞_A ≅ 𝔞_G`. Thus `𝔞_G`
  is finite dimensional. Let `r = dim 𝔞_G` and let `b_j` be a basis of `𝔞_G`.
  `relativeSplitCentralDirections` gives a homomorphism `f : A → T` with `iT ∘ f = a`, such
  that the kernel of real restriction of characters along `f` is the span of the relative
  roots (the real span `relativeRootSpanReal`). Fix a splitting of `A` and put `z j = f(PositiveRealTorus.positiveExp (Φ⁻¹ b_j))`.
  These points lie in `A_T` because homomorphisms map positive real points to positive real
  points (`PositiveRealTorus.map_intrinsicSubgroup_le`). From `iT ∘ f = a` and
  `characterLog_map` we get `H_G(iT(z j)) = Φ(Φ⁻¹ b_j) = b_j`. A simple root `β` restricts
  along `f` to a character with vanishing real restriction, so its logarithm at the positive
  point is `0`, and `β(z j) = 1`.

## The datum and the existence theorems

- `LocalFinitenessGroupDatum iT ν` is a structure bundling a choice of group data. Its fields
  are the affine group schemes `Ua α`, closed immersion homomorphisms `u α : Ua α → G`, points
  `t α`, a number `r`, points `z j` (`j < r`), and a proof of
  `IsLocalFinitenessGroupData iT ν u t z`.
- `LocalFinitenessGroupDatum.nonempty`: if `G` is connected reductive with `G.X.left` affine,
  `iT` is a maximal split torus and `ν` is generic, then a `LocalFinitenessGroupDatum iT ν`
  exists. It combines the three constructions above.
- `exists_isLocalFinitenessGroupData`: the same result in the existential form of the
  hypotheses of `EisensteinSystemDominationStatement` and
  `UniformGrowthLocalFinitenessStatement`. There are `Ua`, proofs that each `Ua α` is affine,
  `u`, proofs that each `u α` is a closed immersion, and `t`, `r`, `z` with
  `IsLocalFinitenessGroupData iT ν u t z`.

When `A_G = 1` the construction gives `r = dim 𝔞_G = 0`, as in BL, where the central
equations are then absent.

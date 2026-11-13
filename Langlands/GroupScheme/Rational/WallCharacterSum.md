# Rational characters of a common Levi across a rank-one wall

This module proves the structural input to the proof of
`Langlands.Plancherel.WallUnramifiedTwistSurjectivityStatement`. Everything is in
the namespace `Langlands.GroupScheme.WallCharacterSum`, over a field `k` of
arbitrary universe `u`.

The main theorem is `exists_nsmul_eq_restrict_add`. Its hypotheses are exactly
the structural hypotheses of the wall statement:

* parabolics `p : P ⟶ G`, `q : Q ⟶ M`, `p₁ : P₁ ⟶ G`, `q₁ : Q₁ ⟶ M₁`;
* rational Levis `m : M ⟶ P`, `l : L ⟶ Q`, `m₁ : M₁ ⟶ P₁`, `l₁ : L ⟶ Q₁`;
* the connected reductive group `G`;
* `l ≫ q ≫ m ≫ p = l₁ ≫ q₁ ≫ m₁ ≫ p₁`;
* `q₁` not an isomorphism, and maximal among proper parabolics of `M₁` (the
  hypothesis `hmax`, verbatim from the statement);
* a split component `a : A_M ⟶ M` with `b ≫ l ≫ q = a`, where `b ≫ l₁ ≫ q₁` is not
  central.

Conclusion: for every rational character `χ` of `L` there are `n > 0` and rational
characters `ψ` of `M` and `ψ₁` of `M₁` with
`n • χ = characterRestrict (l ≫ q) ψ + characterRestrict (l₁ ≫ q₁) ψ₁`.
So the two restriction images together have finite index in `X*(L)`.

This is internal, derived material. The mathematical idea is the standard
comparison of root spans in `ℚ ⊗ X*(T)` for a common maximal split torus `T`.
Its structural inputs are published Library theorems: the root reflections, the
complement of the relative root span, the central directions, and the rank-one
central-kernel character. No new structural assertion is introduced.

## Pairing with cocharacters (section `Pairing`)

For a commutative group scheme `A` and a cocharacter `ν`,
`ratPairing ν : ℚ ⊗[ℤ] X*(A) →ₗ[ℚ] ℚ` is the rational extension of `χ ↦ ⟨χ, ν⟩`.
It is the base change of `(latticePairing A).flip ν` followed by `ℚ ⊗ ℤ ≅ ℚ`.

* `ratPairing_tmul`: `ratPairing ν (q ⊗ χ) = q * ⟨χ, ν⟩`.
* `ratPairing_zsmul_sub`: the map is additive and `ℤ`-homogeneous in `ν`.
* `eq_zero_of_ratPairing`: on a split torus, an element pairing to zero with every
  integral cocharacter is zero. Clear denominators with
  `exists_nsmul_eq_one_tmul`. The resulting integral character is zero because
  the Library's `CocharacterUniformizer.latticePairing_isPerfPair` makes the
  lattice pairing perfect.

## Orthogonality to root spans (section `RootSpan`)

* `ratPairing_restrict_eq_zero_of_isCentral`: let `f ≫ i = m` factor a morphism
  `m : A ⟶ G` through `i : T ⟶ G`. Suppose `ν ≫ m` is central for a cocharacter
  `ν` of `A`. Then every element of the relative root span of `i`, restricted to
  `A`, pairs to zero with `ν`. For roots this is the Library lemma
  `MaximalLeviConeComplementLine.latticePairing_restrict_eq_zero_of_isCentral`.
  It extends to the span by linearity.
* `restrict_orthogonal_rootSpan`: let `iH` be a maximal split torus of a connected
  reductive `H`, and let `iH ≫ j = iG` be a monomorphism into `G`. Let `B` be a
  bilinear form on `ℚ ⊗ X*(T)` invariant under the full relative Weyl action of
  `iG` (`relativeWeylFullRatAction`). Then `B v s = 0` whenever `v` lies in the
  range of `rationalCharacterRestrictRat iH` and `s` lies in the relative root
  span of `iH`.
  Proof: for a root `α`, `relativeRootReflectionExistence` provides a
  representative `n` in the normalizer of `iH`. It acts by
  `χ ↦ χ - ⟨χ, α^∨⟩ • α`, with `⟨α, α^∨⟩ = 2`. Its image under
  `normalizerPointsMap` in the normalizer of `iG` acts the same way
  (`weylAction_normalizerPointsMap`). It fixes restrictions of characters of `H`
  (`weylAction_torusCharacterRestrict`) and sends `α` to `-α`. Then
  `apply_eq_zero_of_fixed_of_neg` gives the claim for generators, and linearity
  gives it in general.

## The wall lemma (section `Wall`)

`rootSpan_inf_le_of_wall`: take the wall hypotheses (`q`, `l`, `q₁`, `l₁`, `hne`,
`hmax`, `a`, `b`, non-centrality) and a maximal split torus `iL` of `L`. Then the
relative root span of `iL ≫ l ≫ q` meets that of `iL ≫ l₁ ≫ q₁` inside the
relative root span of `iL`.

Proof:

1. Let `a_L : A_L ⟶ L` be a split component of `L` (`splitComponentStatement`).
   `relativeSplitCentralDirections` gives `f : A_L ⟶ T` with `f ≫ iL = a_L` and
   `ker (rationalCharacterRestrictRat f) = relativeRootSpan iL`.
2. `hasCentralKernelCharacter_of_maximal parabolicDynamic` is the rank-one input.
   It gives `α₀ ∈ X*(A_L)` such that every cocharacter `ν` of `A_L` with
   `⟨α₀, ν⟩ = 0` has `ν ≫ a_L ≫ l₁ ≫ q₁` central.
3. `b` is central in `L` (by `IsCentral.of_comp` through the closed immersions
   `l` and `q`), so `IsSplitComponent.exists_factor` gives `c : A_M ⟶ A_L` with
   `c ≫ a_L = b`. Since `b ≫ l₁ ≫ q₁` is not central, `isCentral_of_forall_cocharacter`
   gives a cocharacter `ε` of `A_M` with `ε ≫ b ≫ l₁ ≫ q₁` not central. Put
   `ε₀ = ε ≫ c`. Then `ε₀ ≫ a_L ≫ l ≫ q = ε ≫ a` is central in `M`, and
   `⟨α₀, ε₀⟩ ≠ 0` by step 2.
4. Let `x` lie in both root spans and let `ν` be any cocharacter of `A_L`. By the
   first lemma of the previous section, the restriction of `x` to `A_L` pairs to
   zero with `ε₀`, using the root span of `M`. It also pairs to zero with
   `⟨α₀, ε₀⟩ ν - ⟨α₀, ν⟩ ε₀`, using the root span of `M₁`: this cocharacter is
   killed by `α₀`, hence central in `M₁`. So `⟨α₀, ε₀⟩ · ⟨x|, ν⟩ = 0`, hence
   `⟨x|, ν⟩ = 0`. By `eq_zero_of_ratPairing` the restriction of `x` vanishes, so
   `x ∈ relativeRootSpan iL`.

## Assembly (section `Assembly`)

* `characterRestrict_injective`: restricting rational characters of a connected
  reductive `L` to a maximal split torus is injective. Restriction to the split
  component is injective (`characterRestriction`), and the split component
  factors through the torus.
* `exists_nsmul_eq_restrict_add_of_le_sup`: suppose the rationalized restriction
  image of `X*(L)` in `ℚ ⊗ X*(T)` lies in the sum of the images from `M` and `M₁`.
  Suppose also that restriction from `L` to the split torus `T` is injective. Then
  the conclusion of the main theorem holds. Proof: decompose `1 ⊗ χ`, clear the
  two denominators, and use injectivity of `X*(T) → ℚ ⊗ X*(T)` on a split torus
  (`IsSplitTorus.character_toRat_injective`) together with injectivity of
  restriction.
* `restrictRange_le_sup`: this proves the inclusion hypothesis above when `iL`
  is maximal split in `L`, `iL ≫ l ≫ q` in `M`, `iL ≫ l₁ ≫ q₁` in `M₁`, and
  `iL ≫ l ≫ q ≫ m ≫ p` in `G`.
  The relative Weyl group of the last torus is finite
  (`IsConnectedReductive.finite_relativeWeylGroup`), and `ℚ ⊗ X*(T)` is
  finite-dimensional. So `exists_invariant_anisotropic` gives an invariant
  anisotropic form `B`. `relativeCharacterRootComplement` makes, for `M` and
  `M₁`, the restriction range and the root span sum to the whole space. The
  previous section makes each range `B`-orthogonal to its root span, for `L`, `M`
  and `M₁`. The wall lemma gives the intersection condition, and
  `le_sup_of_anisotropic` concludes.
* `exists_maximalSplitTorus_factor_levi`: some maximal split torus of `G` factors
  through `L`.
  Proof: `ParabolicLeviTorus.exists_maximalSplitTorus_factor` (with
  `parabolicDynamic`) gives a maximal split torus of `G` inside `M`, maximal in
  `M`, and a maximal split torus of `M` inside `L`. `maximalSplitTorusConjugacy`
  in `M` conjugates the second onto the first. `comp_innerIso_hom_comp`
  transports this conjugation to `G`, and `IsMaximalSplitTorus.of_factor`
  concludes.
* `exists_nsmul_eq_restrict_add`: choose `iL` as in the previous item. Maximality
  in `M`, `M₁` and `L` follows from `IsMaximalSplitTorus.of_comp`, using the
  commutativity hypothesis for `M₁`. Then combine the three previous items.

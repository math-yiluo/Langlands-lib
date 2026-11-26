# Rational points and heights for standard parabolic subgroups

Module `Langlands.Global.ArthurSiegelPartitionPoints`, namespace
`Langlands.Global.ArthurTruncation`. The objects are those of `Langlands.Global.ArthurTruncation`
(see its Markdown): a group scheme `G` over a number field `F`, a maximal split torus `i : T → G`,
a generic cocharacter `ν`, the standard parabolic subgroups `P_S = Standard.parabolicHom i ν S`,
a compact subgroup `K` with `P_0(𝔸)K = G(𝔸)` and the height `H_0 = height hi hK hρ` with values
in `𝔞_0 = V T`.

## Results

- `mem_parabolicRationalImage_iff`: `parabolicRationalImage` is the published `rationalImage`.
- `parabolicRationalImage_mono`: `P_{S_1}(F) ⊆ P_S(F)` for `S_1 ⊆ S ⊆ Δ_0`, from the published
  order of standard parabolic subgroup functors `standardParabolicOrder` and
  `rationalImage_le_of_range_le`.
- `rationalSubgroup_le_parabolicRationalImage`: `G(F) ⊆ P_{Δ_0}(F)`, from
  `standardParabolicEndpoints` (`P_{Δ_0} = G` as subgroup functors).
- `exists_parabolicFactor`: a factorization `f : P_0 → P_S` of the closed representatives, from the
  order and `SubgroupFunctor.exists_factor_of_range_le`.
- `isIwasawaCompact_standard`: `P_0(𝔸)K = G(𝔸)` implies `P_S(𝔸)K = G(𝔸)`.
- `height_standard_eq`: the height `H_{P_S}` of `K` is the image of `H_{P_0}` under the map
  `Hom(X(P_0), ℝ) → Hom(X(P_S), ℝ)` dual to restriction of characters along `f`.
- `toCharacterDual_height`: `toCharacterDual F i ν S (H_0(g)) = H_{P_S}(g)`, that is,
  `⟨χ|_T, H_0(g)⟩ = H_{P_S}(g)(χ)` for every rational character `χ` of `P_S`.
- `height_sub_mem_span`: for `r ∈ P_S(F)` and `y ∈ G(𝔸)`, `H_0(ry) − H_0(y)` lies in the span of
  the coroots of `S`. It uses `ParabolicSpacesComparisonStatement` (Arthur 2005, (5.1)) as a
  hypothesis: its fourth conjunct identifies the kernel of `toCharacterDual F i ν S` with that span,
  and `H_{P_S}(ry) = H_{P_S}(y)` by the product formula (`IsIwasawaCompact.height_rational_mul`).
  Equivalently, the projection of `H_0(ry)` to `𝔞_{P_S}` is that of `H_0(y)`, as used in Arthur
  1978, proof of Lemma 6.4.

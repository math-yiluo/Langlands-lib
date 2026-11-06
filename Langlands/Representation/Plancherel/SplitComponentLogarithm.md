# Logarithm vectors of Levi points along a split component

Lean module: `Langlands.Representation.Plancherel.SplitComponentLogarithm`,
namespace `Langlands.Plancherel`.

## Purpose and provenance

Provenance: internal. For a Levi subgroup `M` with split component `A`, Waldspurger's map
`H_M : M(F) → a_M` (Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra* (2003), I.1) is characterized by `q^{-⟨χ, H_M(m)⟩} = |χ(m)|_F` for rational
characters `χ` of `M`. The convergence proof of the standard intertwining integrals (IV.1.1,
printed pp. 277–281) compares several such logarithms at one point `m`. This module realizes
`H_M(m)` as one vector `w` of the real cocharacter space of `A`, in the natural-logarithm
normalization, and shows that pairing with `w` computes both the logarithm of `|ξ(m)|` for
rational characters `ξ` of `M` and the logarithm of `‖χ(m)‖` for unramified characters `χ` of
`M(F)`. The definition and the argument are derived from Library results and are not
transcribed from the source.

## Setting and notation

- `F` is a nonarchimedean local field with normalized absolute value
  `LocalField.residueNormalizedAbsoluteValue F` and residue cardinality `q`.
- `A` is a commutative group scheme over `Spec F`, `M` is a group scheme over `Spec F`, and
  `a : A.toGrp ⟶ M` is a homomorphism. `RealTorusSpace.V A` is the real cocharacter space
  `ℝ ⊗ X_*(A)`, `RealTorusSpace.Vstar A` the real character space `ℝ ⊗ X^*(A)`, and
  `RealTorusSpace.pair A` their real pairing.
- `characterRestrict a : rationalCharacters M →+ rationalCharacters A.toGrp` restricts rational
  characters along `a`, and `rationalCharacters.equivCharacterLattice A` identifies rational
  characters of `A` with the character lattice `X^*(A)`.
- `rationalCommonNormKernel M` is the subgroup of `m ∈ M(F)` with `|ξ(m)|_F = 1` for every
  rational character `ξ` of `M`.
- For a split torus `A` (proof `hT`) and a character `χ` of `A(F)` with values in `ℂˣ`,
  `SplitTorus.normalizedRealPart hT χ ∈ Vstar A` is the Library's normalized real part. Its
  pairing with `r ⊗ c`, for `c ∈ X_*(A)`, is `r · (-log ‖χ(c(ϖ))‖ / log q)`, where `c(ϖ)` is the
  Library's uniformizer section.

## Declarations

- `IsSplitComponentLogarithm hT a m w` (definition): `w : RealTorusSpace.V A` is a logarithm
  vector of `m ∈ M(F)` when both of the following hold.
  1. For every rational character `ξ` of `M`,
     `pair (1 ⊗ (ξ restricted to A)) w = log |ξ(m)|_F`.
  2. For every group homomorphism `χ : M(F) →* ℂˣ` whose kernel contains
     `rationalCommonNormKernel M`,
     `log ‖χ(m)‖ = pair (normalizedRealPart hT (χ ∘ a)) w`, where `χ ∘ a` is `χ` composed with
     the map `A(F) → M(F)` induced by `a`.
- `exists_splitComponentLogarithm` (main result): assume `M` is connected reductive, `a` is a
  split component of `M` (`IsSplitComponent a`, so in particular `A` is a split torus) and
  restriction of rational characters along `a` is injective. Then every `m ∈ M(F)` has a
  logarithm vector `w`.

No continuity is assumed of `χ` in the second condition, and no compatibility between the two
conditions is assumed. The injectivity hypothesis is the conclusion of the Library's
`CentralSplitTorusCharacterStatement` for split components and is kept as an explicit premise.

## Proof

Let `N` be the index of the range of `characterRestrict a`. This index is finite by the Library
theorem `IsSplitComponent.finiteIndex_range_characterRestrict`.

1. By `RenardCartan.pow_index_mem_splitValuationImage`, which uses the injectivity hypothesis,
   the `N`-th power of the rational-character valuation of `m` lies in the valuation image of
   `A(F)`. By `RenardCartan.exists_rationalCharacterValuation_map_eq` there is a cocharacter
   `c ∈ X_*(A)` such that `z = a(c(ϖ))` has the same valuation as `m ^ N`. Hence
   `m ^ N z⁻¹` lies in the kernel of the valuation, which is `rationalCommonNormKernel M` by
   `rationalCharacterValuation_ker`.
2. Take `w = (-log q / N) ⊗ c`.
3. Rational characters: by `RealTorusSpace.pair_tmul_tmul` the pairing equals
   `(-log q / N) · ⟨ξ|_A, c⟩`. By `RenardCartan.rationalCharacterValuation_map_uniformizerSection`,
   `⟨ξ|_A, c⟩` is the valuation of `ξ(z)`, which is `N` times the valuation of `ξ(m)`. By
   `rationalNormLogarithm_spec` and `rationalNormLogarithm_eq_intValuation`,
   `|ξ(m)|_F = q ^ (-v(ξ(m)))`. Taking logarithms gives the claim.
4. Unramified characters: since `χ` kills `m ^ N z⁻¹`, `χ(z) = χ(m) ^ N`. By
   `SplitTorus.pair_normalizedRealPart_tmul`, the pairing equals
   `(-log q / N) · (-log ‖χ(z)‖ / log q)`. This unfolds definitionally, because the uniformizer
   section used in step 1 is the lattice section used by the normalized real part
   (`RenardCartan.uniformizerSection_eq_latticeSection`). Then
   `log ‖χ(z)‖ = N · log ‖χ(m)‖`, and the factors cancel since `log q ≠ 0` and `N ≠ 0`.

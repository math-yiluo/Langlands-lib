# Integrability of Siegel-dominated functions on `G(F) \ G(𝔸)`

Module `Langlands.Global.AdelicSiegelDominatedIntegrabilityProof`.

This module proves the Library statement
`Langlands.Global.SiegelDominatedIntegrabilityStatement`
(`Langlands/Global/AdelicWavePacketRapidDecaySiegelReduction.lean`):

```
theorem Langlands.Global.siegelDominatedIntegrability : SiegelDominatedIntegrabilityStatement
```

The theorem has no hypotheses beyond those of the statement. It uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. In particular it does not use the finite-place
Iwasawa decomposition (`FinitePlaceGroupPoints.ParabolicIwasawaStatement`) or
`AdelicGoodSiegelReductionStatement`.

The statement and its derivation from Lapid's §1–2 are explained in
`AdelicWavePacketRapidDecaySiegelReduction.md`. The proof here does not follow Lapid's
domain `𝔰` and his function `σ_L`. It follows the alternative route through the Library's
reduction theory: a Siegel cover of `G(𝔸)¹` by finitely many right translates of a weak Siegel
product, the decomposition `G(𝔸) = A_G G(𝔸)¹`, Haar measure of Siegel sets, and a lower bound
of `adelicLogHeight` on the Siegel set.

The module uses two helper modules:
`Langlands/Analysis/Local/SiegelSetIntegral.lean` (weighted integrals over abstract Siegel sets
and summability of polynomial weights on `ℤ^n`) and `Langlands/Global/LeftCosetUnfoldingBound.lean`
(the unfolding inequality on `Γ \ H`).

## Sources

- E. Lapid, *On the Harish-Chandra Schwartz space of G(F)\G(A)*, ESI preprint 2403 (2012),
  registered as `lapid-2013-harish-chandra-schwartz-space-automorphic`, §1–2 (PDF pp. 5–8): the
  statement proved here is derived from his (2), (3), property 2 and (5), as explained in
  `AdelicWavePacketRapidDecaySiegelReduction.md`.
- P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered as
  `delorme-2023-spectral-theorem-langlands`, (2.5) (published PDF numbering, §2, pp. 7–9), where
  Lapid's (5) is quoted.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`, I.1.13 (printed p. 18): Haar
  measure in Iwasawa coordinates `dg = du m^{-2ρ₀} dm dk`. The proof here replaces this formula
  by piecewise volume bounds (`SiegelSetIntegral.md`); the cancellation of `δ(a)` against the
  Haar density is the same.

## Notation and data

`F : Type` is a number field and `G` an affine group scheme over `F`, locally of finite type and
connected reductive. `rho : MatrixRepresentation G (Fin N)` is a closed embedding. Write
`σ = adelicLogHeight F G rho` and `‖·‖ = RepresentationGrowth.adelicHeight F G rho`; the Library
proves `‖·‖ = N^{[F:ℚ]} · adelicSourceNorm` (`adelicHeight_eq_scalar_mul_sourceNorm`), and `‖·‖`
is submultiplicative (`adelicHeight_mul_le`) and at least `1` when `N > 0`.

For an algebraic Siegel setup `(T, i, ν, T₀, j)`, the setup contains a split central torus
`zc : Z₀ → T` such that `Z₀ → T → G` is a split component of `G`. By the Library's
`RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup`, the image of the positive points of
`Z₀` in `G(𝔸)` is `A_G = RestrictionSplitCentre.canonicalSubgroup F G`, the group of the
statement's central factor.

## Declarations

### Finite products

- `map_finprod_of_injective`: an injective monoid homomorphism commutes with `finprod`, with no
  finiteness hypothesis (both sides are `1` when the support is infinite).
- `coe_finprod_nnreal`: the coercion `ℝ≥0 → ℝ` commutes with `finprod`.

### The Levi decomposition and the torus

- `exists_semidirect_standard`: under the setup, `P(𝔸) = M(𝔸) ⋉ N(𝔸)` inside `G(𝔸)`
  (`IsSemidirectDecomposition`) with continuous Levi projection. It is the published
  `exists_standardLeviPart` combined with `IsSemidirectDecomposition.of_retraction` and
  `continuous_of_retraction_projection`, read in `G(𝔸)` instead of `G(𝔸)¹`.
- `positiveMap_commute_of_mem_standardLevi`: if `standardLevi = torusCentralizer` (part of the
  setup), the image of the positive points of any torus mapping to `T` commutes with `M(𝔸)`.
  The argument is the one used in the published `siegelProductFiniteMeasureStatement_of_inputs`.
- `siegelTorusMap zc hzc : A_{Z₀} × A_{T₀} →* G(𝔸)`, `(z, x) ↦ z x`, where `z` and `x` are
  mapped by `positiveMap`. It is a homomorphism (`MonoidHom.noncommCoprod`) because the image of
  `Z₀` is central (`positivePointMap_commute`, from `IsCentral`). `positiveMap_central` records
  this centrality and `continuous_siegelTorusMap` the continuity.
- `centralSiegelSet zc hzc C t` is the set `Ω_N Ω_M a(A_{Z₀} × A_{T₀}(t)) K` of `G(𝔸)`, where
  `a = siegelTorusMap`, `Ω_N`, `Ω_M` are the images of the compact factors of `C`,
  `A_{T₀}(t) = weakSimpleRootChamber F T₀ T j G i ν t` and `K = C.compactSubgroup`. Since the
  image of `Z₀` is central and equals `A_G`, this set is `A_G · weakSiegelProduct`.
- `siegelModulusNN x` is `∏ᶠ_{β ∈ Φ⁺} |β(x)|^{m_β}` in `ℝ≥0`; `coe_siegelModulusNN` identifies its
  real value with the statement's `siegelModulus`.

### The weighted Siegel bound in `G(𝔸)`

`exists_lintegral_centralSiegelSet_le` takes the setup, compact factors `C` whose compact
subgroup `K` lies in an open subgroup `H₁` of `G(𝔸)` with `H₁ ⊆ P(𝔸) K`, positive-torus
compatibility of `K` (`IsPositiveTorusCompatible`), a threshold `t`, characters
`λ_c` of `A_{Z₀} × A_{T₀}` with compact dyadic box, and exponents with
`siegelModulusNN(x) ≤ ∏_c λ_c(z, x)^{e_c}`. It gives `D < ∞` such that every measurable
`f ≥ 0` with

`f(n m a(z, x) k) ≤ siegelModulusNN(x) · Φ(κ(z, x))` for `x ∈ A_{T₀}(t)`, `n ∈ Ω_N`, `m ∈ Ω_M`,
`k ∈ K`

satisfies `∫_{centralSiegelSet} f d(haar) ≤ D ∑_κ Φ(κ)`, where `κ = zIndex λ` is the integer
dyadic index. *Proof.*
- `Q = P(𝔸)`, `M = M(𝔸)`, `U = N(𝔸)` are closed (`isClosed_standard…Image`) and
  `Q = M ⋉ U` (`exists_semidirect_standard`).
- The published `CompactFactorization.exists_measure_inter_mul_eq_of_isOpen`, applied in
  `G(𝔸)` with `H₁`, gives `c` with `haar(S ∩ Q H₁) = c μ_Q(S ∩ Q)` for measurable right
  `K`-saturated `S`. So the saturated-set bound holds for `μ = haar.restrict (Q H₁)`.
- `a` takes values in `M(𝔸)` (`positiveMap_mem_standardLeviImage`), is central in `M(𝔸)`, and
  commutes with `K ∩ Q` (centrality of `Z₀` and `IsPositiveTorusCompatible`).
- The modulus: `δ_U(a(z, x)) = δ_U(z) δ_U(x) = siegelModulusNN(x)`. The first factor is `1`
  because `z` is central (`closedNormalizerCharacter_eq_one_of_commute`); the second is the
  published modulus formula `positiveTorusUnipotentModulus_of_coordinates
  positiveTorusTriangularCoordinates`.
- `SiegelSetMeasure.exists_lintegral_chamber_le` applies with `C = A_{Z₀} × A_{T₀}(t)`.
- The Siegel set lies in `Q K ⊆ Q H₁`, so its integrals for `haar` and for `μ` agree
  (`Measure.restrict_restrict_of_subset`).

### Coordinates

- `siegelCoordinates zc χ` is the family of characters of `A_{Z₀} × A_{T₀}` indexed by
  `J₀ ⊕ Δ`: `(z, x) ↦ |χ_k(z)|` for rational characters `χ_k` of `G` (via `characterNorm` of the
  image of `z`), and `(z, x) ↦ |α(x)|` for the simple relative roots `α ∈ Δ`.
- `isCompact_characterNormBox`: for a coordinate splitting `e : Z₀ ≅ 𝔾_m^I` and characters
  `χ_k` with `|χ_k(z(x))| = x_k^n` (`n > 0`) on positive points `x ∈ (ℝ_{>0})^I`, the box
  `{z | 1/2 ≤ |χ_k(z)| ≤ 2 for all k}` in `A_{Z₀}` is compact. *Proof.* Its preimage under the
  surjection `fullIntrinsic` is closed and lies in the compact box `[1/2, 2]^I`, because
  `x^n ∈ [1/2, 2]` with `n ≥ 1` forces `x ∈ [1/2, 2]`.
- `isCompact_dyadicBox_siegelCoordinates`: the dyadic box of `siegelCoordinates` is the product of
  this box with the simple-root box `{1/2 ≤ |α| ≤ 2}` of `A_{T₀}`, which is compact by the
  published `simpleRootBoxCompactStatement_of_rootComplement relativeRootNegation
  relativeCharacterRootComplement`.
- `exists_siegelModulusNN_le`: with exponents `0` on the central coordinates and the exponents of
  the published `exists_simpleRoot_exponents` on the roots,
  `siegelModulusNN(x) = ∏_c λ_c(z, x)^{e_c}`.

### Elementary estimates

- `abs_intLog_two_le`: `|⌊log₂ r⌋| ≤ |log r| / log 2 + 1` for `r > 0`.
- `abs_log_le_of_le_of_inv_le`: `r ≤ C h^e` and `r⁻¹ ≤ C h^e` with `C, h ≥ 1` give
  `|log r| ≤ log C + e log h`.
- `abs_log_le_of_mem_Icc`: `t ≤ r ≤ C h^e` with `t > 0`, `C, h ≥ 1` give
  `|log r| ≤ |log t| + log C + e log h`.
- `log_adelicHeight_le`: `log ‖x‖ ≤ log N^{[F:ℚ]} + σ(x)`.
- `mul_five_le`, `max_le_of_sum_le`: real arithmetic; the second turns `∑_c |κ_c| ≤ n(Aσ + |B|)`
  into `max(1, c₀ ∑_c |κ_c| - C₀) ≤ σ` for `c₀ = 1/((n + 1)(A + 1))`, `C₀ = |B|/(A + 1)`, using
  `σ ≥ 1`.

### The height at Siegel points

Let `X = n m a(z, x) k w` with `n ∈ Ω_N`, `m ∈ Ω_M`, `k ∈ K`, `w` in a finite set
`W ⊆ G(𝔸)¹`.

- `characterNorm_siegelPoint`: for every rational character `χ` of `G`, `|χ(X)| = |χ(z)|`.
  The factors `n`, `m`, `x`, `k`, `w` are norm one: `N(𝔸) ⊆ G(𝔸)¹`
  (`standardUnipotentImage_le_normOne` with the published `unipotentRationalQuotientCompact`),
  `m ∈ M(𝔸)¹` maps into `G(𝔸)¹` (`map_normOneSubgroup_le`), `T₀` maps into the derived group
  (`positiveMap_mem_normOne_of_range_le_derived`), compact subgroups are norm one
  (`compactSubgroup_le_normOneSubgroup`), and `W ⊆ G(𝔸)¹`.
- `adelicHeight_le_of_eq_mul` and `exists_adelicHeight_siegelTorusMap_le`: there is `B ≥ 1` with
  `‖a(z, x)‖ ≤ B ‖X‖`. Since `z` is central, `a(z, x) = m⁻¹ n⁻¹ X w⁻¹ k⁻¹`; the heights of
  `m⁻¹`, `n⁻¹`, `k⁻¹`, `w⁻¹` are bounded on the compact sets `Ω_M`, `Ω_N`, `K` and the finite set
  `W` (`continuous_adelicHeight`).
- `exists_rootNorm_le`: for a relative root `α` there are `C, e` with
  `|α(x)| ≤ C ‖a(z, x)‖^e`. *Proof.* Put `t = z₀(z) j(x)` in `T(𝔸)`, so that `i(t) = a(z, x)`.
  `T → G` is a closed subgroup (`IsMaximalSplitTorus`), so `i ≫ rho` is a closed embedding of
  `T`, and the published `exists_characterNorm_le` gives `|α(t)| ≤ C ‖t‖_{i ≫ rho}^e`, where
  `‖t‖_{i ≫ rho} = ‖i(t)‖` (`adelicMatrix_map`). The root `α` is trivial on the central split
  torus `Z₀` (the published `root_restrict_eq_zero_of_isCentral`), so `|α(t)| = |α(x)|`.
- `exists_abs_zIndex_le` (**lower bound of the height**): there are `A ≥ 0` and `B` with
  `|κ_c(z, x)| ≤ A σ(X) + B` for every coordinate `c` and every such `X` with `x ∈ A_{T₀}(t)`.
  For a central coordinate, `|χ_k(z)| = |χ_k(X)|` and `|χ_k(X)|^{±1} ≤ C ‖X‖^e`
  (`exists_characterNorm_le`, which uses that `rho` is closed). For a root coordinate,
  `t ≤ |α(x)| ≤ C B^e ‖X‖^e`. In both cases the elementary estimates and `log_adelicHeight_le`
  bound `|⌊log₂ λ_c⌋|` linearly in `σ(X)`.

### Siegel points and the cover

- `isSiegelPoint_of_mem`: `X = n m a(z, x) k w` with `x ∈ A_{T₀}(t)`, `w ∈ W` satisfies
  `IsSiegelPoint F G T i ν T₀ j C t W x X`, with central factor `z ∈ A_G`
  (`imageSubgroup_eq_canonicalSubgroup`) and torus coordinate `x`; the factorization
  `X = z (n m x k) w` uses centrality of `z`.
- `exists_rational_mul_mem_centralSiegelSet_mul`: if every point of `G(𝔸)¹` has a rational left
  translate in `weakSiegelProduct · W`, then every `g ∈ G(𝔸)` has one in
  `centralSiegelSet · W`. Write `g = z g₁` with `z ∈ A_G` and `g₁ ∈ G(𝔸)¹`
  (`RestrictionSplitCentre.intrinsicNormOneDecomposition`), express `z` through `Z₀`, and move
  the central `z` into the torus factor.

### The theorem

`siegelDominatedIntegrability_of_pos` treats `N > 0`.

1. *Data.* The setup is the published `siegelAlgebraicSetupExistence_of_structural
   genericMinimalParabolic derivedMaximalSplitTorus derivedCentralSplitTorusProduct`.
   `exists_compact_openSubgroup_finite_cover` gives `K`, the open subgroup `H₁ ⊇ K` with
   `H₁ ⊆ P(𝔸) K`, positive-torus compatibility and a finite `W ⊆ G(𝔸)¹`, and
   `exists_rational_mul_mem_weakSiegelProduct_mul` gives compact factors `C` with compact
   subgroup `K` and a threshold `t` with `G(𝔸)¹ = G(F) · weakSiegelProduct · W`. The theorem uses
   `C`, `t`, `Ω = W` (finite, hence compact) and `d = 2n`, where `n` is the number of
   coordinates `I ⊕ Δ`; here `I` indexes a splitting of `Z₀`, and the central characters `χ_k`
   are those of the published `exists_characterNorm_full` (they exist because
   `characterRestrictionFiniteIndexStatement` gives finite index of the restriction of
   characters to the split component).
2. *Unfolding.* `LeftCosetSpace.lintegral_comp_out_le_setLIntegral`, with the cover of
   `exists_rational_mul_mem_centralSiegelSet_mul`, bounds the integral over `[G]` by
   `∫_{centralSiegelSet · W} f`.
3. *The finite set `W`.* The set `centralSiegelSet · W` is the union over `w ∈ W` of the right
   translates `centralSiegelSet · w`. Haar measure on `G(𝔸)` is right invariant
   (`adelicHaarUnimodularity.2`), so
   `∫_{centralSiegelSet · w} f = ∫_{centralSiegelSet} f(· w)`
   (`MeasurePreserving.setLIntegral_comp_preimage_emb`).
4. *Each translate.* At `X = n m a(z, x) k w`, the hypothesis on `f` for the Siegel point of
   `isSiegelPoint_of_mem` gives `f(X) ≤ siegelModulus(x) / σ(X)^d`. By
   `exists_abs_zIndex_le` and `max_le_of_sum_le`,
   `σ(X) ≥ max(1, c₀ ∑_c |κ_c| - C₀)`, so `f(X) ≤ siegelModulusNN(x) · Φ(κ)` with
   `Φ(κ) = max(1, c₀ ∑_c |κ_c| - C₀)^{-d}`. `exists_lintegral_centralSiegelSet_le` bounds each
   translate by `D ∑_κ Φ(κ)`.
5. *Summation.* `SiegelSetMeasure.tsum_decay_ne_top` shows `∑_{κ ∈ ℤ^n} Φ(κ) < ∞` for
   `d = 2n`. The finite sum over `W` of finite terms is finite.

`siegelDominatedIntegrability_of_zero` treats `N = 0`. A closed embedding into `GL_0` makes
`G(𝔸)` a subsingleton (`isClosedEmbedding_adelicMatrix`). With compact factors `{1}`, `{1}`,
`⊥`, threshold `1`, `Ω = {1}` and `d = 0`, the point `1` is a Siegel point with torus
coordinate `1`, so `f(1) < ∞`. Every representative `y.out` is `1`, and the total mass of `[G]`
is at most the Haar measure of the compact space `G(𝔸)`.

`siegelDominatedIntegrability` combines the two cases.

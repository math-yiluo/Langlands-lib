# Finite volume of the norm-one adelic rational quotient

This module proves the Library target
`Langlands.Global.AdelicGroupPoints.NormOneRationalQuotientFiniteVolumeStatement`
(`Langlands/Global/AdelicFiniteVolumeStatement.lean`). This is Getz–Hahn, Theorem 2.6.3, over
number fields. For every number field `F` and every affine group scheme `G` over `Spec F` that
is locally of finite type, smooth and connected, the measure
`normOneRationalQuotientHaarMeasure F G` is finite. This measure is the quotient of the actual
norm-one Haar measure on `G(𝔸_F)¹` by principal counting of `G(F)`. The theorem is

`Langlands.Global.AdelicGroupPoints.normOneRationalQuotientFiniteVolume :
  NormOneRationalQuotientFiniteVolumeStatement.{u}`.

The proof follows the Library's Siegel-set route for connected reductive groups, with one
change: no finite-place Iwasawa decomposition `P(𝔸_F) K = G(𝔸_F)` is used. Instead it uses the
weaker data of `Langlands/Global/AdelicOpenIwasawaCompact.lean`, together with the measure
bound of `Langlands/Global/AdelicSiegelMeasureOpenSubgroup.lean`. Those two modules and
`Langlands/Analysis/Local/OpenCompactFactorizationHaar.lean` were ported together with this module.

The final theorem uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Declarations

### `AdelicSiegelFactors.measure_mul_finite_lt_top`

Let `H` be a second-countable, locally compact topological group with its Borel σ-algebra,
let `ν₀` be a Haar measure on `H`, let `A ⊆ H` with `ν₀ A < ∞`, and let `W ⊆ H` be finite.
Then `ν₀ (A W) < ∞`.

*Proof.*
- `A W` is contained in the finite union `⋃_{w ∈ W} (· * w⁻¹)⁻¹' A` of right translates of `A`.
  By `measure_biUnion_lt_top` it suffices to bound each translate.
- The pushforward of `ν₀` under right multiplication by `w⁻¹` is left invariant
  (`isMulLeftInvariant_map_mul_right`). It is finite on compacts, because right
  multiplication is a homeomorphism (`IsFiniteMeasureOnCompacts.map`).
- By uniqueness of Haar measure (`Measure.isMulLeftInvariant_eq_smul`, which needs second
  countability), the pushforward is `c • ν₀` for a constant `c : ℝ≥0`.
- Hence `ν₀((· * w⁻¹)⁻¹' A) = c · ν₀ A < ∞`. The first equality is
  `MeasurableEquiv.map_apply`, which holds for every set.

### `AdelicSiegelFactors.exists_rational_mul_mem_weakSiegelProduct_mul`

**Hypotheses.**
- `F` is a number field, and `G` is locally of finite type and connected reductive.
- `T, i, ν, T₀, j` satisfy `IsSiegelAlgebraicSetup F G T i ν T₀ j`. Write
  `P = Standard.parabolicScheme i ν ∅`, `N = Standard.unipotentScheme i ν ∅` and
  `M = Standard.leviScheme i ν ∅`.
- `K` is a compact subgroup of `G(𝔸_F)`.
- `W` is a finite subset of `G(𝔸_F)¹` with `P(𝔸_F) (K W) = G(𝔸_F)`.

**Conclusion.** There are compact factor data `C : CompactFactors F G N M` with
`C.compactSubgroup = K` and a threshold `t : ℝ≥0ˣ` such that every `g ∈ G(𝔸_F)¹` has a
rational point `q ∈ G(F)` with

`q g ∈ weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t · W`.

The weak Siegel product is `Ω_N Ω_M A_{T₀}(t) K`, as in
`Langlands/Global/AdelicSiegelFactors.lean`.

*Proof.* This adapts the published `exists_isSiegelCover_of_chamber`
(`Langlands/Global/AdelicSiegelChamberReduction.lean`) to the compact set `Ω = K W`.
- `Ω` is compact (`IsCompact.mul`, since a finite set is compact). It lies in `G(𝔸_F)¹`
  because compact subgroups do (`compactSubgroup_le_normOneSubgroup`) and `W` does.
- The published chamber reduction for compact covers,
  `hasWeakChamberCoverReduction_of_rootLeviHeightBounds`, applies to `Ω`. Its root-Levi height
  input is `RepresentationGrowth.hasRootLeviHeightBounds_of_rankOne`, applied to the published
  rank-one height bound `RepresentationGrowth.rankOneParabolicRationalOrbitHeightBound`. It
  gives `t` such that every `g ∈ G(𝔸_F)¹` has `q` with `n m a (k w) = q g`, where:
  - `n ∈ N(𝔸_F)` and `m ∈ M(𝔸_F)¹`;
  - `a` lies in the weak chamber;
  - `k ∈ K` and `w ∈ W`.
- `Ω_N` and `Ω_M` are the published compact covers (`exists_unipotentCompactCover_of_setup`,
  and `exists_leviCompactCover_of_setup` with Springer's theorem
  `centralSplitCompactQuotient`). Then `C = ⟨Ω_N, Ω_M, K⟩`.
- As in the published proof, choose `μ ∈ M(F)` with `μ m ∈ Ω_M`. Choose `ρ ∈ N(F)` with
  `ρ (μ n μ⁻¹) ∈ Ω_N`; this uses that `P(𝔸_F)` normalizes `N(𝔸_F)`. Then
  `(ρ μ q) g = [ρ (μ n μ⁻¹)] [μ m] a k · w`, and the bracketed part lies in the Siegel product
  (`mem_productSet_iff`). The identity is the published rewriting followed by `group`, with
  the extra right factor `w`.

### `AdelicSiegelFactors.isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive`

For a number field `F` and an affine `G`, locally of finite type and connected reductive,
`normOneRationalQuotientHaarMeasure F G` is a finite measure.

*Proof.*
1. A Siegel setup `T, i, ν, T₀, j` exists, by `siegelAlgebraicSetupExistence_of_structural`
   with the published `genericMinimalParabolic`, `derivedMaximalSplitTorus` and
   `derivedCentralSplitTorusProduct`.
2. `exists_compact_openSubgroup_finite_cover` gives:
   - a compact `K` and an open `H₁ ⊇ K` with `H₁ ⊆ P(𝔸_F) K`;
   - the compatibility `IsPositiveTorusCompatible … K`;
   - a finite `W ⊆ G(𝔸_F)¹` with `P(𝔸_F) (K W) = G(𝔸_F)`.
3. `exists_rational_mul_mem_weakSiegelProduct_mul` gives `C` with `C.compactSubgroup = K` and
   `t`.
4. `measure_weakSiegelProduct_lt_top_of_openSubgroup` says the trace on `G(𝔸_F)¹` of the
   Siegel product `S` has finite Haar measure. Its three inputs are the published proofs
   `unipotentRationalQuotientCompact`,
   `positiveTorusUnipotentModulus_of_coordinates positiveTorusTriangularCoordinates` and
   `simpleRootBoxCompactStatement_of_rootComplement relativeRootNegation
   relativeCharacterRootComplement`.
5. Inside `G(𝔸_F)¹`, the trace of `S W` lies in (trace of `S`) · (trace of `W`): if
   `x = s w` with `x, w ∈ G(𝔸_F)¹`, then `s = x w⁻¹ ∈ G(𝔸_F)¹`. The trace of `W` is finite.
   So `measure_mul_finite_lt_top` gives finite Haar measure for the trace of `S W`.
6. Every `x ∈ G(𝔸_F)¹` has `q ∈ G(F)` with `q x ∈ S W`. The published covolume criterion
   `LeftCosetSpace.isFiniteMeasure_haarQuotientMeasure_of_measure_lt_top`, applied to the
   discrete subgroup `rationalNormOneSubgroup F G`, gives finiteness.

### `AdelicGroupPoints.connectedReductiveFiniteVolume`

`ConnectedReductiveFiniteVolumeStatement.{u}`
(`Langlands/Global/AdelicReductiveFiniteVolumeStatement.lean`) follows directly from the
previous theorem.

### `AdelicGroupPoints.normOneRationalQuotientFiniteVolume`

`NormOneRationalQuotientFiniteVolumeStatement.{u}`, the target. For smooth connected `G`, the
published reduction `isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_levi`
(`Langlands/Global/AdelicFiniteVolumeReduction.lean`) applies. It takes the
characteristic-zero Levi decomposition `characteristicZeroLeviDecomposition`, compactness of
unipotent rational quotients `unipotentRationalQuotientCompact`, and the connected reductive
case `connectedReductiveFiniteVolume`.

## Sources

- Jayce R. Getz and Heekyoung Hahn, *An Introduction to Automorphic Representations* (2024),
  Theorem 2.6.3. This is the statement proved; the proof route here is the Library's
  Siegel-set route.
- Armand Borel, *Reduction theory for arithmetic groups*, in *Algebraic Groups and
  Discontinuous Subgroups*, Proc. Sympos. Pure Math. 9 (1966), §1.6 and Lemma 1.9: finite
  measure of Siegel sets. This is the source cited by the published
  `AdelicSiegelMeasureReduction.md`, whose argument the finite-measure step reuses.

# Proof of the sharp Siegel count of rational points in conjugates of compact sets

Module `Langlands.Global.AdelicSiegelRationalConjugateCountingProof` proves

`Langlands.Global.siegelRationalConjugateCounting : SiegelRationalConjugateCountingStatement`

(module `Langlands.Global.AdelicSiegelRationalConjugateCountingStatement`; a multiplicity
refinement of the upper bound of Delorme 2023, Lemma 2.1 (i), as explained in the statement's
Markdown). The theorem has no hypotheses beyond those of the statement and uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

For a connected reductive `G` over a number field `F`, an algebraic Siegel setup
`(T, i, ν, T₀, j)`, compact factors `C` with compact subgroup `K`, a threshold `t`, compact sets
`Ω` and `E` of `G(𝔸)`, it gives `B ≥ 0` such that for every Siegel point
`x = z · (n m a k) · w` (`IsSiegelPoint`) the set `G(F) ∩ x E x⁻¹` is finite with at most
`B · siegelModulus a` elements. Below `δ(a) = siegelModulusNN a`, the `ℝ≥0`-valued modulus of the
Library (`coe_siegelModulusNN` identifies it with `siegelModulus`), `vol` is the Haar measure of
`G(𝔸)` and `N(𝔸) = standardUnipotentImage F G T i ν`, a closed subgroup.

The proof follows the route "Packing, Coordinates, Volume" of the statement's Markdown, with the
roles of `N` and its opposite exchanged in the volume step: the volume is controlled through the
Haar modulus of `N(𝔸)`, which the Library proves, and not through the opposite radical.

## Auxiliary results

- `mulEquivHaarChar_normalizerConj_positiveMap`: the Haar modulus `mulEquivHaarChar` of the
  conjugation `u ↦ a u a⁻¹` on `N(𝔸)` is `δ(a)`. This is the published
  `positiveTorusUnipotentModulus_of_coordinates positiveTorusTriangularCoordinates` read through
  `SiegelSetMeasure.coe_closedNormalizerCharacter`. With Mathlib's convention
  (`mulEquivHaarChar_smul_preimage`), `ν(a S a⁻¹) = δ(a) ν(S)` for a Haar measure `ν` on `N(𝔸)`.
- `conj_image_mul_subset_biUnion` (any group): if every point of `W₀` is `n q` with `n ∈ N₀` and
  `p q p⁻¹ ∈ Q`, and `E ⊆ ⋃_{g ∈ s} g⁻¹ W₀` for a finite `s`, then
  `p E p⁻¹ W' ⊆ ⋃_{g ∈ s} (p g⁻¹ p⁻¹) · (p N₀ p⁻¹) Q W'`. Indeed, for `e ∈ E` and `g e = n q`,
  `p e p⁻¹ w' = (p g⁻¹ p⁻¹)(p n p⁻¹)(p q p⁻¹) w'`.
- `preimage_image_mul` (any group): for a multiplicative equivalence `ψ`,
  `ψ⁻¹(ψ(A) V) = A ψ⁻¹(V)`.
- `measure_image_mul_le`: for a Haar measure `ν` (regular) and a topological group automorphism
  `φ` with `φ⁻¹(V) ⊆ V''`, `ν(φ(A) V) ≤ mulEquivHaarChar φ · ν(A V'')`, by
  `mulEquivHaarChar_smul_preimage` and the previous identity.

## The volume bound

`exists_measure_conj_mul_le`: for compact `E₁, W' ⊆ G(𝔸)` there is `C₀ < ∞` with

`vol(a E₁ a⁻¹ W') ≤ C₀ · δ(a)` for every `a` in the weak chamber of threshold `t`.

*Proof.* Take `W₀`, `N₁`, `Q` from `exists_siegel_archimedeanCell` (module
`AdelicSiegelArchimedeanCell`) and a finite `s` with `E₁ ⊆ ⋃_{g ∈ s} g⁻¹ W₀`
(`compact_covered_by_mul_left_translates`). Let `ν` be a Haar measure on `N(𝔸)` (regular by
`Measure.regular_of_isMulLeftInvariant`), `V` a compact identity neighborhood of `N(𝔸)` and `V''`
the compact set of points of `N(𝔸)` in a compact set containing all `a⁻¹ v a` (`v ∈ V`, `a` in the
chamber), given by `exists_isCompact_conj_unipotent_of_generic` and the closed embedding of
`N(𝔸)`. Let `N₁'` be the image of `N₁` in `N(𝔸)`, `X = a N₁' a⁻¹` and `B₀ = Q W'`.

1. `conj_image_mul_subset_biUnion` and left invariance give
   `vol(a E₁ a⁻¹ W') ≤ #s · vol(X B₀)`.
2. The fibre bound `HaarPacking.measure_mul_mul_le` for the closed subgroup `N(𝔸)` gives
   `vol(X B₀) · ν(V) ≤ ν(X V) · vol(V⁻¹ B₀)`; `X V` and `V⁻¹ B₀` are compact, hence measurable.
3. Every `u` with `a u a⁻¹ ∈ V` lies in `V''`, so `measure_image_mul_le` and the modulus give
   `ν(X V) ≤ δ(a) · ν(N₁' V'')`.

Hence one can take `C₀ = #s · ν(N₁' V'') · vol(V⁻¹ B₀) / ν(V)`, which is finite because the sets
are compact and `ν(V) > 0`.

## The theorem

1. *Packing set.* `G(F)` is discrete (`isDiscrete_rationalSubgroup`), so some open `O ∋ 1` meets
   `G(F)` only in `1`. Choose an open `V₁ ∋ 1` with `V₁ V₁ ⊆ O`
   (`exists_open_nhds_one_mul_subset`) and a compact `W_p ⊆ V₁ ∩ V₁⁻¹` with `1` in its interior
   (`exists_compact_subset`). Then `W_p W_p⁻¹ ∩ G(F) = {1}` and `0 < vol(W_p) < ∞`.
2. *Compact sets.* `D = Ω_N Ω_M` (images of the compact factors of `C`), `W' = D⁻¹ W_p`,
   `KΩ = K Ω` and `E₁ = KΩ · E · KΩ⁻¹`, all compact. Let `C₀` be the constant of
   `exists_measure_conj_mul_le` for `E₁` and `W'`, and `B = (C₀ / vol(W_p))` as a real number.
3. *Reduction to `Z`.* Let `x = z (n m a k) w`, `p = n m`. The central factor `z ∈ A_G` commutes
   with everything (`RestrictionSplitCentre.canonicalSubgroup_le_center`), so
   `x e x⁻¹ = p (a ((k w) e (k w)⁻¹) a⁻¹) p⁻¹` and `G(F) ∩ x E x⁻¹ ⊆ G(F) ∩ Z` with
   `Z = p (a E₁ a⁻¹) p⁻¹`.
4. *Volume of `Z W_p`.* Since `p ∈ D`, `Z W_p ⊆ p · (a E₁ a⁻¹ W')`, so by left invariance and the
   volume bound `vol(Z W_p) ≤ C₀ δ(a) < ∞`.
5. *Count.* The packing lemma `HaarPacking.finite_inter_and_ncard_mul_le` gives that `G(F) ∩ Z`
   is finite with `#(G(F) ∩ Z) · vol(W_p) ≤ vol(Z W_p) ≤ C₀ δ(a)`. Hence `G(F) ∩ x E x⁻¹` is
   finite, and its cardinality is at most `#(G(F) ∩ Z) ≤ (C₀ / vol(W_p)) δ(a)`. Passing from
   `ℝ≥0∞` to `ℝ` uses that the right side is finite (`ENNReal.toReal_mono`).

## Helper modules

The proof uses four modules, each with its own Markdown page:
`Langlands.Analysis.HaarPacking` (packing and fibre bounds),
`Langlands.GroupScheme.Dynamic.RingPointOpenCell` (the opposite cell on points over a local
topological algebra), `Langlands.Global.AdelicArchimedeanTripleCell` (assembly of the
archimedean cells into an identity neighborhood of `G(𝔸)`) and
`Langlands.Global.AdelicSiegelArchimedeanCell` (the archimedean open cell of a Siegel setup).

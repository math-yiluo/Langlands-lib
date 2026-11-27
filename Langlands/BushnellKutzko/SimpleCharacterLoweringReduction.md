# Lowering the simple-character level: the refinement argument

`SimpleCharacterLoweringReductionStatement` says that the published proposition
`SimpleCharacterLoweringStatement` (Bushnell and Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (3.5.9), printed pp. 121–122, PDF pp. 133–134) follows from
eight published propositions. The literature ID is `bushnell-kutzko-1993-admissible-dual-gln`,
with SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
`simpleCharacterLoweringReduction` proves it.

The premises are `SimpleStratumGroupPropertiesStatement` ((3.1.14)–(3.1.15)),
`SimpleCharacterRestrictionStatement` ((3.2.4), (3.2.5), (3.3.18), (3.3.21)),
`SimpleCharacterChoiceStatement` ((3.3.20)), `SimpleCharacterIntertwiningStatement` ((3.3.2),
(3.3.17)), `SimpleCharacterPairingStatement` ((3.4.1)), `SimpleCharacterCoherenceStatement`
((3.5.8)), `SimpleCharacterCovarianceStatement` ((3.3.9)) and
`PureStratumSimpleApproximationStatement` ((2.4.1)). The last one supplies a defining
sequence for the new stratum.

Two steps of the source's proof are results of other modules:

- `SimpleCharacterNormalizerRestrictionStatement`, defined in
  `SimpleCharacterNormalizerRestriction`, is (3.5.10), printed p. 122, together with the
  normalization of `H^m` used with it on p. 121. The theorem
  `simpleCharacterNormalizerRestrictionReduction` of that module derives it from the
  restriction, intertwining and conjugation-formula statements; the proof of
  `simpleCharacterLoweringReduction` applies it to the corresponding premises.
- `SimpleStratumIntertwinedRefinementStatement`, defined and proved
  (`simpleStratumIntertwinedRefinement`) in `SimpleStratumIntertwinedRefinement`, is the
  refinement step on p. 122: if `ψ_b` on `U^m(𝔅_β)` is intertwined by `B_β^×` for a simple
  `[𝔄,n,m,β]` and `b ∈ 𝔓^{−m}`, then some simple `[𝔄,n,m,β']` on the same chain has
  `β' ≡ β + b (mod 𝔓^{1−m})`. Its proof combines (2.4.11) over `F[β]` with the refinement
  theorem (2.2.8) for a nonzero derived coset and with the conjugation of (2.2.1) for the zero
  derived coset; simplicity at index `m` comes from the critical-exponent formula of
  (2.2.8)(ii).

## The proof

The first assertion of (3.5.9) is `simpleCharacterLoweringGroupsReduction` from
`SimpleCharacterLoweringGroups`. For the second assertion write `m = i + 1`.
`exists_equivalent_simpleCharacterPairs_pred_eq` follows the refinement argument of the
source (printed pp. 121–122):

1. Equal pairs at depth `m` give a common character `θ₀` on `H^{m+1}`
   (`simpleCharacters_correspond_of_pairs_eq`). The restriction statement lifts it to
   `θ ∈ C(𝔄,i,β₁)` and `φ ∈ C(𝔄,i,β₂)`, on the common group `H^m`.
2. The quotient `χ = φ/θ` is trivial on `H^{m+1} = H^m ∩ U^{m+1}(𝔄)`, by the exact carriers of
   the subgroup statement. `exists_elementCharacter_eq_of_trivial_on_succ` from
   `UnitFiltrationCharacterExtension` gives `b ∈ 𝔓^{−m}` with `χ = ψ_b` on `H^m`.
3. Let `t ∈ B_{β₁}^×`. It intertwines `θ₀`, so it lies in the intertwining double coset
   `Y B_{β₂}^× Y` of `θ₀` as a character of `β₂` at depth `m`: `t = a s c`. The factors `a`
   and `c` normalize `θ₀` (`simpleCharacterIntertwiningFactor_subset_normalizer`), lie in
   `U^1(𝔄)` (`simpleCharacterIntertwiningFactor_subset_unitFiltration_one`), and by
   (3.5.10) (`SimpleCharacterNormalizerRestrictionStatement`) normalize `H^m` and fix `θ` on
   `U^m(𝔅_{β₁})`. Elements of `U^1(𝔄)`
   normalizing `H^m` fix `χ`, because their commutators with `H^m` lie in `H^{m+1}`
   (`LatticeChain.commutator_mem_unitFiltration_succ`). The element `s ∈ B_{β₂}^×` intertwines
   `φ`, and `t` intertwines `θ`. Comparing `φ = θχ` at `cyc⁻¹` and at
   `s(cyc⁻¹)s⁻¹ = a⁻¹(tyt⁻¹)a` gives `χ(tyt⁻¹) = χ(y)` for `y, tyt⁻¹ ∈ U^m(𝔅_{β₁})`. Hence
   `ψ_b` satisfies the hypothesis of `SimpleStratumIntertwinedRefinementStatement`.
4. `simpleStratumIntertwinedRefinement` gives a simple `[𝔄,n,m,β₁']` with
   `β₁' − β₁ − b ∈ 𝔓^{1−m}`. Then
   `β₁' − β₁ ∈ 𝔓^{−m}`, which is the equivalence of the strata at index `m`.
5. The second clause of the choice statement ((3.3.20)) identifies `H^m(β₁')` with `H^m(β₁)`
   and `C(𝔄,i,β₁')` with `C(𝔄,i,β₁)ψ_{β₁'−β₁}`. On `H^m ⊆ U^m(𝔄)` the functions `ψ_{β₁'−β₁}`
   and `ψ_b` agree, so `φ = θψ_b ∈ C(𝔄,i,β₁')`. Coherence at depth `i` then gives
   `C(𝔄,i,β₁') = C(𝔄,i,β₂)`, and `characterPair_image_eq_iff` turns this into the equality of
   the sets of pairs.

If the first stratum has no defining sequence, neither has the second, because the
restriction statement makes the sets of simple characters nonempty. All the sets of pairs are
then empty, and `β₁' = β₁` works.

The Lean argument is uniform in `m`: it applies the refinement step for every `m ≥ 1`.
The source obtains the equivalence directly when `⌊n/2⌋ ≤ m − 1` (printed p. 121) and uses
the refinement argument only below that range, and it concludes with (3.5.7) where the Lean
proof uses coherence (3.5.8). The module `SimpleCharacterLoweringSets` treats the cases
`⌊n/2⌋ ≤ m − 1` and `2m ≤ finiteCriticalDepth L n β₁` (which is `−k₀(β₁,𝔄)` for nonscalar
`β₁` and `n` for scalar `β₁`) without (3.5.10) and the refinement step.

## Helpers

`characterNormalizer_eq_of_agree` and `inv_mem_characterNormalizer` concern normalizers of
characters. `Stratum.IsSimple.lt_simpleCriticalDepth` bounds the index of a simple stratum by
its critical depth. `LatticeChain.commutator_mem_unitFiltration_succ` bounds commutators with
`U^1(𝔄)`.

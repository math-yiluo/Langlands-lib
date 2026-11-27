# Simple characters one step below a common depth

`SimpleCharacterLoweringOuterCasesReductionStatement` is the second assertion of
Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), (3.5.9), printed pp. 121–122 (PDF pp. 133–134), in two of its cases. The
literature ID is `bushnell-kutzko-1993-admissible-dual-gln`, with SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

The statement assumes eight published propositions:
`SimpleStratumGroupPropertiesStatement` ((3.1.14)–(3.1.15)),
`SimpleCharacterRestrictionStatement` ((3.2.4), (3.2.5), (3.3.18), (3.3.21)),
`SimpleCharacterChoiceStatement` ((3.3.20)), `SimpleCharacterIntertwiningStatement`
((3.3.2), (3.3.17)), `SimpleCharacterPairingStatement` ((3.4.1)),
`SimpleCharacterCoherenceStatement` ((3.5.8)),
`SimpleCharacterCentralizerDeterminantStatement` (the determinant part of (2.4.11) on
a simple character domain) and `SimpleCharacterInvariantsStatement` ((3.5.1)).

Its conclusion concerns a nonarchimedean local field `F`, an `F`-vector space `V`,
an additive character `ψ_F` satisfying `IsBKAdditiveCharacter`, a lattice chain `L`
with hereditary order `𝔄`, an integer `n` and a natural number `m ≥ 1`. Let
`[𝔄,n,m,β₁]` and `[𝔄,n,m,β₂]` be simple strata on `L` with equal sets
`simpleCharacterPairs` at depth `m`. Write `r` for the finite critical depth
`finiteCriticalDepth L n β₁` of `β₁`: it is `−k₀(β₁,𝔄)` when `β₁` is not scalar, and it is the
level `n` when `β₁` is scalar (where `−k₀(β₁,𝔄)` is infinite in the source: (1.4.6), printed
p. 36, and (3.1.6)–(3.1.7), printed p. 90). If `⌊n/2⌋ ≤ m − 1` or `2m ≤ r`, there is a simple
stratum `[𝔄,n,m,β₁']` on `L`, equivalent to `[𝔄,n,m,β₁]`, whose pairs at depth `m − 1`
equal those of `[𝔄,n,m,β₂]`. The proof is `simpleCharacterLoweringOuterCasesReduction`.
The remaining case is `m − 1 < ⌊n/2⌋` and `r < 2m`, where the source uses the
refinement argument with (2.2.8) and (3.5.10).

## The two cases

**High depth** (`simpleStratum_equivalent_of_pairs_eq_of_half_le`). If
`⌊n/2⌋ ≤ m − 1`, take `β₁' = β₂`. The proved `simpleCharacterHighIndex` describes the
common character at depth `m`: it is `ψ_{β₁}` and also `ψ_{β₂}` on
`H^{m+1} = U^{m+1}(𝔄)`. Hence `ψ_{β₂−β₁}` is trivial on `U^{m+1}(𝔄)`. Both elements lie in
`𝔓^{−n}`, so the proved `additiveDuality` gives `β₂ − β₁ ∈ 𝔓^{−m}`, which is the
equivalence of the strata at index `m`. This is the case "`m ≥ [n/2] + 1`" of the source.

**Low depth** (`simpleCharacterPairs_pred_eq_of_two_mul_le`). If `2m ≤ r`, the stratum
itself works, `β₁' = β₁`. Write `m = i + 1` and let `θ ∈ C(𝔄,i,β₁)` and
`φ ∈ C(𝔄,i,β₂)` restrict to a common character `θ₀` at depth `m`. By
`simpleCharacterLoweringGroupsReduction` the domains `H^m` coincide, and `χ = φ/θ` is trivial
on `H^{m+1}`. Every `t ∈ B_{β₁}^×` intertwines `θ` and `θ₀`. Since `θ₀` is also a simple
character of `β₂`, `t` lies in its double coset `Y B_{β₂}^× Y` at depth `m`. The invariants
statement gives the same critical depth for `β₂`, so by
`simpleCharacterIntertwiningFactor_eq_simpleJLayer` the outer factor `Y` at depth `m` is
contained in the factor at depth `i` (`simpleCharacterIntertwiningFactor_succ_subset`). That
factor normalizes `φ` (`simpleCharacterIntertwiningFactor_subset_normalizer`), and
`mul_mul_mem_characterSelfIntertwining` shows that `t` intertwines `φ`. So `B_{β₁}^×`
intertwines `χ`. The centralizer determinant statement (the relative form of the character
part of (2.4.11) over `F[β₁]`) then makes the restriction of `χ` to
`H^m ∩ B_{β₁}^× = U^m(𝔅_{β₁})` factor through the image of the determinant
`det_{B_{β₁}}` (`factorsThroughCentralizerDet`); `χ` itself is defined on all of `H^m`. The
fibre lemma `simpleCharacter_mul_mem_of_belowCutoff` (the fibre description (3.2.5)) takes
exactly these two properties of `χ`, the factorization on `H^m ∩ B_{β₁}^×` and triviality on
`H^{m+1}`, together with the cutoff `i < r/2`, and gives `φ = θχ ∈ C(𝔄,i,β₁)`. Coherence at depth `i` identifies the
two character sets, and `characterPair_image_eq_iff` turns this into equality of the pairs.

The source obtains the equivalence directly when `⌊n/2⌋ ≤ m − 1` (printed p. 121) and uses
the refinement argument with (2.2.8) only below that range (printed p. 122). In the low-depth
case the argument above does without refinement: the determinant factorization places `φ`
directly in `C(𝔄,m−1,β₁)`.

When the first stratum has no defining sequence, the second has none either, since its
sets of simple characters are nonempty by the restriction statement. Then all the sets of
pairs are empty and `β₁' = β₁` works.

## Helpers

- `DefiningSequenceChoice.atIndex` lowers the index of a stratum and of the first term of a
  defining sequence while keeping the tail definitionally equal (`tail_atIndex`), so that the
  coherence statement, which is stated at the depth equal to the stratum index, applies to
  the same groups and character sets.
- `mem_characterSelfIntertwining_div_of_mem`, `characterSelfIntertwining_eq_of_agree`,
  `characterSelfIntertwining_comp_inclusion`, `characterSet_ndrec_inter_nonempty` and
  `characterSetTwistCorrespondence_of_ndrec_eq` are facts about intertwining sets and about
  character sets on equal subgroups.
- `lt_simpleCriticalDepth_of_lt`, `simpleCharacterIntertwiningFactor_one_mem`,
  `centralizerUnitGroup_subset_selfIntertwining` and `simpleCharacterPairs_eq_empty` record
  elementary consequences of the definitions and of the intertwining statement.

# Reduction of the critical translation

`SimpleCharacterCriticalTranslationReductionStatement` is the implication from
three propositions to `SimpleCharacterCriticalTranslationStatement`, the
conclusion of BK94 (5.3)–(5.6). The three propositions are:

- `SimpleCharacterResidueComparisonStatement`: BK94 Lemma (5.2), with the
  equality `𝔅₁ + 𝔓 = 𝔅₂ + 𝔓` from the proof of BK93 (3.5.1);
- `SimpleCharacterLoweringStatement`: BK93 (3.5.9);
- `NonsplitFundamentalSimpleStatement`: BK93 (2.4.13), used through its clause
  over the integral closure `subfieldIntegers F E`.

The theorem `simpleCharacterCriticalTranslationReduction` proves the
implication. It also uses theorems that the Library proves:
`criticalDerivedStratum` (BK93 (2.4.1)(iii)), `refinement` (BK93 (2.2.8)),
`stratumEquivalence` and `tameCorestriction`.

## Proof

Let `T₁ = [𝔄,n,m+1,γ₁]` and `T₂ = [𝔄,n,m+1,γ₂]` have the same depth-`m` pairs.
Let `S₁ = [𝔄,n,m,β₁]` be simple with `β₁ − γ₁ ∈ 𝔓^{−(m+1)}` and
`k₀(β₁) = −(m+1)`.

1. **Depth zero** (`exists_depthZero_of_pairs_eq`). Apply
   `SimpleCharacterLoweringStatement` at the levels `m, m−1, …, 1`, lowering the
   index of the strata between steps with `simpleCharacterPairs_congr`. This
   gives a simple `[𝔄,n,0,γ₁*]` with `γ₁* − γ₁ ∈ 𝔓^{−m}` and the depth-zero
   pairs of `γ₂`. Each step replaces a stratum by an equivalent simple one, so
   `stratumEquivalence` keeps `k₀`. Hence `[𝔄,n,m+1,γ₁*]` is simple.
2. **The perturbation.** Put `c = β₁ − γ₁* ∈ 𝔓^{−(m+1)}`. If `c ∈ 𝔓^{−m}`, then
   `[𝔄,n,m,β₁]` and `[𝔄,n,m,γ₁*]` would be equivalent simple strata. Then
   `stratumEquivalence` would give `k₀(β₁) = k₀(γ₁*) < −(m+1)`. Hence
   `v_𝔄(c) = −(m+1)`.
3. **Residue comparison.** `SimpleCharacterResidueComparisonStatement` for
   `γ₁*` and `γ₂` gives (A), (i), (ii) and tame corestrictions `s₁, s₂` with
   `s₁(c) ≡ s₂(c) (mod 𝔓^{−m})`.
4. **The derived strata.** `criticalDerivedStratum`, applied to `[𝔄,n,m+1,β₁]`
   and `[𝔄,n,m+1,γ₁*]`, gives the derived stratum `D₁ = [𝔅₁,m+1,m,s₁(c)]` and a
   simple stratum `C₁ = [𝔅₁,m+1,m,α]` equivalent to it. Here `𝔅₁` is a chain over
   `𝔬_{E₁}` with the lattices of `L`. The derived stratum
   `D₂ = [𝔅₂,m+1,m,s₂(c)]` uses `LatticeChain.extensionChain`.
5. **Residue data of `C₁`** (`simple_residue_data`). Let `R` be the image of
   `E₁[α]` in `End_F(V)`. Its nonzero elements are units of `𝔎(𝔄)`. The element
   `α` carries `L_i` onto `L_{i−(m+1)}`. The integers of `E₁` and the elements
   `y_α` lie in `R ∩ 𝔄`.
6. **`D₁` is nonsplit** (`derived_isNonsplit`). The coset of `D₁` meets
   `α + 𝔓^{−m}`, so it is fundamental by
   `LatticeChain.not_isNilpotent_of_shift`. Its `y_b` is congruent modulo `𝔓`
   to `y_α ∈ R`. Hence `Stratum.isNonsplit_of_residue_domain` applies with the
   image of `R ∩ 𝔄` in `𝔄/𝔓`.
7. **Semisimplicity.** `NonsplitFundamentalSimpleStatement`, applied to `D₁`
   and `C₁`, makes the residue centralizer of `D₁` semisimple. By (A) and
   `exists_order_congr_of_centralizer_eq`, the orders of the two derived chains
   agree modulo `𝔓`. With `s₁(c) ≡ s₂(c)`, `residueCentralizer_map_le` in both
   directions shows that the two residue centralizers have the same image in
   `𝔄/𝔓`. Hence the residue centralizer of `D₂` is semisimple.
8. **`D₂` is nonsplit** (BK94 (5.3)). Its coset lies in `α + 𝔓^{−m}` at the
   level of `F`, so it is fundamental. By (ii), `π₂ = π₁u` with `u ∈ U¹(𝔄)`.
   This gives equal periods (`period_eq_of_primeElement_congr`), and then
   congruent `y_b` (`restrict_fundamentalElement_sub_mem`). So the `y_b` of
   `D₂` is congruent to `y_α ∈ R`. By (i), the integers of `E₂` are congruent
   to integers of `E₁` in `R`. So `derived_isNonsplit` applies again.
9. **Conclusion** (BK94 (5.5)–(5.6)). `NonsplitFundamentalSimpleStatement` for
   `D₂` gives a simple stratum equivalent to `D₂`. Then `refinement` gives a
   simple `[𝔄,n,m,β₂]` equivalent to `[𝔄,n,m,γ₂ + c]`. Finally
   `c − (β₁ − γ₁) = γ₁ − γ₁* ∈ 𝔓^{−m}`.

## Relation to the source

Bushnell and Kutzko, *Simple types in GL(N): computing conjugacy classes*
(1994), §5, printed pp. 132–133 (PDF pp. 145–146), literature ID
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`. BK94 show
(5.3) by comparing characteristic polynomials over the two residue fields. They
show (5.5) by computing the ring `ℛ` of (5.4) twice through the intertwining of
`θ`. The proof here instead compares the residue centralizers of the two
derived strata directly inside `𝔄/𝔓`, using (A) and (iii). It obtains
nonsplitness from the field `E₁[α]`, using (i) and (ii). The inputs from
Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), are (2.2.8), (2.4.1)(iii), (2.4.13) and (3.5.9), printed pp. 56, 65,
75 and 121, literature ID `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

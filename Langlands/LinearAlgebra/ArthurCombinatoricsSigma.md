# Arthur's characterization of `σ` and the vanishing of `∑ ± τ τ̂`

Lean module: `Langlands.LinearAlgebra.ArthurCombinatoricsSigma`. It imports
`Langlands.LinearAlgebra.ArthurCombinatoricsAlternating` (the alternating sum)
and `Langlands.LinearAlgebra.ArthurCombinatoricsCartanInverse` (nonnegativity
of the inverse Cartan block). It changes no published file and states no new
proposition.

It is part of the proof of
`Langlands.ArthurCombinatorics.ArthurCombinatoricsStatement` and
proves two of the six conjuncts, each as its own named theorem:

```lean
theorem Langlands.ArthurCombinatorics.sigmaCharacterizationStatement :
    SigmaCharacterizationStatement.{u}
theorem Langlands.ArthurCombinatorics.tauTauHatVanishingStatement :
    TauTauHatVanishingStatement.{u}
```

## Notation

`P : RootPairing ι ℝ M N` is a finite crystallographic root system with a
base `b`. For `Θ ⊆ b.support`, `ϖ^Θ_k = weightCoordinate P Θ k` (the weights
of `Θ`, zero for `k ∉ Θ`), `H_Θ = levelProjection P Θ H`, and
`W^Θ = (cartanBlock P Θ)⁻¹`, so that `ϖ^Θ_k = ∑_{l ∈ Θ} W^Θ_{kl} α_l` for
`k ∈ Θ` (`weightCoordinate_apply`).

## Auxiliary results

- `card_sdiff_trans`: `|Z \ X| = |Z \ Y| + |Y \ X|` for `X ⊆ Y ⊆ Z`. It is
  used to split signs `(−1)^{|Z \ X|}`.
- `alternatingSum_eq'`: `∑_{A ⊆ Θ ⊆ B} (−1)^{|Θ \ A|}` is `1` if `A = B` and
  `0` otherwise. It follows from `alternatingSum_eq` (exponent `|B \ Θ|`) by
  the sign split above.
- `levelProjection_apply`, `root'_eq_zero_of_mem_rootAnnihilator`,
  `rootAnnihilator_anti` and `root'_levelProjection_eq_zero` unfold the
  definitions: `H_Θ = H − ∑_{j ∈ Θ} ϖ^Θ_j(H) α_j^∨`, the roots `α_i`, `i ∈ Θ`,
  vanish on `rootAnnihilator P Θ` and on `H_Θ`, and `rootAnnihilator P S` is
  contained in `rootAnnihilator P Θ` for `Θ ⊆ S`.
- `cartanBlock_nonpos_of_ne`: the off-diagonal entries of `cartanBlock P Θ`
  are `≤ 0` (Mathlib's `RootPairing.Base.pairingIn_le_zero_of_ne`, through
  `pairing_nonpos_of_ne`).
- `cartanBlock_inv_nonneg'`: `cartanBlock_inv_nonneg` under `[Finite ι]`.
- `half_le_cartanBlock_inv_self`: `W^Θ_{kk} ≥ 1/2`. The diagonal entry of
  `W^Θ · cartanBlock P Θ = 1` gives `1 = 2 W^Θ_{kk} + ∑_{l ≠ k} W^Θ_{kl} A_{lk}`,
  and each `W^Θ_{kl} A_{lk}` is `≤ 0`.
- `weightCoordinate_pos`: if `α_i(Y) ≥ 0` for every `i ∈ Θ` and
  `α_k(Y) > 0`, then `ϖ^Θ_k(Y) ≥ W^Θ_{kk} α_k(Y) > 0`.
- `weightCoordinate_nonpos`: if `α_i(Y) ≤ 0` for every `i ∈ Θ`, then
  `ϖ^Θ_k(Y) ≤ 0`.
- `weightCoordinate_coroot_nonpos`: `ϖ^Θ_k(α_j^∨) ≤ 0` for a simple root
  `j ∉ Θ`, because `ϖ^Θ_k` is a nonnegative combination of the `α_l`, `l ∈ Θ`,
  and `α_l(α_j^∨) ≤ 0` for `l ≠ j`.
- `weightCoordinate_eq_sum_of_subset`: for `Θ ⊆ S ⊆ b.support`,
  `ϖ^Θ_k(Y) = ∑_{j ∈ S} ϖ^S_j(Y) ϖ^Θ_k(α_j^∨)`. Write
  `Y = Y_S + ∑_{j ∈ S} ϖ^S_j(Y) α_j^∨`; `ϖ^Θ_k` vanishes on `Y_S`, which lies in
  `rootAnnihilator P S ⊆ rootAnnihilator P Θ`
  (`weightCoordinate_eq_zero_of_mem_rootAnnihilator`).
- `weightCoordinate_le_of_subset` (comparison of weights): for
  `Θ ⊆ S ⊆ b.support` and `k ∈ Θ`, if `ϖ^S_j(Y) ≥ 0` for every `j ∈ S \ Θ`,
  then `ϖ^Θ_k(Y) ≤ ϖ^S_k(Y)`. In the expansion above the terms `j ∈ Θ` give
  `ϖ^S_k(Y)` (the published `weightCoordinate_coroot`), and the terms
  `j ∈ S \ Θ` are `≤ 0` by `weightCoordinate_coroot_nonpos`.
- `weightCoordinate_levelProjection`: for `Θ ⊆ S ⊆ b.support` and
  `k ∈ S \ Θ`, `ϖ^S_k(H_Θ) = ϖ^S_k(H)`, since `ϖ^S_k(α_j^∨) = 0` for `j ∈ Θ`.

## `sigma_eq`: Lemma 6.1 in the Levi subgroup of `S`

For `Θ₁ ⊆ Θ₂ ⊆ S ⊆ b.support`, `sigma P S Θ₁ Θ₂ H` is `1` if

- (i) `α_i(H_{Θ₁}) > 0` for `i ∈ Θ₂ \ Θ₁`,
- (ii) `α_i(H_{Θ₁}) ≤ 0` for `i ∈ S \ Θ₂`, and
- (iii) `ϖ^S_i(H) > 0` for `i ∈ S \ Θ₂`,

and `0` otherwise. The general `S` is used for `TauTauHatVanishingStatement`.

Proof. Put `H₁ = H_{Θ₁}`, `R = {i ∈ S : ϖ^S_i(H) ≤ 0}`, `A = Θ₂ ∪ R` and
`B = {i ∈ S : i ∈ Θ₁ or α_i(H₁) > 0}`. For `Θ₂ ⊆ Θ₃ ⊆ S`, unfolding the
definitions gives `τ_{Θ₁}^{Θ₃}(H) = [Θ₃ ⊆ B]` and `τ̂_{Θ₃}^S(H) = [A ⊆ Θ₃]`
(the weights `ϖ^S_i` do not depend on `Θ₃`). Hence

`σ = ∑_{A ⊆ Θ₃ ⊆ B} (−1)^{|Θ₃ \ Θ₂|}`.

If `A ⊄ B` the sum is empty. If `A ⊆ B`, `alternatingSum_eq'` evaluates it to
`(−1)^{|A \ Θ₂|}` if `A = B` and `0` otherwise. Unfolding the definitions,
the conditions (i)–(iii) hold exactly when `B = Θ₂` and `A = Θ₂`.

The geometric step is that `A = B` forces `A = Θ₂`. Suppose `k ∈ A \ Θ₂`.
Then `k ∈ R`, so `ϖ^S_k(H) ≤ 0`; and `k ∈ B \ Θ₁`, so `α_k(H₁) > 0`. Every
`α_i`, `i ∈ A = B`, is `≥ 0` on `H₁` (zero on `Θ₁`, positive otherwise), so
`ϖ^A_k(H₁) > 0` by `weightCoordinate_pos`. For `j ∈ S \ A`, `j ∉ R` gives
`ϖ^S_j(H₁) = ϖ^S_j(H) > 0` (`weightCoordinate_levelProjection`). By
`weightCoordinate_le_of_subset`,
`0 < ϖ^A_k(H₁) ≤ ϖ^S_k(H₁) = ϖ^S_k(H) ≤ 0`, a contradiction.

So `σ = 1` when (i)–(iii) hold. Otherwise either `A ⊄ B`, or `A ⊆ B` with
`A ≠ B`, and `σ = 0`. The remaining case `A = B` would give `A = B = Θ₂`
and hence (i)–(iii).

`sigmaCharacterizationStatement` is the case `S = b.support`.

## The vanishing identity

- `tauTauHat_sum_eq_sigma`: for any `Θ_R`, `Θ_P`,
  `∑_{Θ_R ⊆ Θ₁ ⊆ Θ_P} (−1)^{|Θ_P \ Θ₁|} τ_R^{Θ₁}(H) τ̂_{Θ₁}^{Θ_P}(H) =
  (−1)^{|Θ_P \ Θ_R|} sigma P Θ_P Θ_R Θ_R H`. This is the definition of
  `sigma` with `S = Θ_P` and the sign identity
  `(−1)^{|Θ_P \ Θ₁|} = (−1)^{|Θ_P \ Θ_R|} (−1)^{|Θ₁ \ Θ_R|}`.
- `sigma_self_eq_zero`: for `Θ_R ⊊ Θ_P ⊆ b.support`,
  `sigma P Θ_P Θ_R Θ_R H = 0`. By `sigma_eq` it suffices that (ii) and (iii)
  cannot hold together. Choose `k ∈ Θ_P \ Θ_R`. Under (ii) every `α_i`,
  `i ∈ Θ_P`, is `≤ 0` on `H_R` (zero on `Θ_R`), so `ϖ^P_k(H_R) ≤ 0`
  (`weightCoordinate_nonpos`). But `ϖ^P_k(H_R) = ϖ^P_k(H)`
  (`weightCoordinate_levelProjection`), which is `> 0` by (iii).
- `tauTauHatVanishingStatement` combines the two.

## Provenance

- `SigmaCharacterizationStatement` is Arthur, *A trace formula for reductive
  groups I* (1978), Lemma 6.1, p.938, with its proof on pp.938–939
  (registered as `arthur-1978-trace-formula-reductive-groups-I`; PDF page =
  printed page − 910, so PDF pages 28–29). The definition of `σ_1^2` is on
  p.938. The reduction of `σ` to an interval alternating sum follows Arthur's
  proof: his parabolic `R` has `Θ_R = Θ₂ ∪ R` in the notation above. For the
  case `R ≠ P_2` Arthur expands `H` in the coroots and shows all
  coefficients positive. The Lean proof uses instead the comparison of
  weights `weightCoordinate_le_of_subset`. Both arguments rest on the fact
  that weights are nonnegative combinations of simple roots
  (`cartanBlock_inv_nonneg`).
- `TauTauHatVanishingStatement` is the remark after Corollary 6.2 of the same
  paper, p.940 (PDF page 30): the case `P_1 = P_2 ≠ G` of Lemma 6.1, where
  the set described by Lemma 6.1 is empty. The relative form, with `Θ_P`
  in place of `G`, is Lemma 6.1 in the Levi subgroup attached to `Θ_P`. It
  is used in this form in the proof of Lemma 6.3 on the same page.

## Axioms

The module compiles without errors or warnings. The
lake-build inspection (over Library `72480b70`) of `arthurCombinatoricsStatement`, which
depends on both theorems, reports only `propext`, `Classical.choice` and
`Quot.sound`.

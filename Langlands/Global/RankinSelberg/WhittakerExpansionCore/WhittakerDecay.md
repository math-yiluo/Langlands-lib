# Polynomial decay of Whittaker terms in the last row

Module `Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerDecay`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. A helper lemma for half (S) of the Whittaker
expansion (see `Interface`). It is internal to this proof, not taken from the literature. It
makes precise the usual remark that differentiating along an archimedean unipotent column
multiplies a Whittaker term by a character frequency, so smoothness gives rapid decay in the
last row.

Throughout, `V` is a space of functions on `GL_(r+1)(𝔸)` with a family `R` of archimedean
derivatives forming a `WhittakerDecayClass`, `ψ` is a standard additive character, and
`F` satisfies `CompactSpace (AdeleQuotient F)`.

## Definitions

* `wordFamily N f : Option (Fin N → EntryIndex F (r + 1)) → V` sends `none` to `f` and
  `some l` to the word composite `entryWord N l f = R(D_(l 0)) ∘ ⋯ ∘ R(D_(l (N-1))) f`, where
  the `D_s` are the real matrix units of `WhittakerWords`. The family is finite and is fixed
  once `N` and `f` are fixed.

## Main result

* `exists_lastRow_decay`: let `j < r`, `N ∈ ℕ` and `C` a compact set of adelic points. There is
  a constant `c ≥ 0`, depending on `j`, `N`, `C` and `ψ` but not on `f`, with the following
  property. Take `f ∈ V`, a real `T ≥ 1`, a natural number `e`, a rational matrix `ρ` with
  `HeightLE F T e ρ`, a point `x ∈ C` and `γ ∈ GL_(j+1)(F)` with last row `ξ`. Then

  `(1 + ‖ξ‖)^N ‖W_f(diag(γ, I) ρ x)‖ ≤ c T^(2N) Σ_o ‖W_(f_o)(diag(γ, I) ρ x)‖`,

  where `f_o = wordFamily N f o` and `‖ξ‖` is the sup norm of the image
  `EqualAnalytic.rowEmbedding F (j + 1) ξ` in `(F_∞)^(j+1)`. Only the size bound in
  `HeightLE` is used, not the denominator `e`.

## Proof

1. Write `ψ(x) = ψ₀(β x)` with `β ≠ 0` (`EqualAnalytic.exists_eq_standardCharacter_mul`). By
   `exists_norm_le_sum_colFrequency` there is `K₀ ≥ 0` with
   `‖ξ_a‖ ≤ K₀ Σ_k |L_(a,k)|` for every index `a ≤ j`. Here `L_(a,k)` is the frequency
   `colFrequency β (padRow γ) w_(a,k)` along the direction `w_(a,k) = Pi.single a e_k`, and
   `e_k` is the lattice basis of the mixed space. By `pi_norm_le_iff_of_nonneg`,
   `‖ξ‖ ≤ K₀ Λ` with `Λ = Σ_p |L_p|`, the sum running over the finite index set
   `p ∈ Fin (j+1) × ChooseBasisIndex`.
2. Fix `p` and let `Z = colConj j (ρ x) w_p`. The entries of `(ρ x)_∞^(±1)` are at most
   `(r+1) T B`. Here `B` bounds the entries of `x_∞^(±1)` on `C` (`exists_archCoord_bound`,
   `norm_archCoord_ratPoint_mul_apply_le`). Hence the entries of `Z` are at most
   `(r+1)((r+1)(τ ω₀) τ)` with `τ = (r+1) T B` and `ω₀ = Σ_k ‖e_k‖`
   (`norm_colConj_apply_le`), which equals `c₅ T²` for a constant `c₅`.
3. By the iterated character derivative `whittaker_pow_deriv_eq`,
   `W_((R_Z)^N f)(g) = (2πi L_p)^N W_f(g)` at `g = diag(γ, I) ρ x`. By `norm_whittaker_pow_le`,
   `‖W_((R_Z)^N f)(g)‖ ≤ (κ c₅ T²)^N S`, where `κ = coordConst` and
   `S = Σ_l ‖W_(entryWord N l f)(g)‖`. Since `2π ≥ 1`, this gives
   `|L_p|^N ‖W_f(g)‖ ≤ (κ c₅ T²)^N S`.
4. From `1 + ‖ξ‖ ≤ (1 + K₀)(1 + Λ)` and the power-mean bound `sum_pow_le_card_pow_mul_sum_pow`,
   applied on `Option (index set)` to the values `1` and `|L_p|`,
   `(1 + ‖ξ‖)^N ≤ (1 + K₀)^N m^N (1 + Σ_p |L_p|^N)`, where `m` is the cardinality of the
   `Option` index set.
5. Multiplying by `‖W_f(g)‖` and inserting step 3 gives
   `(1+‖ξ‖)^N ‖W_f(g)‖ ≤ P (‖W_f(g)‖ + Q T^(2N) S)`. Here `P = (1+K₀)^N m^N`, and
   `Q = (#index set) (κ c₅)^N`. Since `T^(2N) ≥ 1`, this is at most
   `P (1 + Q) T^(2N) (‖W_f(g)‖ + S)`. Finally `‖W_f(g)‖ + S` is the sum over `wordFamily`
   (`Fintype.sum_option`). So `c = P (1 + Q)`.

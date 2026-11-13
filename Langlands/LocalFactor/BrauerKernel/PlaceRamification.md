# Ramification and conductors of completions in their canonical packages

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. At the finite places other
than the distinguished one, Deligne's global argument (1973, proof of Lemma 4.12) uses that almost
all places are unramified and that a highly ramified twist makes the remaining epsilon factors
behave stably (Lemmas 4.15 and 4.16). The published local lemmas are stated for the canonical
realizations of p-adic fields, while the global characters live on completions of number fields.
This unit translates the needed notions. It is elementary and has no separate literature source.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`.

## Results

- `canonicalDiscreteValuation_padicFieldAt`: the normalized discrete valuation of the canonical
  realization of `padicFieldAt w h` (for any `h : residuePrime w = p`) is the valuation of the
  completion `K_w`. Proof: substitute `h`; the canonical valuative relation is that of the
  canonical norm, which is equivalent to the completion valuation (`valued_isEquiv`); the
  completion valuation is onto `ℤᵐ⁰`, so `discreteValuation_eq_of_vle` applies.
- `ramificationIndex_towerPadicField_eq`: if the place `u` of `𝕃` over `z` of `k` has ramification
  index one, then `towerPadicField z u` and `padicField z` have the same absolute ramification index
  (the order of `p`). Proof: both orders are read with the completion valuations, and the
  valuation of the image of `p` in `𝕃_u` is that of `p` in `k_z` raised to the ramification index
  (`valuation_completionMap`).
- `valued_le_exp_neg_one_of_mem_maximalIdeal`, `valued_le_exp_neg_of_mem_maximalIdeal_pow`: an
  element of the `r`-th power of the maximal ideal of the completed integers has valuation at most
  `exp (-r)`. Proof: a non-unit integer has valuation `< 1`, hence `≤ exp (-1)` in `ℤᵐ⁰`; induction
  on `r` through products and sums.
- `isUnramifiedQuasicharacter_quasicharacterAt`: if a Hecke character is unramified at `w`
  (trivial on the completed integral units), its component, read in the canonical realization, is
  an unramified quasicharacter (`adicCompletionIntegers.mem_units_iff_valued_eq_one`).
- `lt_multiplicativeConductor_of_nontrivialOnPrincipalUnits`: if a character of `K_w^×` is
  nontrivial on some unit congruent to `1` modulo the `r`-th power of the maximal ideal (the
  published `NontrivialOnPrincipalUnits w η r` of the character prescription statements), its
  conductor exponent in the canonical realization exceeds `r`: otherwise it would be trivial on the
  principal units of level `r`, which contain that unit.

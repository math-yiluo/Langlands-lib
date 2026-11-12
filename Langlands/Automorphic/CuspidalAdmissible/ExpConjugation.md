# Conjugating exponentials in the adelic group

Module: `Langlands.Automorphic.CuspidalAdmissible.ExpConjugation` (namespace
`Langlands.Global`). Provenance: internal.

- `infiniteOneParameter_eq_expInf`: `exp(tY) = expInf(t · Y)` for a real Lie direction `Y`.
- `expInf_zero`: `expInf 0 = 1`.
- `conj_ofInfinite`, `conj_ofFinite`: conjugating an archimedean (resp. finite) element by an
  adelic `u` only involves the infinite (resp. finite) part of `u` (componentwise equality via
  `ext_infinite_finite`).
- `conj_expInf`: `c⁻¹ exp(Z) c = exp(c⁻¹ Z c)` in coordinates (`NormedSpace.exp_units_conj'`).
- `finite_mem_of_mem_expBox`: an element of `expBox δ L` has finite part in `L` and infinite
  part `exp Z` with `‖Z‖ ≤ δ`.

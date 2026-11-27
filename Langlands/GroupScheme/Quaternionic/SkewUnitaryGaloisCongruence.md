# Transport of special unitary crossed homomorphisms along a congruence

Module: `Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisCongruence`.

For a unit `P` of `M_n(D)`, `unitOver F P R` is its image `1 ⊗ P` in units over `R ⊗ D`; it
is fixed by coefficient maps (`unitMap_unitOver`).

- `gramOver_congr`: `1 ⊗ (P H P*) = (1 ⊗ P)(1 ⊗ H)(1 ⊗ P)*`.
- `conj_mem_suGroup`, `conj_inv_mem_suGroup`: conjugation by `1 ⊗ P` maps `suGroup τ H R`
  onto `suGroup τ (P H P*) R` (and its inverse back); `inv_congr_gram` computes
  `P⁻¹ (P H P*) (P⁻¹)* = H`.
- `IsCoboundaryAt.congr`: coboundary data for `c` and `P H P*` give coboundary data for
  `s ↦ (1 ⊗ P)⁻¹ c s (1 ⊗ P)` and `H`.
- `HasseFor τ H` (over a number field) is the proposition that every locally coboundary
  special unitary crossed homomorphism for `H` over every finite Galois `L/F` is a coboundary
  of an element of `suGroup τ H L`. `HasseFor.congr`: `HasseFor τ H` implies
  `HasseFor τ (P H P*)`. The groups `SU(H)` and `SU(P H P*)` are isomorphic over `F` by
  conjugation, which transports cocycles, local data and primitives.

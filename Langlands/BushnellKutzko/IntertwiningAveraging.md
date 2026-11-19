# Intertwining an eigenvector and a fixed vector by finite averaging

`Langlands.BushnellKutzko.IntertwiningAveraging` supplies the group-theoretic step
used in `FundamentalStratumLevelCore`. It uses Mathlib's quotient and subgroup
index APIs and the cyclic subrepresentation in `Langlands.Representation.FiniteVectors`.

## Intertwining lemma

`exists_forall_conj_mem_eq_one` takes a complex irreducible representation `ρ`
of a group `G`, subgroups `H, J, N`, and a function `χ : G → ℂ`. It assumes

- `H ∩ N` has finite index in `H`, expressed as `N.relIndex H ≠ 0`.
- `H ∩ g J g⁻¹` has finite index in `H` for every `g ∈ G`, expressed using
  `J.comap (MulAut.conj g⁻¹).toMonoidHom`.
- A nonzero `v` satisfies `ρ(h) v = χ(h) v` for all `h ∈ H`, and `χ(h) = 1`
  on `H ∩ N`.
- A nonzero `w` is fixed by `J`.

Then some `g` satisfies `χ(h) = 1` whenever `h ∈ H` and `g⁻¹ h g ∈ J`.
This is the intertwining step in the operator note's proof of Lemma 4.11(i),
printed pp. 15–16 (`operator-numerical-llc-route-2026-11-16`). The Lean proof
constructs a finite character sum from the relative-index hypotheses.

## Proof

1. The eigenvector equation and `v ≠ 0` give multiplicativity and nonvanishing
   of `χ` on `H` and `χ(1) = 1`.
2. `exists_finsupp_sum_eq` writes `v = ∑_g c_g ρ(g) w` with `c` finitely
   supported. `FiniteVectors.self_mem_orbitSpan` places `w` in
   `FiniteVectors.orbitSubrepresentation ρ w`. The subrepresentation is
   nonzero and hence equals the whole representation by irreducibility.
3. Let `T = N ∩ ⋂_{g ∈ supp c} g J g⁻¹`. Each intersection in its definition
   has finite relative index in `H`, so `H ∩ T` has finite index in `H`.
   Its normal core `S` in `H` has finite index as well. The subgroup `S`
   fixes `v` and each `ρ(g) w` in the sum, and `χ` is trivial on `S`.
4. Define `E = ∑_{q ∈ H/S} χ(h_q)⁻¹ ρ(h_q)` using a representative `h_q`
   for each coset. On `S`-fixed vectors the summands depend only on `q`.
   Each summand sends `v` to `v`, so `E v = [H : S]·v`.
5. Suppose the conclusion fails. For each `g ∈ supp c` there is an `h₀ ∈ H`
   fixing `x = ρ(g) w` with `χ(h₀) ≠ 1`, since `g⁻¹ h₀ g ∈ J`. Right
   multiplication by `h₀ S` permutes `H/S` and gives
   `E x = χ(h₀)⁻¹·E x`. Hence `E x = 0` for each such translate. By
   linearity `E v = 0`, contradicting `v ≠ 0` and the nonzero complex scalar
   `[H : S]`.

`relIndex_ne_zero_of_isCompact` supplies the index hypotheses in the topological
application. If `C` is a compact subgroup and `O` is open, `C ∩ O` is open in
`C` and has finite index there by `Subgroup.quotient_finite_of_isOpen`.

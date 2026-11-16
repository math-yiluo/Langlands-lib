# Lattices in the finite adeles

Module `Langlands.Global.RankinSelberg.SchwartzBruhatProof.Lattice`, namespace
`Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof`. It is a supporting module for
the proof of `Langlands.Global.RankinSelbergGlobal.SchwartzBruhatStatement`.

## Provenance

These are internal lemmas. They formalize the standard facts used in Getz–Hahn, *An
Introduction to Automorphic Representations* (2024), §C.3, printed pp.553–554 (registered as
`getz-hahn-2024-automorphic-representations`). The lattices `∏_v ϖ_v^(k_v) 𝒪_v` with
`k_v = 0` for almost all `v` form a neighbourhood basis of zero in `𝔸_f`. A locally constant
compactly supported function on `𝔸_f^n` is therefore a finite combination of indicators of
cosets of one such lattice. The proofs are written for this formalization and do not follow
a printed argument.

## Declarations

- `finiteLattice m` for `m : FinitePlace F →₀ ℤ` is the additive subgroup
  `L_m = {b ∈ 𝔸_f | b_v ∈ L_v(m v) for all v}`. Here
  `L_v(k) = (topologicalData v).additiveLattice k = {x | v(x) ≤ exp k} = ϖ_v^(-k) 𝒪_v`.
  Since `m v = 0` for almost all `v`, this is `∏_v ϖ_v^(-m v) 𝒪_v`. Lemmas:
  `mem_finiteLattice`, `finiteLattice_mono` (monotone in `m`), `isOpen_finiteLattice`,
  `isClosed_finiteLattice` and `isCompact_finiteLattice`.
  - Openness: `L_m` is the intersection of the open set "`b_v ∈ 𝒪_v` for `v ∉ supp m`"
    (`RestrictedProduct.isOpen_forall_imp_mem`) with finitely many open conditions at the
    places of `supp m`.
  - Compactness: `L_m` is closed, and it lies in the compact set `δ⁻¹ 𝒪̂`, the image of the
    integral finite adeles under multiplication by `δ⁻¹`. Here `δ ∈ 𝒪_F \ {0}` lies in the
    fractional ideal `Hecke.latticeIdeal (-m)`, so `δ L_m ⊆ 𝒪̂`.
- `exists_finiteLattice_subset`: every neighbourhood of `0` in `𝔸_f` contains some `L_m`. The
  proof uses the description `RestrictedProduct.nhds_zero_eq_map_structureMap` of the
  neighbourhoods of zero in the restricted product, and Library lattice bases at each place.
- `latticeVec n m = L_m^n` (`AddSubgroup.pi`), with `mem_latticeVec`, `coe_latticeVec`,
  `isOpen_latticeVec`, `isCompact_latticeVec`, `isClosed_latticeVec`, `latticeVec_mono` and
  `exists_latticeVec_subset` (the `L_m^n` form a neighbourhood basis of `0` in `𝔸_f^n`).
- `exists_mem_additiveLattice` (every `x ∈ F_v` lies in some `L_v(k)`) and
  `exists_additiveLattice_pi_of_isCompact` (a compact subset of `F_v^n` lies in some
  `L_v(k)^n`).
- In a commutative topological additive group `G`:
  - `cosetIndicator H a = 1_(a + H)`, valued in `ℂ`;
  - `isLocallyConstant_of_add_invariant`: a function invariant under an open subgroup is
    locally constant;
  - `cosetIndicator_add`: `1_(a+H)` is `H`-invariant. Hence
    `isLocallyConstant_cosetIndicator`, and `hasCompactSupport_cosetIndicator` when `H` is
    compact and open;
  - `exists_invariant_of_basis`: let `L i` be a family of open subgroups forming a
    neighbourhood basis of `0`. A locally constant compactly supported `f` is then invariant
    under one `L j`. Proof: cover the support by finitely many cosets `x + L(i x)` on which
    `f` is constant. Take `L j` inside the intersection of the finitely many `L(i x)`, and
    handle points off the support by symmetry;
  - `exists_eq_sum_cosetIndicator`: a compactly supported `f` invariant under an open `H` is
    `Σ_(a ∈ s) f(a) 1_(a+H)` for a finite set `s` of coset representatives. The support meets
    only finitely many cosets.
- `exists_latticeVec_invariant` and `exists_eq_sum_latticeVec`: these specialize the last two
  results to `𝔸_f^n` with the basis `L_m^n`.

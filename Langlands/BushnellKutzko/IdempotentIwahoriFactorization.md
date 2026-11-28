# Block decompositions attached to an idempotent

The module `Langlands.BushnellKutzko.IdempotentIwahoriFactorization` (namespace
`Langlands.BushnellKutzko.BlockIdempotent`) studies the two-block decomposition of a ring
given by an idempotent `e` and its complement `1 - e`: the corresponding unipotent radicals,
Levi subgroup and contracting elements, and the Iwahori factorization of a group of units of
a lattice order.

The corner and factorization argument follows C. J. Bushnell and P. C. Kutzko, *The
admissible dual of GL(N) via compact open subgroups* (1993),
`bushnell-kutzko-1993-admissible-dual-gln`, (7.1.14)–(7.1.15), printed pp. 213–214 (PDF page =
printed page + 12), where it gives the Iwahori decomposition of `J(β, 𝔄)` relative to the
parabolic of an `E`-decomposition subordinate to `𝔅` in the sense of (7.1.1)–(7.1.2), printed
p. 208, with unipotent parts in `J^1(β, 𝔄)`. The module proves a formal two-block version: for
an idempotent `e` of the `𝔬_F`-algebra `R` (in the application `R = 𝔍(β, 𝔄)`) satisfying the
radical-corner condition `e x (1 - e), (1 - e) x e ∈ 𝔓` for all `x ∈ 𝔄`, the group
`J = U(𝔄) ∩ R` factors as `(J ∩ U)(J ∩ M)(J ∩ U⁻)` and `J ∩ U^±` lie in `U^1(𝔄)`. The condition
is a hypothesis: membership of `e` in the centralizer order alone does not give it. A
decomposition satisfying it need not be subordinate in the sense of BK93: grouping the
summands of a subordinate decomposition into two blocks keeps the radical-corner condition,
since each corner across the grouping is a sum of off-diagonal corners, but for
`e(𝔅 | 𝔬_E) = 3` the grouping `V^1 ⊕ (V^2 ⊕ V^3)` of the decomposition (5.5.2) has two blocks,
whereas by (7.1.1) the number of blocks of an `E`-decomposition subordinate to `𝔅` divides
`e(𝔅 | 𝔬_E)`. The factorization is in the order
upper–Levi–lower; the order lower–Levi–upper of (7.1.14) follows by inversion.

## Groups of an idempotent (any ring `A`)

- `upperGroup e`: the units `g` with `g e = e` and `(1 - e) g = 1 - e`, that is `g = 1 + y`
  with `y = e y (1 - e)`; `lowerGroup e = upperGroup (1 - e)`; `leviGroup e`: the units
  commuting with `e`. `mem_upperGroup`, `mem_leviGroup` unfold the definitions.
- `sub_one_eq_of_mem_upperGroup`, `sub_one_mul_sub_one_of_mem_upperGroup`,
  `val_inv_of_mem_upperGroup`: for `g ∈ upperGroup e`, `g - 1 = e (g - 1)`,
  `(g - 1) e = 0`, `(g - 1)² = 0` and `g⁻¹ = 1 - (g - 1)`.
- `contraction he c hc = c e + (1 - e)` for an idempotent `e` and a central unit `c`
  (`inv_comm_of_comm`: its inverse is also central), with value lemmas `val_contraction`,
  `val_contraction_inv`.
- `val_conj_upper`, `val_conj_lower`, `pow_conj_upper`, `pow_conj_lower`: conjugation by
  `ζ^r` (resp. `ζ^{-r}`) maps `upperGroup e` (resp. `lowerGroup e`) into itself and
  multiplies `g - 1` by `c^r`; `contraction_comm_levi`: `ζ` commutes with `leviGroup e`.
- `IsComplementary e f` (`e + f = 1`, `e² = e`, `f² = f`, `e f = f e = 0`) and
  `IsComplementary.levi_comm`: if `D` inverts the corner `f x f` in `f A f`, then
  `(1 - e x f D) x (1 - D f x e)` commutes with `e`.

## Lattice orders

Let `𝓛` be an `𝔬_F`-lattice chain, `R ⊆ 𝔄 = 𝓛.order` an `𝔬_F`-subalgebra and `J` a subgroup
with `g ∈ J ↔ g ∈ U(𝔄) ∧ g ∈ R`.

- `unitOfSqZero`, `unitOfSqZero_mem`, `exists_mem_of_mem_endFiltration_one`: units `1 + y`
  for `y² = 0` or `y ∈ 𝔓 = End^1(𝓛)`, and their membership in `J`.
- `exists_factor` (Iwahori factorization): if `e ∈ R` is idempotent and `e x (1 - e)`,
  `(1 - e) x e ∈ 𝔓` for all `x ∈ 𝔄`, then every `j ∈ J` is `u m l` with `u ∈ J ∩ upperGroup e`,
  `m ∈ J ∩ leviGroup e`, `l ∈ J ∩ lowerGroup e`. Proof: with `x = j`, `x' = j⁻¹`, the elements
  `1 - (f x e)(e x' f)` and `1 - (f x' e)(e x f)` (`f = 1 - e`) lie in `U^1(𝔄)` and in `R`,
  hence are units of `J` commuting with `e`; they give a two-sided inverse `D` of the corner
  `f x f` in `f R f`. Then `u = 1 + (e x f) D`, `l = 1 + D (f x e)` and `m = u⁻¹ j l⁻¹`, and
  `levi_comm` shows that `m` commutes with `e`.
- `scalarUnit a`: the scalar unit `a · 1`, central (`val_scalarUnit`, `scalarUnit_comm`).
- `mem_of_mem_upperGroup`: an element of `upperGroup e` with `g - 1 ∈ R` lies in `J`;
  `mem_unitFiltration_one_of_mem_upperGroup`: an element of `J ∩ upperGroup e` lies in
  `U^1(𝔄)` when the corners `e x (1 - e)` of `𝔄` lie in `𝔓`.
- `exists_pow_smul_mem`: if `F` is a nonarchimedean local field and an `𝔬_F`-submodule `M` of
  `End_F(V)` spans it over `F`, then `ϖ^r • y ∈ M` for some `r`.
- `pow_smul_mem_endFiltration`: `ϖ^r End^k(𝓛) ⊆ End^{k + e(𝓛) r}(𝓛)`.
- `pow_conj_mem_unitFiltration`: with `ζ = ϖ e + (1 - e)` and a second lattice chain `𝓛'`
  such that `End^N(𝓛) ⊆ End^m(𝓛')`, conjugation by `ζ^r` maps `J ∩ upperGroup e` into
  `U^m(𝓛')` as soon as `N ≤ e(𝓛) r`.

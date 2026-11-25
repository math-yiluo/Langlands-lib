# Moy's reduction: cosets containing a nilpotent element (Bushnell 1987, Theorem 1)

Module `Langlands.BushnellKutzko.MoyReduction`. It imports
`Langlands.BushnellKutzko.SplittingBasis`. It is an
internal step of the proof of T2 (`SupercuspidalSwanLevelStatement`). It is also the algebraic input to
Bushnell (1987), Theorem 2′(ii): at a hereditary order that attains the normalized level, every
character occurring in the representation gives a fundamental stratum.

## Main result

`LatticeChain.exists_latticeChain_of_pow_mem 𝓛 hx hn hxy`. Let `F` be a nonarchimedean local
field, `ι` a finite type, and `𝓛` an `𝔬_F`-lattice chain in `F^ι` with period
`e = 𝓛.period`. Let `j ∈ ℤ` and `x ∈ 𝔓^j(𝓛)` (`hx : x ∈ 𝓛.endFiltration j`). Suppose that the
coset `x + 𝔓^{j+1}(𝓛)` contains an element `y` (`hxy : y - x ∈ 𝓛.endFiltration (j + 1)`) with
`y^n ∈ 𝔓^{nj+1}(𝓛)` for some `n ∈ ℕ` (`hn : y ^ n ∈ 𝓛.endFiltration (n * j + 1)`). Then there
are an `𝔬_F`-lattice chain `𝓜` in `F^ι`, with period `e' = 𝓜.period`, and an integer `j'` such
that:

- every `z` with `z - x ∈ 𝔓^{j+1}(𝓛)` lies in `𝔓^{j'}(𝓜)`, i.e. `x + 𝔓^{j+1}(𝓛) ⊆ 𝔓^{j'}(𝓜)`;
- `j · e' < j' · e`, i.e. `j / e < j' / e'`.

The corollary `LatticeChain.exists_latticeChain_of_isNilpotent 𝓛 hx hy hxy` has the same
conclusion when the coset contains a nilpotent `y` (`hy : IsNilpotent y`): if `y^n = 0`, then
`y^n ∈ 𝔓^{nj+1}(𝓛)`.

Here `𝔓^j(𝓛)` is the published `LatticeChain.endFiltration`:
`{x ∈ End_F(F^ι) : x L_i ⊆ L_{i+j} for all i}`.

## Provenance

This is Bushnell (1987), *Hereditary orders, Gauss sums and supercuspidal representations of
GL_N*, Theorem 1, printed p. 192 (conjectured by Moy). Bushnell–Kutzko (1993) quote it as
(2.3.1). Bushnell's hypothesis is a nilpotent element of the coset (the corollary
`exists_latticeChain_of_isNilpotent`). His Lemma 2.1 (printed pp. 192–193) shows that, after
scaling so that `0 ≤ j ≤ e - 1`, this is equivalent to `x^n ∈ 𝔓^{nj+1}` for some `n ≥ 1`. His
proof then uses only that condition, in Lemma 2.4. `exists_latticeChain_of_pow_mem` takes the
condition for any `y` in the coset as its hypothesis. No scaling is needed, and Bushnell's
nilpotent-lifting Lemma 2.2 is not used.

Bushnell states the theorem for hereditary orders `𝔄, 𝔄'` with radicals `𝔓, 𝔓'` and
`e = e(𝔄)`, `e' = e(𝔄')`. Here the theorem is phrased directly in terms of the lattice
chains. The proof works with `𝔓^j(𝓛) = End^j_𝔬(𝓛)` as defined in BK93 (1.1.2), printed
p. 20. For the associated order `𝔄(𝓛)`, the chain period is `e(𝔄)`.

The Lean proof follows Bushnell's §2 (printed pp. 194–195): the operator `I`, the lattices
`ϖ^k I^l(L)`, and the comparison `e m ≥ a j + 1`. It differs from Bushnell in three places.
- Lemma 2.4 is proved through the congruence `I^k(L) ≡ y^k L` (step 3), for any `y` in the
  coset with `y^n ∈ 𝔓^{nj+1}`, instead of Bushnell's expansion of products.
- Bushnell takes `a` minimal and counts lattices in segments to get period `a` and `j' = m`. The
  Lean proof does not need a minimal `a`: it shows that `I` acts on the new chain as a
  translation of indices by some `c`, and that `a c = e' m`.
- Bushnell first scales `x` so that `0 ≤ j ≤ e - 1`. The Lean proof needs no scaling.

## Proof as implemented

Let `I(L)` be the `𝔬_F`-submodule spanned by the vectors `z v` with `z ∈ x + 𝔓^{j+1}(𝓛)` and
`v ∈ L` (`cosetImage j x L`). Choose a uniformizer `ϖ` and let `ϖ` also denote the unit
`uniformizerAsUnit hϖ` of `F`, acting on submodules pointwise.

1. **Basic properties of `I`.** `I` is monotone (`cosetImage_mono`) and commutes with every
   unit of `F` (`cosetImage_units_smul`). If `L ⊆ L_p` then `I(L) ⊆ L_{p+j}`
   (`cosetImage_le`).
2. **Lower bound.** `exists_mem_endFiltration_apply_eq`: if `v ∈ L_p` and `v ∉ L_{p+1}`, then
   every `w ∈ L_{p+k}` equals `d v` for some `d ∈ 𝔓^k(𝓛)`. The proof takes a basis splitting `𝓛`
   (`exists_basis_splits_both`), picks a coordinate `l₀` of `v` that is not in `L_{p+1}`, and
   uses the rank-one map `u ↦ (β^*_{l₀}(u) / β^*_{l₀}(v)) · w`. Consequently, if `L ⊆ L_p` and
   `L ⊄ L_{p+1}`, then `L_{p+j+1} ⊆ I(L)`: write `w = (x + d) v - x v`
   (`lattice_le_cosetImage`). Steps 1 and 2 together are Bushnell's Lemma 2.3.
3. **Power bound** (Bushnell's Lemma 2.4). `exists_sub_pow_mem`: if `L ⊆ L_p`, every
   `w ∈ I^k(L)` is congruent to `y^k v` modulo `L_{p+kj+1}` for some `v ∈ L`. The proof is by
   induction on `k` and on the span, using `z u - y^{k+1} v = z (u - y^k v) + (z - y)(y^k v)`.
   With `y^n ∈ 𝔓^{nj+1}` this gives `I^n(L) ⊆ L_{p+nj+1}` (`iterate_cosetImage_le_of_pow_mem`;
   the case `y^n = 0` is `iterate_cosetImage_le_of_pow_eq_zero`).
4. **Sandwiched lattices.** `IsSandwiched 𝓛 p M` means `L_{p+1} ⊊ M ⊆ L_p`. Such an `M` is a
   lattice and is comparable with every `L_r`. Its index `p` is unique, and `p ≤ p'` whenever
   `M' ⊆ M` with `M'` sandwiched at `p'`. Moreover `ϖ^k M` is sandwiched at `p + e k`, and
   `ϖ M ⊊ M`. By steps 1–2, `I(M)` is either sandwiched at `p + j` or equal to `L_{p+j+1}`
   (`IsSandwiched.cosetImage_or`).
5. **Return to the chain** (compare Bushnell's Lemma 2.5).
   `exists_iterate_cosetImage_eq_lattice`: from a sandwiched `A`, some `I^t(A)` with `t ≥ 1`
   is a lattice `L_q` of the chain. Otherwise `I^t(A)` would be sandwiched at `p + t j` for
   every `t`, which contradicts step 3 at `t = n`.
6. **A periodic lattice** (Bushnell's (2.6)). `exists_iterate_cosetImage_eq_smul`: starting
   from `L_0`, step 5 gives times `0 = t_0 < t_1 < …` and indices `q_k` with
   `I^{t_k}(L_0) = L_{q_k}`. By pigeonhole on `q_k mod e` there are `k₁ < k₂` with
   `q_{k₂} = q_{k₁} + e m`. With `a = t_{k₂} - t_{k₁} ≥ 1` and `B = L_{q_{k₁}}` this gives
   `I^a(B) = L_{q_{k₁} + e m} = ϖ^m B` (`lattice_add_period_mul`).
7. **The new chain** (Bushnell's (2.7)–(2.8)). `exists_latticeChain_shift` is stated for any
   operator `J` with the properties of `I` from steps 1 and 4 and with `J^a(L_q) = ϖ^m L_q`.
   Let `C = {ϖ^k J^l(B) : k ∈ ℤ, l ∈ ℕ}`.
   - Every member of `C` is sandwiched.
   - `C` is totally ordered. Compare `ϖ^{k₁} J^l(B) = J^l(L_{q + e k₁})` with
     `ϖ^{k₂} J^{l+d}(B) = J^l(ϖ^{k₂} J^d(B))`. The two arguments are comparable by step 4, and
     `J^l` is monotone.
   - `C` is stable under `ϖ^ℤ`, `ϖ` acts strictly decreasingly, and intervals are finite.
     `ϖ^k J^l(B) = ϖ^{k + m⌊l/a⌋} J^{l mod a}(B)`, and the sandwich indices bound the exponent.
   - `exists_latticeChain_range_eq` then gives a lattice chain `𝓜` whose lattices are exactly
     `C`. It enumerates `C` by `ℤ` using Mathlib's `orderIsoIntOfLinearSuccPredArch`
     (`exists_strictMono_int_range_eq`), and the period comes from the translation by which
     `ϖ` acts (`exists_shift_of_strictMono`).
   - `J` maps `C` onto `C` and is strictly monotone on it, because `J^a = ϖ^m` on `C`. By
     `exists_shift_of_strictMono`, `J(M_t) = M_{t+c}` for some `c ∈ ℤ`. Comparing
     `J^a(M_0) = M_{a c}` with `ϖ^m M_0 = M_{e' m}` gives `a c = e' m`.
8. **Conclusion** (`exists_latticeChain_of_pow_mem`). Take `J = I` and `j' = c`. Each `z`
   in the coset satisfies `z M_t ⊆ I(M_t) = M_{t+c}`, so `z ∈ 𝔓^c(𝓜)`. For the inequality,
   step 3 iterated gives `I^{n a}(L_q) ⊆ L_{q + a(nj+1)}`. By step 6,
   `I^{a n}(L_q) = ϖ^{m n} L_q = L_{q + e m n}`, so `a(nj + 1) ≤ e m n`. Hence `a j < e m`:
   for `n ≥ 1` divide by `n`; for `n = 0` the inequality reads `a ≤ 0`, which contradicts
   `a ≥ 1`. Multiplying by `e' > 0` and using `a c = e' m` gives `a · j e' < a · c e`, so
   `j e' < c e`. The corollary `exists_latticeChain_of_isNilpotent` applies this with `y^n = 0`.

## Other declarations

- Order theory: `exists_strictMono_int_range_eq` (a nonempty chain with no maximum or minimum
  and finite closed intervals is the range of a strictly monotone `ℤ → β`) and
  `exists_shift_of_strictMono` (a strictly monotone permutation of such a range acts as a
  translation of indices).
- Units acting on submodules: `units_smul_mono`, `units_smul_le_units_smul_iff`,
  `units_smul_lt_units_smul_iff`, `uniformizerAsUnit_smul_eq` (`ϖ L = 𝔭 L`), and
  `lattice_add_period_mul` (`L_{q + e m} = ϖ^m L_q`).
- Iterates: `iterate_zpow_smul_comm` and `iterate_mul_eq_zpow_smul`, for any map commuting with
  the powers of a group element. Also `iterate_cosetImage_units_smul`.
- `mem_endFiltration_of_sub_mem` (the coset lies in `𝔓^j`), `pow_mem_endFiltration_natMul`
  (`y ∈ 𝔓^j ⇒ y^k ∈ 𝔓^{kj}`) and `apply_mem_cosetImage`.
- Sandwich API: `isSandwiched_lattice`, `IsSandwiched.not_le_succ`, `.le_or_le`, `.le_of_le`,
  `.eq`, `.isLattice`, `.zpow_smul`, `.uniformizer_smul_lt` and `.exists_cosetImage`.

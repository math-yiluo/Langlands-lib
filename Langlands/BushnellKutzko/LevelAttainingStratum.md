# A stratum contained at a level-attaining lattice chain is fundamental

Module `Langlands.BushnellKutzko.LevelAttainingStratum`. It imports
`Langlands.BushnellKutzko.MoyReduction` and the published modules
`Langlands.BushnellKutzko.FundamentalStratumDual` and
`Langlands.BushnellKutzko.NormalizedLevel`. It is an internal step of the proof of T2
(`SupercuspidalSwanLevelStatement`).

## Main results

`pow_add_not_mem_of_isNormalizedLevel K n ψ hψ a 𝓛 m b hcont hlev` and its corollary
`not_isNilpotent_of_isNormalizedLevel K n ψ hψ a 𝓛 m b hcont hlev`. Let `K` be a `p`-adic field
(`PadicField p`, with its canonical topology, valuation and topology on `GL_n(K)`). Let
`ψ : AddChar K ℂ` be trivial on the maximal ideal `𝔭_K` (`hψ`); nothing else about `ψ` is assumed.
Let `a` be a class of irreducible admissible complex representations of `GL_n(K)`, `𝓛` an
`𝔬_K`-lattice chain in `K^n`, `m ∈ ℕ`, and `b ∈ End_K(K^n)`. Assume

- `hcont : ContainsStratum K n ψ a 𝓛 m b`: `m ≥ 1`, `b ∈ 𝔓^{-m}(𝓛)`, and some representative of
  `a` has a nonzero vector `v` with `g v = ψ(tr(b(g - 1))) v` for all `g ∈ U^m(𝔄(𝓛))`;
- `hlev : IsNormalizedLevel K n a (m / e(𝓛))`: `m / e(𝓛)` is the least element of
  `normalizedLevelValues K n a`, where `e(𝓛) = 𝓛.period`.

Then for every `y ∈ 𝔓^{1-m}(𝓛)` (`𝓛.endFiltration (1 - m)`):

- `(b + y)^k ∉ 𝔓^{1-km}(𝓛)` for every `k ∈ ℕ` (`pow_add_not_mem_of_isNormalizedLevel`; in Lean
  the filtration index is `k * (-m) + 1`);
- in particular `b + y` is not nilpotent (`not_isNilpotent_of_isNormalizedLevel`). That is, the
  stratum `[𝔄(𝓛), m, m - 1, b]` is fundamental in the sense of BK93 p. 57.

For `y = 0`, the first conclusion and `LatticeChain.list_prod_not_mem` show that a
product of `k` elements of the coset stays outside `𝔓^{1-km}(𝓛)`. This is used for the
conductor lower bound. The second conclusion is the condition of the Library's
`Stratum.IsFundamental` for the chain `𝓛` and stratum parameters `m, m - 1, b`.

## Provenance

This is Bushnell (1987), *Hereditary orders, Gauss sums and supercuspidal representations of
GL_N*, Theorem 2′(ii), printed pp. 196–197, for strata given by an element `b` rather than by a
character `θ` of `U^m/U^{m+1}`. Bushnell's conclusion is that the stratum is fundamental
(`not_isNilpotent_of_isNormalizedLevel`). The stronger `pow_add_not_mem_of_isNormalizedLevel`
is what his proof gives, because his proof of Theorem 1 uses only the power condition (his
Lemma 2.1 and Lemma 2.4); it is not stated in Bushnell (1987). Bushnell assumes that `f(𝔄', π) ≥ 1` for every hereditary
order `𝔄'` and that `f(𝔄, π)/e(𝔄)` is minimal, where `f(𝔄, π)` is the least `f` such that `π`
has a nonzero `U^{f+1}(𝔄)`-fixed vector. Here the minimality is `hlev`, over lattice chains
(the Library's `normalizedLevelValues`), and `m ≥ 1` is part of `ContainsStratum`. Bushnell's
assumption that every `f(𝔄', π)` is positive is not a hypothesis: it follows from `hlev` and
`m ≥ 1`, and the proof does not use it. The proof uses Bushnell's
Theorem 1 (BK93 (2.3.1), printed p. 57), in the lattice-chain form of `MoyReduction`, with the
power condition as hypothesis (`exists_latticeChain_of_pow_mem`).

## Proof as implemented

Choose a uniformizer `ϖ`.

1. **Traces of `𝔓^1`** (`LatticeChain.inv_uniformizer_mul_trace_mem`). If `x ∈ 𝔓^1(𝓛)` then
   `ϖ^{-1} tr(x) ∈ 𝔬_K`. In a basis splitting `𝓛` (`exists_basis_splits_both`), each diagonal
   entry `x_kk ≠ 0` satisfies `e · ord(x_kk) ≥ 1` by `le_of_mem_endFiltration`, so `ord(x_kk) ≥ 1`.
   Hence `ψ(tr x) = 1` (`LatticeChain.addChar_trace_eq_one_of_mem_one`).
2. **Duality** (`LatticeChain.endFiltration_one_sub_le`). For lattice chains `𝓛, 𝓜` and
   `a, b ∈ ℤ`, `𝔓^a(𝓛) ⊆ 𝔓^b(𝓜)` implies `𝔓^{1-b}(𝓜) ⊆ 𝔓^{1-a}(𝓛)`. Take `w ∈ 𝔓^{1-b}(𝓜)`
   and a basis splitting `𝓛`. By `elementaryEnd_mem_iff` it suffices to show that each nonzero
   entry `w_kl` has the order required for `𝔓^{1-a}(𝓛)`. If not, the elementary endomorphism
   `E_lk(ϖ^{-ord(w_kl)})` lies in `𝔓^a(𝓛)`, hence in `𝔓^b(𝓜)`. Then
   `w E_lk(ϖ^{-ord(w_kl)}) ∈ 𝔓^1(𝓜)`, and its trace `ϖ^{-ord(w_kl)} w_kl`
   (`trace_mul_elementaryEnd`) has order `0`. This contradicts step 1. The inclusion is
   the instance of trace duality from BK93 (1.1.4), printed p. 22, used in the proof.
3. **Units** (`LatticeChain.unitFiltration_le_of_endFiltration_le`). If `𝔓^c(𝓜) ⊆ 𝔓^d(𝓛)` with
   `d ≥ 1`, then `U^c(𝔄(𝓜)) ⊆ U^d(𝔄(𝓛))`.
4. **Lattice core** (`LatticeChain.exists_latticeChain_of_pow_add_mem`). Let `m ≥ 1`,
   `b ∈ 𝔓^{-m}(𝓛)`, `y ∈ 𝔓^{1-m}(𝓛)` and `(b + y)^k ∈ 𝔓^{1-km}(𝓛)` for some `k`. Moy's
   reduction (`exists_latticeChain_of_pow_mem`, applied to `x = b`, `j = -m`, the element
   `b + y` and `n = k`) gives `𝓜` and `j'` with `b + 𝔓^{1-m}(𝓛) ⊆ 𝔓^{j'}(𝓜)` and `-m e(𝓜) < j' e(𝓛)`. Put
   `l = max(-j', 0) ∈ ℕ`. Then `l e(𝓛) < m e(𝓜)`, `b ∈ 𝔓^{-l}(𝓜)`, and subtracting `b` gives
   `𝔓^{1-m}(𝓛) ⊆ 𝔓^{-l}(𝓜)`. Step 2 turns this into `𝔓^{l+1}(𝓜) ⊆ 𝔓^m(𝓛)`. The nilpotent
   case is `LatticeChain.exists_latticeChain_of_isNilpotent_add` (if `(b + y)^k = 0`, then
   `(b + y)^k ∈ 𝔓^{1-km}(𝓛)`).
5. **Representation part** (`pow_add_not_mem_of_isNormalizedLevel`). Suppose
   `(b + y)^k ∈ 𝔓^{1-km}(𝓛)` and take `𝓜, l` from step 4. By step 3, `U^{l+1}(𝔄(𝓜)) ⊆ U^m(𝔄(𝓛))`, so the
   eigenvector `v` satisfies `g v = ψ(tr(b(g - 1))) v` for `g ∈ U^{l+1}(𝔄(𝓜))`. There
   `b(g - 1) ∈ 𝔓^{-l}(𝓜) 𝔓^{l+1}(𝓜) ⊆ 𝔓^1(𝓜)`, so step 1 gives `g v = v`. Hence
   `l / e(𝓜) ∈ normalizedLevelValues K n a`. Minimality gives `m / e(𝓛) ≤ l / e(𝓜)`, which
   contradicts `l e(𝓛) < m e(𝓜)`.
6. **Corollary** (`not_isNilpotent_of_isNormalizedLevel`). If `(b + y)^k = 0`, then
   `(b + y)^k ∈ 𝔓^{1-km}(𝓛)`, which step 5 excludes.

## Other declarations

- `ordOf_uniformizer`: `ord(ϖ) = 1`.
- The `p`-adic section declares the canonical instances as named local instances
  (`lvlAttTopologicalSpace`, `lvlAttValuativeRel`, `lvlAttLocalField`, `lvlAttTopologicalSpaceGL`).
  This avoids clashes with automatically named instances when the module is imported next to the
  Library's normalized-level statement modules.

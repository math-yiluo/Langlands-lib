# A coset satisfying the power condition contains a nilpotent element

Module `Langlands.BushnellKutzko.FundamentalStratumPowerCondition`. It imports
`Langlands.BushnellKutzko.MoyReduction` and `Langlands.BushnellKutzko.FundamentalStratumDual`.

## Main result

`LatticeChain.exists_isNilpotent_add_of_pow_mem_endFiltration 𝓛 hx hn`. Let `F` be a
nonarchimedean local field, `V` a finite-dimensional `F`-vector space and `𝓛` an
`𝔬_F`-lattice chain in `V`. Write `𝔓^j(𝓛)` for `𝓛.endFiltration j`. If `x ∈ 𝔓^j(𝓛)`
(`hx`) and `x^n ∈ 𝔓^{nj+1}(𝓛)` for some `n ∈ ℕ` (`hn`), then there is `y ∈ 𝔓^{j+1}(𝓛)` with
`x + y` nilpotent. In other words, the coset `x + 𝔓^{j+1}(𝓛)` contains a nilpotent element.

For a stratum `[𝓛, n, n-1, b]` (so `j = -n`), this says that the stratum is not fundamental in
the sense of the Library's `Stratum.IsFundamental` as soon as `b^k ∈ 𝔓^{1-kn}(𝓛)` for some `k`.

## Provenance

This is the "if" direction of Bushnell, *Hereditary orders, Gauss sums and supercuspidal
representations of GL_N* (1987), `bushnell-1987-hereditary-orders-gauss-sums`, Lemma (2.1),
printed p. 192 (PDF p. 9). Bushnell states it for `0 ≤ j ≤ e(𝓛) - 1` and proves it with
band matrices and his nilpotent-lifting Lemma (2.2). The Lean statement has no restriction on
`j`, and the proof is different: it combines Moy's reduction (Bushnell's Theorem 1, printed
p. 192, in the Library's form `LatticeChain.exists_latticeChain_of_pow_mem`) with a weight
argument.

## Proof as implemented

1. **Two chains** (`LatticeChain.exists_isNilpotent_add_of_mem_both`, in `F^ι`). Let `𝓛, 𝓛''`
   be lattice chains with periods `e, e''` and let `m'' e < m e''`. If
   `b ∈ 𝔓^{-m}(𝓛) ∩ 𝔓^{-m''}(𝓛'')`, then `b + y` is nilpotent for some `y ∈ 𝔓^{1-m}(𝓛)`. The
   proof is the proof of `LatticeChain.exists_isNilpotent_add` in `FundamentalStratumDual`,
   with its character hypothesis replaced by the membership `b ∈ 𝔓^{-m''}(𝓛'')`. Choose a basis
   splitting both chains (`exists_basis_splits_both`). For an entry `b_{lk}` whose elementary
   term is not in `𝔓^{1-m}(𝓛)`, the entry inequality for `𝓛` is an equality, and
   `LatticeChain.le_of_mem_endFiltration` gives the entry inequality for `𝓛''` directly.
   Together with `m'' e < m e''` they give `w(l) < w(k)` for the weight
   `w(k) = e'' ν(β_k) - e ν''(β_k)`. The sum of these terms is nilpotent by
   `isNilpotent_of_lt_weight`, and the remaining terms lie in `𝔓^{1-m}(𝓛)`.
2. **Coordinates** (`LatticeChain.exists_isNilpotent_add_of_pow_mem`, in `F^ι`). Moy's reduction
   `exists_latticeChain_of_pow_mem`, applied to `x` itself, gives a chain `𝓜` and `j'` with
   `x + 𝔓^{j+1}(𝓛) ⊆ 𝔓^{j'}(𝓜)` and `j e(𝓜) < j' e(𝓛)`. Step 1 with `m = -j`, `m'' = -j'`
   and `𝓛'' = 𝓜` gives the nilpotent element.
3. **Transport.** For a linear equivalence `f : V ≃ W`,
   `LatticeChain.conj_mem_endFiltration_linearEquivMap` shows that `x ↦ f x f⁻¹` identifies
   `𝔓^j(𝓛)` with `𝔓^j` of the transported chain `𝓛.linearEquivMap f`, and
   `LatticeChain.period_linearEquivMap` shows that the period is unchanged. The main result
   transports `𝓛` to coordinates along the basis `Module.finBasis F V`, applies step 2, and
   transports the element back; conjugation by `f` is an algebra isomorphism, so it preserves
   nilpotence.

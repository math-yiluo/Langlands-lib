# A trace bound for subextensions of a Galois extension

Helper module for the proof of `TopLayerNormTraceStatement`
(`DeligneHenniartTopLayerProof.md`).

## Setting

Let `K`, `F` and `M` be p-adic fields with algebras `K → F → M` and `K → M`
forming scalar towers compatible with `Padic p`, and `M/K` finite Galois. The
topological data `TK` and `TM` are arbitrary. Write:

- `t = herbrandPsi TM K n` for a natural number `n`;
- `g_i = lowerGroupOrder TM K i` for the order of `G_i ⊆ Gal(M/K)`;
- `j_i = lowerGroupOrder TM F i` for the order of the lower group of
  `Gal(M/F)`, which is `Gal(M/F) ∩ G_i`.

The integral `∫_0^t j_s ds`, with `j_s = j_{⌈s⌉}`, is the published weighted
ramp sum `rampSum (fun i => j_i) N t`, for any `N ≥ t`.

## Main result

`trace_mem_additiveLattice`. Assume:

- `N` is at least the cutoff `ramificationCutoff TM K` and at least `t`;
- `z ∈ F` is nonzero;
- `rampSum j N t < ord_M(z)`.

Then `Tr_{F/K}(z) ∈ TK.additiveLattice (-(n + 1))`, i.e.
`ord_K(Tr_{F/K} z) ≥ n + 1`. In Herbrand's notation the hypothesis is
`ord_F(z) > ψ_{F/K}(n)`. It is a form of the trace estimate of DH81 3.3
(printed p. 103), which describes `Tr_{F/K}` through the different. Here it is
written in `M`, so `F/K` need not be Galois.

## Proof

Inside the proof `F` carries its canonical topological data `TF`. The
conclusion does not mention `TF`.

1. **Different of `F/K`** (`exists_different_exponent`). The different of
   `O_F/O_K` is a nonzero ideal of a discrete valuation ring, hence
   `m_F^d` for some `d`. Hilbert's formula
   (`differentIdeal_eq_maximalIdeal_pow`) applies to `M/K` and to `M/F`, since
   `M/F` is Galois and its `N`-th lower group is trivial. Mathlib's tower
   formula `differentIdeal_eq_differentIdeal_mul_differentIdeal` relates the
   three differents. The extension of `m_F^d` to `O_M` is `m_M^{j_0 d}` by
   `map_maximalIdeal_pow_of_ramificationIndex_eq_mul` and
   `|Gal(M/F)_0| e_F = e_M`. Comparing exponents via
   `coheight_pow_maximalIdeal` gives
   `Σ_{i<N} (g_i - 1) = Σ_{i<N} (j_i - 1) + j_0 d`.
2. **Ramification indices.**
   - `e = ord_F(π_K)` satisfies `e_F = e · e_K`, by
     `ramificationIndex_mul_ord_algebraMap`.
   - `lowerGroupOrder_zero_mul_ramificationIndex` for `M/K` and `M/F` gives
     `g_0 = j_0 e`.
   - `ord_algebraMap_eq` for `M/F` gives `ord_M(z) = j_0 · ord_F(z)`. With the
     hypothesis, `a = ord_F(z) > 0`, so `z ∈ m_F^a`.
3. **Inequality.**
   - `lowerGroupOrder_le_of_tower` gives `j_i ≤ g_i`.
   - `herbrandPhi_eq_sum` and `herbrandPhi (herbrandPsi n) = n` give
     `rampSum g N t = g_0 n`.
   - `sum_ge_add_rampSum`, applied to `c_i = g_i - j_i` with `c_N = 0`, gives
     `Σ_{i<N} (g_i - j_i) ≥ (g_0 - j_0) + rampSum g N t - rampSum j N t`.
   - Hence `j_0 (d + a) > g_0 (n + 1) - j_0 = j_0 (e (n + 1) - 1)`, so
     `d + a ≥ e (n + 1)` and `(d + a) / e ≥ n + 1`.
4. **Trace image.** The published `LocalField.dvrTraceIdeals` (exact trace
   images of ideal powers, with `m_K O_F = m_F^e` and different `m_F^d`) puts
   `Tr_{F/K}(z)` in `m_K^{(d + a)/e}`. The order bound then gives the
   lattice membership through `mem_additiveLattice_neg_of_le_ord`.

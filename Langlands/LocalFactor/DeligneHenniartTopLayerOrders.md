# Orders in a finite extension of p-adic fields

Helper module for the proof of `TopLayerNormTraceStatement`
(`DeligneHenniartTopLayerProof.md`). Every result is proved here and no
hypothesis is added. Throughout, `K` and `M` are p-adic fields
(`PadicField`). `M` is a `K`-algebra compatible with `Padic p`. `TK` and `TM`
are arbitrary topological data. `ord` is the normalized order `TK.ord` or
`TM.ord`, and `e_K = TK.ramificationIndex` and `e_M = TM.ramificationIndex`
are the absolute ramification indices (orders of `p`).

## Order of a base element and Galois invariance

- `ramificationIndex_mul_ord_algebraMap`: for `x ∈ K`,
  `e_K · ord_M(x) = e_M · ord_K(x)`. The image of `x` in `M` has the same
  canonical (spectral) norm as `x` (`Weil.Local.canonicalNorm_map`). The
  published comparison `ord_mul_le_of_canonicalNorm_le`, applied in both
  directions with exponent `1`, gives the two inequalities.
- `ord_algEquiv_apply`: every `σ ∈ Aut_K(M)` satisfies
  `ord_M(σ x) = ord_M(x)`. The proof is the same argument with `M` on both
  sides, and divides by `e_M > 0`.

## The inertia order is the relative ramification index

From here on, `M/K` is Galois and `G = Gal(M/K)` acts on `O_M = TM.Integers`
through `Ramification.Padic.integerAction`. The integer rings carry the
published relative algebra `relativeIntegerAlgebra TK TM`.

- `isGaloisGroup_integers`: `G` is a Galois group of `O_M` over `O_K` in
  Mathlib's sense (`IsGaloisGroup`).
  - The action is faithful because `O_M` has fraction field `M`.
  - It commutes with `O_K`-scalars because automorphisms fix `K`.
  - A `G`-fixed element of `O_M` lies in `K`
    (`IsGalois.mem_range_algebraMap_iff_fixed`). It lies in `O_K` because
    integrality is detected in `M` (`relative_mem_integers_iff`).
- `lowerRamificationGroup_zero_eq_inertia`: the published `G_0`
  (`lowerRamificationGroup TM K 0`) is Mathlib's inertia group
  `(maximalIdeal O_M).inertia G`; both are defined by `σ x - x ∈ m_M`.
- `ramificationIdx_eq_ord_uniformizer`: the ramification index
  `(maximalIdeal O_M).ramificationIdx O_K` equals `ord_M(π_K)`, with `π_K` the
  uniformizer of `TK`. The extension of `m_K` is the principal ideal of `π_K`.
  `Ideal.ramificationIdx'_spec` applies, with ideal powers read through
  `mem_maximalIdeal_pow_iff_ord`.
- `lowerGroupOrder_zero_mul_ramificationIndex`: `|G_0| · e_K = e_M`.
  Mathlib's `Ideal.card_inertia_eq_ramificationIdxIn` gives
  `|inertia| = ramificationIdxIn`, which equals the ramification index of the
  unique prime above (`Ideal.ramificationIdxIn_eq_ramificationIdx`). Its
  hypotheses are discharged as follows.
  - The extension is finite (`NYLL.relativeIntegerStructure`).
  - It is flat: `O_M` is torsion-free over the Dedekind domain `O_K`.
  - The residue fields are finite, hence perfect, so the residue extension
    is separable.

  The previous item and `ramificationIndex_mul_ord_algebraMap` at `π_K` then
  give `ord_M(π_K) · e_K = e_M`.
- `ord_algebraMap_eq`: for `x ∈ K`, `ord_M(x) = |G_0| · ord_K(x)`. This
  combines the first and the previous item and cancels `e_K > 0`.

`lowerGroupOrder TM K 0` is the order of `G_0`. It is the denominator of the
published `herbrandPhi TM K`, so these facts convert Herbrand functions into
orders of elements.

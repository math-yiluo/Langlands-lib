# The trace form of a semisimple algebra and the decomposition `A = z ⊕ z^⊥`

The module `Langlands.HarmonicAnalysis.UnitConjugation.TraceFormPairing` studies, for a
finite-dimensional algebra `A` over a field `F`, the trace form
`B₀(X, Y) = tr_{A/F}(L_{XY})`, `L` the left regular representation (`traceFormPairing`). All
declarations are in the namespace `Langlands.HarmonicAnalysis.UnitConjugation`.

## Results

- `traceFormPairing_comm`, `traceFormPairing_isSymm`: `B₀` is symmetric, since
  `L_{XY} = L_X L_Y` and `tr(L_X L_Y) = tr(L_Y L_X)`.
- `trace_lmul_conj`, `traceFormPairing_conj`: `B₀(uXu⁻¹, uYu⁻¹) = B₀(X, Y)` for every unit `u`,
  because `L_{uWu⁻¹} = L_u L_W L_u⁻¹`.
- `exists_mul_mul_eq_self`: a semisimple ring is von Neumann regular, every `X` has `Y` with
  `X Y X = X`. Proof: the left ideal `A X` has a complement; the projection onto it along the
  complement is `A`-linear, hence right multiplication by `e = p(1) ∈ A X`, `e = Y X`; it fixes
  `X`, so `X = X e = X Y X`.
- `eq_zero_of_isNilpotent_of_commute`: in a semisimple ring a nilpotent element `N` commuting
  with every element is `0`: from `N Y N = N` and commutation, `N = N^{k+1} Y^k` for all `k`.
- `trace_lmul_ne_zero_of_mul_self` shows that `tr(L_e) ≠ 0` for a nonzero idempotent `e`
  in characteristic zero. Mathlib's `LinearMap.IsProj.trace` gives the rank formula
  for the projection `L_e` onto its range. The proof uses
  `LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero` to deduce `L_e = 0` from a
  vanishing trace. Evaluating at `1` would then give `e = 0`.
- `traceFormPairing_nondegenerate`, `isInvariantPairing_traceFormPairing`: for `A` semisimple
  and `F` of characteristic zero `B₀` is nondegenerate, hence an invariant pairing in the sense
  of the Library's `IsInvariantPairing`: for `X ≠ 0` choose `Y` with `XYX = X`; then `XY` is a
  nonzero idempotent and `B₀(X, Y) = tr(L_{XY}) ≠ 0`.
- `centerOrthogonal F A`: the orthogonal `z^⊥` of the center `z` for `B₀`;
  `conj_mem_centerOrthogonal`: it is stable under conjugation;
  `mem_centerOrthogonal_of_isNilpotent`: it contains every nilpotent `N`, because for central
  `Z` the product `ZN` is nilpotent, so `L_{ZN}` is nilpotent and has trace `0`.
- `exists_center_mul_mul_eq`: for central `Z` there is a central `W` with `Z = Z Z W`. The
  descending chain of subspaces `Z^k z` stabilizes by dimension, giving a central `W` with
  `Z^k = Z^{k+1} W`; then `Z - Z Z W = Z (1 - Z W)` is central with
  `(Z (1 - ZW))^{k+1} = Z^{k+1}(1 - ZW)^{k+1} = 0`, hence `0`.
- `eq_zero_of_mem_center_of_mem_centerOrthogonal`, `isCompl_center_centerOrthogonal`: for `A`
  semisimple in characteristic zero, `z ∩ z^⊥ = 0`, hence `A = z ⊕ z^⊥` (Mathlib's
  `LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint`). If `Z ∈ z ∩ z^⊥ ` is nonzero and
  `Z = Z Z W` with `W` central, then `Z W` is a nonzero idempotent and
  `0 = B₀(W, Z) = tr(L_{ZW}) ≠ 0`.
- `finrank_center_lt_finrank_centralizer`: if `A` is not commutative then
  `dim z < dim C_A(N)` for every nilpotent `N`: `C_A(0) = A`, and for `N ≠ 0` the element `N`
  lies in `C_A(N)` but not in `z`.

## Source

The decomposition of a reductive Lie algebra into its center and its derived algebra is used
in Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes
by S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions`, §3.4, Lemma 3.11, printed p. 26
(PDF p. 41): "`g = z + g₁` where `g₁ = [g, g]`". For the trace form `[A, A] ⊆ z^⊥`; this module
works with `z^⊥` directly.

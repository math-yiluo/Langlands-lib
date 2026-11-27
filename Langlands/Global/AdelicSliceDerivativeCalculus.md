# Invariant derivatives of infinite slices and bounded derivatives of height pairings

Module `Langlands.Global.AdelicSliceDerivativeCalculus`, namespace
`Langlands.Global.AdelicGroupPoints`. The infinite adelic points carry the Library's charted space
`smoothChartedSpace F G hsmooth` and Lie group structure `smoothLieGroup F G hsmooth`; `pair F G a b`
is the adelic point with infinite component `a` and finite component `b`.

## Slice derivatives

- `sliceDerivative hsmooth X ψ` is the function `g ↦ (X · ψ(·, finite g))(infinite g)` on the
  actual adelic points: each infinite slice of `ψ` is differentiated in the invariant direction
  `X : smoothModel F d`.
- `sliceDerivative_pair`: the infinite slice of `sliceDerivative hsmooth X ψ` at `b` is
  `groupDirectionalValue X` of the infinite slice of `ψ` at `b`.
- `sliceDerivative_mul_of_add_const`: if the slices of `ψ` are smooth and `ψ (g₀ * g) = ψ g + κ`
  for all `g`, then `sliceDerivative hsmooth X ψ (g₀ * g) = sliceDerivative hsmooth X ψ g`. Proof:
  `g₀ * pair a b = pair (a₀ a) (b₀ b)` for the components `a₀`, `b₀` of `g₀`, so the slice at `b₀ b`
  is the left translate by `a₀⁻¹` of the slice at `b` plus `κ`; the constant disappears by
  `listDirectionalDerivative_add_const` and the translation by `groupDirectionalValue_leftTranslation`.

## Heights

Let `hK : IsIwasawaCompact p K` for a closed subgroup `p : P → G`.

- `IsIwasawaCompact.exists_infinite_factor`: every infinite point is `p(x) · k_∞` with `x` an
  infinite point of `P` and `k_∞` the infinite component of some `k ∈ K`. Proof: factor `(a, 1)` as
  `p(q) k` and take infinite components, using the naturality of `affinePointsTarget`.
- `IsIwasawaCompact.height_pair_eq_add`: if `K` contains the infinite components of its elements
  (as a maximal compact subgroup does, by `IsMaximalCompactSubgroup.mem_iff`), then
  `H_P(a, b) = H_P(a, 1) + H_P(1, b)`. Proof: with `a = p(x) k_∞`, the point `(a, b)` is
  `p((x, 1)) (1, b) (k_∞, 1)` because the infinite and finite factors commute
  (`factors_commute`); then `height_map_mul` and `height_mul_right` give both heights.
- `IsIwasawaCompact.height_ofInfinite_mul`: `H_P(p(x) a, 1) = log_P (x, 1) + H_P(a, 1)`.
- `IsIwasawaCompact.exists_bound_heightPairing_derivative`: if the height pairings are smooth
  (`HasSmoothHeightPairings`) and `K` contains the infinite components of its elements, then for
  every `λ` and every nonempty list `w` of directions there is `M` with
  `‖D_w (a ↦ ⟨λ, H_P(a, b)⟩)(a)‖ ≤ M` for all `a` and `b`. Proof: by `height_pair_eq_add` each slice
  is `s + c_b` with `s(a) = ⟨λ, H_P(a, 1)⟩`, so its nonempty derivatives are those of `s`. By
  `height_ofInfinite_mul`, `s` changes by constants under left translation by the image of the
  infinite points of `P`, and by `exists_infinite_factor` this image times the compact image of `K`
  covers the infinite points. `exists_bound_listDirectionalDerivative_of_quasiInvariant` gives the
  bound.

## Provenance

Internal. Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995), fix a maximal
compact subgroup `K = ∏_v K_v` of `G(𝔸)` in I.1.1 (printed p. 1), impose condition I.1.4 (i) on
it (printed p. 4), and define the height map `m_P` on printed p. 7, still in I.1.4, through the
decomposition `G = P K` that they deduce from I.1.4 (i). The additivity
`H_P(a, b) = H_P(a, 1) + H_P(1, b)` of the infinite and finite contributions is not stated there; it
is the identity `height_pair_eq_add` established in this module for the Library's actual adelic
points and any Iwasawa compact subgroup that contains the infinite components of its elements.

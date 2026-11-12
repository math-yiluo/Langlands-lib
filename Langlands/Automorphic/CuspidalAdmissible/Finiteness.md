# Finite dimension of reproduced cuspidal vectors with a central law

Provenance: internal. This module is the analytic core of Harish-Chandra's finiteness
theorem for cusp forms (Harish-Chandra, *Automorphic forms on semisimple Lie groups*,
Lecture Notes in Math. 62), in the form needed for `GL_n` over a number field `F`. The classical proof bounds cusp forms by their
convolution with an approximate identity and uses rapid decay in Siegel sets. The Lean
route below is self-contained and uses only sup-norm estimates. It uses no `L²` theory and
no Schur lemma.

Notation: `S : OperatorRealization F n`, `ev f := evaluate F n (S.toContinuous f)`,
`A x := AdelicGL.ofInfinite F n (torInf F n x)` and `d := [F : ℚ]`. The archimedean
group `InfiniteAdelicGL F n` carries a Borel measure `μ`, finite on compacts. A *reproduced*
vector `f` for a kernel `κ : InfiniteAdelicGL F n → ℂ` satisfies, for all `g` and
archimedean `h`,

`ev f (g · h) = ∫ ev f (g · z) κ(z⁻¹ h) dμ(z)`.

## Central torus and weights

- `centralTorus F n t`: the archimedean scalar matrix `e^t · 1`, the same at every infinite
  place, as an adelic matrix. `centralTorus_commute`: it is central.
  `absDet_centralTorus`: `|det (centralTorus t)| = (e^{n t})^d`.
- `weight c f g := ‖ev f g‖ · |det g|^{-c}`. Lemmas: `weight_nonneg`,
  `norm_eq_weight_mul` (`‖ev f g‖ = weight · |det g|^c`), and `weight_rational`
  (invariance under rational left translation, from `evaluate_rational` and
  `absDet_rational_mul`).

## Deep cusp absorption

- `exists_deep_absorption F n h L hL hQ hU hU1`: let `a + b = n`, let `L` be an open
  subgroup of `GL_n(𝔸_f)`, `Q` a compact set of adelic matrices and `U` an open
  neighbourhood of `1` in the archimedean group. Then there is `ℓ₀` with the following
  property. Let `x` be a real vector whose block gaps `x(a + r) - x(p)` are all at most
  `-ℓ` with `ℓ ≥ ℓ₀`, and let `q ∈ Q`. Then every left block-unipotent translate
  `u(Y) · A x · q` equals `γ · (A x · q · u) · l` with `γ` rational, `u ∈ U` and `l ∈ L`.
  Proof: write `Y = ξ + δ W` with `ξ` rational and `W` in the compact fundamental set
  (`exists_matrix_decomposition`, `exists_nsmul_conj_blockUnipotent_mem`). The finite part
  of `δ W`, conjugated by the finite part of `q`, lies in `L`. The archimedean part,
  conjugated by `A x`, is rescaled by `e^{x(a+r) - x(p)} ≤ e^{-ℓ}`. A tube-lemma argument
  (`generalized_tube_lemma`) applied to `(s, Z, k) ↦ k⁻¹ u(s Z) k` near `s = 0` makes the
  conjugate by the archimedean part of `q` lie in `U` once `e^{-ℓ}` is small.

## Uniform continuity and the kernel modulus

- `exists_nhds_one_norm_sub_lt`: a continuous compactly supported function `κ` on a locally
  compact group satisfies `‖κ(z h) - κ(z)‖ < ε` for all `z` and all `h` in a neighbourhood
  of `1` (tube lemma on `tsupport κ · V⁻¹ × {1}`).
- `continuous_absDet_ofInfinite_rpow`, `hasCompactSupport_kernel_translate`: continuity of
  `z ↦ |det z|^c` and compact support of `z ↦ κ(z⁻¹ h)`.
- `kernelModulus F n μ κ c h := ∫ |det z|^c ‖κ(z⁻¹ h) - κ(z⁻¹)‖ dμ(z)`.
  `integrable_modulus_integrand`: the integrand is integrable.
- `exists_kernelModulus_le`: for `ε > 0` there is an open neighbourhood `U` of `1` on which
  `kernelModulus ≤ ε`. Proof: outside the compact set `C = (tsupport κ · V⁻¹)⁻¹` the
  integrand vanishes. On `C` it is at most `ε / (M + 1) · |det z|^c`, where `M` is the
  integral of `|det|^c` over `C`.
- `norm_sub_le_kernelModulus` (the reproduction estimate): if `f` is reproduced by `κ` and
  `weight c f ≤ Φ` everywhere, then
  `‖ev f (g h) - ev f g‖ ≤ Φ |det g|^c kernelModulus(h)`. Proof: subtract the reproducing
  identities at `h` and at `1`. Then bound the integrand by
  `‖ev f (g z)‖ ≤ Φ |det g|^c |det z|^c`.

## Central law and central normal form

- `weight_mul_centralTorus lam c hc f hcent`: if `ev f (g · e^t) = e^{λ t} ev f g` and
  `n d c = Re λ`, then the weight is invariant under the central torus.
- `exists_centralNormalForm F n hn` (`0 < n`): there are a compact `Q₁` and `K ≥ 0` such that
  every `g` satisfies `γ g = A x · q · centralTorus s` with `γ` rational, `q ∈ Q₁`,
  `x ∈ Chamber K` and `∑ x = 0`. Proof: the Siegel decomposition
  `exists_siegelDecomposition`, with the mean of `x` moved into the central torus.
- `exists_weight_bound hS hn lam c hc f hcent`: a cuspidal vector with a central law has
  bounded weight. Proof: reduce to `A x · q` with `∑ x = 0` by the two previous lemmas. Then
  `exists_chamber_decay` with `R = 0` and decay exponent `0` bounds `‖ev f‖`, and `|det q|^{-c}`
  is bounded on the compact `Q₁`.
- `absDet_one`: `|det 1| = 1`.

## The finite net, the cusp cover and evaluation

- `evalOn T`: the linear map `f ↦ (p ↦ ev f p)` to functions on a finite set `T`.
  `evalOn_apply` unfolds it.
- `exists_finite_net F n hΩ hUo hU1 L hL c`: a compact set `Ω` is covered by finitely many
  sets `{g | (p⁻¹ g)_∞ ∈ U, (p⁻¹ g)_f ∈ L, |det (p⁻¹ g)|^{-c} < 2}` with `p` in a finite set
  `T`. These sets are open neighbourhoods of `p`; apply `IsCompact.elim_nhds_subcover`.
- `CuspAbsorbed U L g` (definition): there is a maximal block `a + (n - a) = n` with
  `0 < a` such that every left block-unipotent translate `u(Y) g` equals
  `γ · (g · u) · l` with `γ` rational, `u ∈ U` and `l ∈ L`.
- `exists_cusp_cover F n hn L hL hUo hU1`: there is a compact set `Ω` such that every `g`
  satisfies `γ g = g' · centralTorus s` with `γ` rational, and either `g' ∈ Ω` or
  `CuspAbsorbed U L g'`. Proof: write `g` in central normal form. Apply
  `chamber_alternative` with `R = 0`. Either `∑ |x i|` is bounded, or some block gap is at
  most `-ℓ`. If `ℓ ≥ ℓ₀(a)` (from `exists_deep_absorption`), `A x · q` is absorbed;
  otherwise `∑ |x i|` is again bounded. Then `Ω` is the image of
  `{∑ |x i| ≤ B} × Q₁` under `(x, q) ↦ A x · q`.
- `eq_zero_of_weight_le_half c f M hM hhalf`: if the weight of `f` is bounded by `M`, and
  every bound `Φ` of the weight also gives the bound `Φ / 2`, then `f = 0`. Proof: apply
  the hypothesis to `Φ = sup weight`, so `sup ≤ sup / 2` and the weight vanishes. Then `ev f = 0`,
  and `f = 0` by `toContinuous_injective`.

## The estimates and the theorem (section with a measure `μ`)

- `weight_le_of_absorbed` (deep estimate): if `f` is cuspidal and reproduced, has level `L`
  and `weight ≤ Φ`, and `g` is absorbed along a block into right translates by
  `U × L` where `kernelModulus ≤ ε` on `U`, then `weight c f g ≤ Φ ε`. Proof:
  `norm_le_of_cuspidal` bounds `‖ev f g‖` by the supremum over `Y` of
  `‖ev f (u(Y) g) - ev f g‖`. By absorption, rational invariance and level invariance this
  equals `‖ev f (g u) - ev f g‖ ≤ Φ |det g|^c ε`.
- `weight_le_of_near` (near estimate): if `ev f p = 0`, `(p⁻¹ g)_∞ ∈ U` and
  `(p⁻¹ g)_f ∈ L`, then `weight c f g ≤ Φ ε |det (p⁻¹ g)|^{-c}`. Proof: `g = p · k_∞ · k_f`,
  level invariance removes `k_f`, and the reproduction estimate at `p` applies.
- `weight_le_half` (halving): suppose `f` is cuspidal, reproduced by `κ`, of level `L`, with
  centrally invariant weight bounded by `Φ`. Suppose `kernelModulus ≤ 1/4` on `U`, `Ω` is a
  cusp cover for `U` and `L`, and `T` is a net of `Ω` on which `ev f` vanishes. Then
  `weight c f g ≤ Φ / 2` for every `g`. Proof: reduce to `g'` by rational and central
  invariance. If `g' ∈ Ω`, the near estimate at a net point gives `Φ · 1/4 · 2`; otherwise
  the deep estimate gives `Φ / 4`.
- `finiteDimensional_of_reproduced hS hn hκ hκc L hL lam W hlevel hrep hcent` (**main
  theorem**): let `S` be cuspidal, `0 < n`, and `κ` continuous and compactly supported.
  Let `W` be a subspace of `S.Space` all of whose vectors have level `L` (an open
  subgroup), are reproduced by `κ`, and satisfy the central law
  `ev f (g · e^t) = e^{λ t} ev f g` for one `λ ∈ ℂ`. Then `W` is finite-dimensional.
  Proof: put `c = Re λ / (n d)`. Choose `U` with `kernelModulus ≤ 1/4`, a cusp cover `Ω`
  and a finite net `T` of `Ω`. The linear map `evalOn T` restricted to `W` is injective:
  if `ev f` vanishes on `T`, the weight of `f` is bounded (`exists_weight_bound`) and halves
  every bound (`weight_le_half`), so `f = 0`. Hence `dim W ≤ |T|`. This theorem uses a
  raised heartbeat limit (`800000`).

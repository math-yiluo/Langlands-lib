# `U(2)`-finite functions of `GL_2(ℂ)` principal series as bottom-row polynomials

Lean module: `Langlands.Representation.Archimedean.ComplexGLTwoKFinite` (namespace
`Langlands.Archimedean.GLTwoKFinite`). Worker 728 wrote it for the proof of
`ComplexGLTwoUnlinkedIrreducibleStatement` (the target of Task 7148; written under Task 7064).

Provenance: internal, derived. It writes a `U(2)`-finite function as a polynomial on `U(2)`
(Library `UnitaryFinitePolynomial`) and transports it to all of `GL_2(ℂ)` through the
equivariance of the principal series.

## Definitions

For complex characters `d`, `e` with weights `l_d`, `l_e` and exponents `t_d`, `t_e`:

* `Phi d = unitChar l_d (t_d + 1/2)`, i.e. `Φ(δ) = (δ/|δ|)^{l_d} |δ|^{2t_d + 1}` (Library
  `unitChar`, module `ComplexStandardNontrivialProof`);
* `e0 d e = t_e - t_d - 1`;
* `kU u` = `bottomMat u = !![ū₁, -ū₀; u₀, u₁]` as an element of `U(2)` when `|u| = 1`, and
  `subst`, the entries of `bottomMat` and their conjugates as polynomials in `z, w`;
* `cayley t = (1 + it)/(1 - it)`.

## Main results

* `psc_two`: `principalSeriesCharacter ℂ 2 (complexPositionCharacter [d, e]) a =
  unitChar l_d (t_d + 1/2) (a₀) · unitChar l_e (t_e - 1/2) (a₁)`.
* `eq_of_row_det`: a function of the standard module of `[d, e]` takes the same value at two
  elements with the same bottom row and determinant (`mul_inv_mem_upperUnipotent`).
* `eq_mul_ev`: if `f(k) = Q(k, k̄)` on `U(2)`, then for every `g`
  `f(g) = Φ(det g) · (|r|²)^{t_e - t_d - 1} · Q'(u, ū)`. Here `r` is the bottom row of `g`,
  `u = r/|r|` and `Q' = bind₁ subst Q`.
* `ev_smul_phase`: for `|u| = 1` and `|ζ| = 1`, `Q'(ζu, conj(ζu)) = ζ^{l_e - l_d} Q'(u, ū)`.
* `sum_filter_eq_of_phase`: if `Σ_i ζ^{p_i} ζ^{-q_i} v_i = ζ^m Σ_i v_i` for all `|ζ| = 1`, then the
  terms with `p_i - q_i = m` sum to `Σ_i v_i`.
* `exists_isRealized`: every `x` in the `U(2)`-finite functions of the standard module of `[d, e]`
  satisfies `IsRealized (Phi d) (ls A m J) P x` for some `J` and `P ∈ Eig (la m J) (lb m J)`, with
  `m = l_e - l_d` and `A = (t_e - t_d - 1) + m/2`.

## Proof

`eq_mul_ev`: let `ρ = |r|` and `u = ρ⁻¹ r`. The element `diag(det g/ρ, ρ) · kU u` has the bottom row
and determinant of `g`. By `eq_of_row_det` and equivariance (`diag_mul_apply`, `psc_two`),
`f(g) = unitChar l_d(t_d+½)(det g/ρ) · unitChar l_e(t_e-½)(ρ) · f(kU u)`. Multiplicativity
(`unitChar_mul`) and the values at positive reals (`unitChar_ofReal`) give the factor
`Φ(det g) · ρ^{2(t_e - t_d - 1)}`. `ev_smul_phase` compares `kU(ζu)` with `diag(ζ⁻¹, ζ) · kU u`.
`sum_filter_eq_of_phase` multiplies by `ζ^K` to get a polynomial in `ζ`. That polynomial vanishes
on the infinite unit circle (`infinite_circle`, via `cayley`), so its coefficient of
`ζ^{K+m}` vanishes.

`exists_isRealized`: the Library theorem
`UnitaryFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors` gives `Q`. Write `Q'` as a sum
of monomials. By the phase relation and `sum_filter_eq_of_phase`, on the unit sphere only the
monomials `d` with `deg_z d - deg_w d = m` contribute. Each such monomial has bidegree `(la m j, lb m j)`
with `j = deg_z d - m⁺`. Rescaling from `u` to `r` (`ev_smul_monomial`, `inv_sqrt_pow`) and the
exponent identity `t_e - t_d - 1 - (deg_z d + deg_w d)/2 = ls A m J + (J - j)` (`term_eq`) give
`f = realize Φ (ls A m J) P` with `P = Σ_d N^{J-j_d} · (monomial)`, where `J` is the largest
`j_d`. `P ∈ Eig (la m J) (lb m J)` by `monomial_mem_Eig` and `N_pow_mul_mem`.

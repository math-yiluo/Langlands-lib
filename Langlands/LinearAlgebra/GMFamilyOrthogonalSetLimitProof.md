# Proof of Lapid's Lemma 8 for positive orthogonal sets

`Langlands.GMFamily.orthogonalSetLimit` proves
`Langlands.GMFamily.OrthogonalSetLimitStatement` (module
`Langlands.LinearAlgebra.GMFamilyOrthogonalSetLimitStatement`): for a root set
`R`, a Levi space `a`, `n ∈ ℕ` and `κ ∈ ℝ` there are a finite set `s` of
Schwartz seminorm indices and a constant `C` such that for every
`(G, M)`-family `d` of Schwartz functions, every `t ≥ 0`, every positive
`(G, M)`-orthogonal set `Y` with `⟪v, Y_S⟫ ≥ t` for all chambers `S` and
`v ∈ simpleRoots a S` and with `‖Y_S‖ ≤ κ(1 + t)` for all chambers, and every
chamber `S₀`,

```
‖ (2π)^{-k} ∫_{x ∈ 𝔞_M^G} (cd)_M(Λ_x) dx − d_{S₀}(0) ‖
    ≤ C / (1 + t)^n · ∑_S (s.sup schwartzSeminormFamily)(d S),
```

where `(cd)_M = cM R a (fun S Λ => exp(i Λ(Y S)) · d S Λ)` is `c_M` of the
product of the exponential family `c` and `d`, `Λ_x = ⟪x, ·⟫` and
`k = dim 𝔞_M^G`. The
proof does not use the hypothesis `‖Y_S‖ ≤ κ(1 + t)`: the constants depend
only on `R`, `a` and `n`.

## Structure of the proof

Write `V = 𝔞_M^G = relativeSpace R a` and `c_P(λ) = e^{λ(Y_P)}`. Below,
`c_M` and `c_M^{Q}` always refer to this exponential family `c`, `d_M^{Q}` to
`d`, and `(cd)_M` to the product family of the statement.

1. **Displacement** (`exists_generic_displacement`). Choose `ξ ∈ V` in general
   position for the alternate splitting formula, nonzero on every root
   nonvanishing on `a`, with `posSet R (−2ξ) = S₀`.
2. **Splitting almost everywhere** (`alternateSplitting_of_offWalls`,
   `ae_offWalls`). For almost every `x ∈ V` (those with `Λ_x` off the walls),
   `(cd)_M(Λ_x) = ∑_{(L₁, L₂)} d_M^G(L₁, L₂) c_M^{Q₁}(Λ_x) d_M^{Q₂}(Λ_x)`,
   with `(Q₁, Q₂) = splittingSection R ξ L₁ L₂`; both sections are faces
   `posSet R w_i`, `w_i ∈ a` (`splittingSection_fst_face`,
   `splittingSection_snd_face`).
3. **The `d`-sides** (`exists_face_schwartz`). For each pair, `d_M^{Q₂}`
   agrees off the walls with a Schwartz function `u_{L}` on `V` whose Fourier
   integral `phaseFourier u_L` decays like `(1 + ‖H‖)^{−(n + k + 1)}`, with
   constant `C_d · ∑_P schwartzSup K (d_P)` (Lapid's Corollary 3, in the form
   `exists_schwartz_cM`).
4. **Integration.** Each `c_M^{Q₁}(Λ_x) u_L(x)` is integrable: `u_L` is
   Schwartz, and for the fixed `Y` the function `c_M^{Q₁}` is bounded off the
   walls (`exists_norm_cQM_exp_le`, from the uniform bound `norm_expShift_le`
   at `s = 0`, using that `x ↦ c_M^{Q₁}(Λ_x)` is measurable,
   `measurable_cQM_dualParam`). So the integral of `(cd)_M` is
   `∑_L d_M^G(L₁, L₂) ∫_V c_M^{Q₁}(Λ_x) u_L(x) dx`.
5. **The main pair.** For `(L₁, L₂) = (𝔞_G, a)`, `d_M^G = 1`
   (`dCoeff_centralSpace_self`) and the sections are `(∅, S₀)`
   (`splittingSection_centralSpace_self`), so `c_M^{Q₁} = c_M`, the function
   `c_M` of the exponential family alone (`cQM_empty`), and
   `d_M^{Q₂} = d_{S₀}` (`cQM_parabolic`). Then `u_L = d_{S₀} ∘ Λ` almost
   everywhere, hence everywhere by continuity, and `u_L(0) = d_{S₀}(0)`.
   `exists_main_term_bound` bounds
   `|(2π)^{−k} ∫ c_M(Λ_x) u_L(x) dx − u_L(0)|`.
6. **The other pairs.** If `d_M^G(L₁, L₂) ≠ 0` and `(L₁, L₂) ≠ (𝔞_G, a)`, then
   `Q₁ ≠ ∅` (`eq_centralSpace_self_of_section_empty`), and
   `exists_face_term_bound` bounds `∫ c_M^{Q₁}(Λ_x) u_L(x) dx`.
7. **Assembly.** `exists_bound_at_chamber` sums these bounds, with
   `(2π)^{−k} ≤ 1`, to
   `C_{S₀} (1 + t)^{−n} ∑_P schwartzSup K_{S₀} (d_P)`.
   `orthogonalSetLimit` takes `K = max_{S₀} K_{S₀}`,
   `s = {(i, j) : (i, j) ≤ (K, K)}` (so that `schwartzSup K` is the supremum of
   the seminorms of `s`, after `schwartzSup_real_eq` for the scalar field) and
   `C = ∑_{S₀} C_{S₀}`.

The module also proves `cQM_empty`: `c_M^∅ = c_M` for every family `c`.

## Supporting modules

- `GMFamilyChamberCoordinates`: obtuse simple roots and the coordinate lower
  bound behind Lapid's (15).
- `GMFamilyFaceRestriction`: restriction of families to Levi subgroups of
  faces.
- `GMFamilySchwartzExtension`: Lapid's Corollary 3 with seminorm bounds.
- `GMFamilyExponentialBound`: a bound for `c_M` of an exponential family at
  the spectral parameters `i(Λ + iτμ)`, `|τ| ≤ 1`, for a direction `μ`
  nonzero on all simple roots, at the points where all linear factors
  `Λ(v) + iτμ(v)` are nonzero, uniform in `Λ` (removable singularities and
  maximum modulus).
- `GMFamilyConeIntegrals`: `∫ c_M u` for an exponential family and an
  integrable test `u` as a sum of orthant integrals of Fourier integrals,
  under that module's integrability hypotheses.
- `GMFamilyRelativeFourier`: Fourier integrals on `V`, decay, inversion at
  `0`, coordinates and decay integrals.
- `GMFamilyGenericDisplacement`, `GMFamilySplittingDisplacement`: points off
  the walls, the displacement, the main pair and the alternate splitting
  formula off the walls.
- `GMFamilyOrthogonalSetTerms`, `GMFamilyOrthogonalSetBounds`: the term
  estimates.

## Sources and route

The statement is Lemma 8 of E. Lapid, *On Arthur's asymptotic inner product
formula of truncated Eisenstein series*, in: On Certain L-Functions, Clay Math.
Proc. 13 (2011), §7, pp. 326–327
(`lapid-2011-asymptotic-inner-product-truncated-eisenstein`, volume PDF
SHA-256 `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`;
PDF page = printed page + 9), for an arbitrary positive orthogonal set, as
explained in `GMFamilyOrthogonalSetLimitStatement.md`. The proof follows
Lapid's outline: the product formula of J. Arthur, *The invariant trace
formula. I. Local theory*, §7, Corollary 7.4 (`arthur-1988-invariant-trace-formula-I`,
SHA-256 `902db792ffe113507165a252b0c1b8c59f78ab8d04def1c5c39b0372362dc3ac`),
in the form of the alternate splitting formula of J. Arthur, *An introduction
to the trace formula*, §17, Lemma 17.6, p. 101
(`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`), proved in
the Library as `alternateSplittingFormula`; Lapid's Corollary 3 for the
`d`-side; the estimate (16) for `Q₁ ≠ G`; and (17) for the main term.

It differs from Lapid in the treatment of `c_M^{Q₁}`. Lapid uses Arthur's
formula expressing `c_M^{Q₁}(T; μ)` as the Fourier transform of the
characteristic function of the convex hull of the points `Y_Q(T)` (Arthur 1982,
(3.1); Arthur 2005, (17.3) and Lemma 17.2), and the polynomial growth of the
volumes of these hulls (which is where the bound `‖Y_P‖ ≤ κ(1 + t)` enters).
Here the integral of `c_M` against a test is instead computed from the
boundary values, in the sense of distributions, of the Laplace transforms of
oriented orthants (the coordinate calculation of P. Delorme,
*Troncature pour les espaces symétriques réductifs*, Acta Math. 179 (1997),
§9, (9.1) and Lemma 11, p. 72, `delorme-1997-reductive-symmetric-space-truncation`,
SHA-256 `02eb996aa75322ecb3294cbe839dd9cc2b37077d781455e49128a2f01e0dc70c`,
formalized as `Langlands.Analysis.ConeFourierBoundary`), approached along a
direction `μ` nonzero on all simple roots (in the proof, `μ` is the functional
`⟪ξ, ·⟫` of the displacement). The Library's `θ_S(Λ)` is
`gram(Δ_S)⁻¹ ∏_{v ∈ Δ_S} iΛ(v)`, that is, `θ_S` at the spectral parameter
`iΛ`. Replacing `Λ` by `Λ + iτμ` gives the spectral parameter `iΛ − τμ`,
and for `τ > 0` (with `μ(v) ≠ 0` for all `v ∈ Δ_S`)

```
θ_S(Λ + iτμ)⁻¹ = gram(Δ_S) · ∏_{v ∈ Δ_S} (τ(−μ(v)) + iΛ(v))⁻¹
              = gram(Δ_S) · orthantSign(−μ) ·
                  ∫_{−μ(v) X_v > 0} e^{−τ ∑_v (−μ(v)) X_v} e^{−i ∑_v X_v Λ(v)} dX
```

(`thetaShift_I_mul_inv` and `orthant_laplace'` in `GMFamilyConeIntegrals`),
with the Gram factor `gram(Δ_S)` of the simple roots and the orientation sign
`orthantSign(−μ) = ∏_v sign(−μ(v))`; the damped integral converges
absolutely. As `τ → 0⁺`, off the walls `θ_S(Λ + iτμ)⁻¹` converges pointwise
to the ordinary reciprocal `θ_S(Λ)⁻¹`, whereas the undamped orthant integral
arises only as the limit of the integrals against a test (the reciprocal
`θ_S(Λ)⁻¹` of a single chamber need not be integrable against the test). The
formula `integral_cM_exp_mul` is of this second kind: it pairs `c_M` of an
exponential family with an integrable test `u`, assumes that `μ(v) ≠ 0` on
all simple roots, that the parameter is off the walls almost everywhere and
that the Fourier integrals of the phased tests `e^{iΛ(y_S)} u` are integrable
on the orthants, and takes the limit `τ → 0⁺` of the paired integrals. In the
proof it is applied, through `integral_cM_exp_eq_orthants` of
`GMFamilyOrthogonalSetTerms`, to the Schwartz function `u_L` of step 3 and
to a root set whose `c_M` is `c_M^{Q₁}`: the Levi roots of `Q₁` with the
family `S ↦ Y(Q₁ ∪ S)` for a proper face (`exists_face_term_bound`), and `R`
itself for the main pair, where `Q₁ = ∅` (`exists_main_term_bound`);
`integrable_orthant_phaseFourier` supplies the orthant integrability. The
passage to the boundary uses a bound for `c_M` of
the exponential family that is uniform near the imaginary axis, proved by the
maximum modulus principle; the decay then comes from the hypothesis
`⟪v, Y_P⟫ ≥ t` through the coordinates of the orthant points, without the
bound on `‖Y_P‖`.

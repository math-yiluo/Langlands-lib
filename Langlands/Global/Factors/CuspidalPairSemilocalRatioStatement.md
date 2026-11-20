# Semi-local ratios of partial Rankin–Selberg integrals

Lean module: `Langlands.Global.Factors.CuspidalPairSemilocalRatioStatement`.

This module defines the predicate `CuspidalPairPoles.IsSemilocalRatioFamily` and states
`CuspidalPairSemilocalRatioStatement`: the partial Whittaker integrals `Ψ_(S∪∞)` of two
cuspidal realizations are entire multiples of the semi-local L-function
`L_(S∪∞) = L_∞ ∏_(v ∈ S) L_v` on a fixed right half-plane, and at every point some datum has
a nonvanishing multiplier. This is the local input of Cogdell (2004), §4, written
semi-locally. It is a premise of `CuspidalPairPoleReductionStatement` and a proposition
definition only.

## 1. Sources

"p." is the printed page, "PDF" the one-based page of the registered file.

| Source ID | Short name | Locators |
|---|---|---|
| `cogdell-2004-analytic-theory-gln` | Cog04 (PDF = printed + 3) | convergence of local integrals, p.212 (PDF 215), items 1–3; Theorem 3.1 and the finite sums, p.213 (PDF 216); the space `M(π × π')` and Theorem 3.5, p.217 (PDF 220); completed tensor products, continuity, and K-finite sums for `m = n - 1, n`, pp.217–218 (PDF 220–221); restricted tensor products and the global setup, p.218 (PDF 221); proof of Theorem 4.1, p.219 (PDF 222); finite local sums, p.220 (PDF 223); §4.2, pp.221–222 (PDF 224–225) |
| `jacquet-2009-archimedean-rankin-selberg` | Jac09 (PDF = printed) | the space `L(τ)` and its semi-norms, pp.5–6; integrals (2.4)–(2.6) and Theorem 2.1, p.6; Theorem 2.3 and completed tensor products, pp.8–9; Lemma 2.5, Theorem 2.6, p.9; Theorem 2.7 and standard data, p.10; Lemma 3.5, p.14; §5.1 and (5.1), p.32; Appendix §16 (Tate factors), pp.109–110 |

**What the sources state.**

- *Finite places.* Cog04 p.212: the local integrals converge for `Re s ≫ 0` (absolutely for
  `Re s ≥ 1` for unitary `π`, `π'`), are rational in `q^(-s)`, with a common denominator
  depending only on `π`, `π'`. Theorem 3.1 (p.213): they span a `ℂ[q^s, q^(-s)]`-fractional
  ideal with generator `L(s, π × π')`; equivalently `Ψ / L` is entire for all data, and `L`
  is a finite sum of integrals.
- *Archimedean places.*
  - Jac09 pp.5–6 defines `L(τ)`: the meromorphic functions `f` that are holomorphic
    multiples of `L(s, τ)` and such that `P(s) f(s)` is bounded on `A ≤ Re s ≤ B` whenever
    `P` is a polynomial with `P(s) L(s, τ)` holomorphic there. It is complete for the
    semi-norms `μ_(P,A,B)(f) = sup_(A ≤ Re s ≤ B) |P(s) f(s)|`. Cog04 p.217 defines the same
    space `M(π × π')`.
  - Jac09 Theorem 2.1 (p.6): (i) the integrals converge for `Re s ≫ 0`; (ii) each extends
    to a meromorphic function that is a holomorphic multiple of `L(s, σ_u ⊗ σ'_u')`,
    bounded at infinity in vertical strips. Cog04 Theorem 3.5 (p.217): the integrals lie
    in `M(π × π')`, so the ratios `e = Ψ / L(s, π × π')` are entire.
  - Only the entireness of `e` is used here. The vertical-strip bound belongs to the
    continued integral, multiplied by a polynomial that cancels the poles of `L`. Cog04's
    sentence also calls the ratios bounded in vertical strips. Read literally for the
    ratios, this fails: for the trivial pair of `GL_1(ℝ)` and `Φ(x) = x² exp(-πx²)`, (2.6)
    with `d^×x = dx / |x|` gives `Ψ(s) = L(s + 2)`, where `L(s) = π^(-s/2) Γ(s/2)`
    (Jac09 Appendix §16, pp.109–110). So `Ψ(s) / L(s) = s / (2π)`, which is unbounded on
    every vertical line.
  - Jac09 Theorem 2.3 (p.8): the maps `(f, f') ↦ Ψ_j(s, W_f, W_f')` (`n > n'`) and
    `(f, f', Φ) ↦ Ψ(s, W_f, W_f', Φ)` (`n = n'`, `Φ ∈ S(F^n)`) are continuous into
    `L(σ_u ⊗ σ'_u')`. Jac09 pp.8–9 and Cog04 pp.217–218: the integrals extend to functions
    `W(g, g') = λ(π(g) ⊗ π'(g') f)` with `f` in the completed (projective) tensor product
    `I_(σ,u) ⊗̂ I_(σ',u')`, and Theorems 2.1 and 2.3 remain true for them.
  - Jac09 §5.1, (5.1) (p.32): in the range of convergence
    `|Ψ(s, W_v, W'_v, Φ)| ≤ ∫ |W_v| |W'_v| |Φ(e_n g)| |det g|^(Re s) dg ≤ μ(v) μ'(v') ν(Φ)`
    with continuous semi-norms `μ`, `μ'`, `ν`. The convergence proof (Lemma 3.5, p.14) uses
    `Φ` only through `|Φ(e_n a k)| ≤ C_N (1 + a_n²)^(-N)`. The range of `Re s` depends on the
    representations (through their growth exponents), not on the vectors.
  - Jac09 Theorem 2.6 (p.9): suppose the exponents are ordered,
    `Re u_1 ≤ … ≤ Re u_r` and likewise for `u'`. For `n > n'` every `m ∈ L(σ_u ⊗ σ'_u')`
    is `Ψ(s, W)` for one `f ∈ I_(σ,u) ⊗̂ I_(σ',u')`. For `n = n'` it is a finite sum
    `Σ_i Ψ(s, W_i, Φ_i)` with `f_i ∈ I_(σ,u) ⊗̂ I_(σ',u')`. These are smooth data in the
    completed tensor product; they need not be finite sums of pure tensors. Lemma 2.5 and
    the paragraph after it (p.9): if the Langlands quotient of `I_(σ,u)` (ordered
    exponents) is generic, then `I_(σ,u)` is irreducible. So by the Langlands
    classification a generic irreducible representation is such an irreducible
    `I_(σ,u)`.
  - Jac09 Theorem 2.7 (p.10): if `I_(σ,u)` and `I_(σ',u')` are irreducible, then
    `L(s, σ_u ⊗ σ'_u')` is a single integral (`n' = n - 1`) or a finite sum of integrals with
    standard Schwartz functions (`n' = n`), of `K`-finite `f` in the algebraic tensor product.
    Cog04 p.218 states the same for `m = n - 1, n`.
- *Global.* Cog04 p.218: the restricted tensor product decompositions `π ≅ ⊗' π_v` with
  irreducible admissible smooth generic unitary `π_v`. Cog04 p.219, proof of Theorem 4.1:
  for appropriate (factorizable) data,
  `I(s; φ, φ') = (∏_(v ∈ S) e_v(s; W_v, W'_v)) L(s, π × π')` with entire local ratios
  `e_v = Ψ_v / L_v`, and similarly for `m = n` with `Φ`. Cog04 pp.221–222: "for any `s₀ ∈ ℂ`
  and any `v` there is a choice of local `W_v`, `W'_v` and `Φ_v` such that the local ratios
  `e_v(s₀; W_v, W'_v) ≠ 0` or `e_v(s₀; W_v, W'_v, Φ_v) ≠ 0`".

## 2. Declarations

### `IsSemilocalRatioFamily good Ψ L`

For a family of functions `Ψ i : ℂ → ℂ` indexed by data `i` and a predicate `good`: there is
`σ` such that (a) every good `i` has an entire `E` with `Ψ i s = E s * L s` for all
`σ < Re s`, and (b) for every `s₀` some good `i` has such an `E` with `E s₀ ≠ 0`.

### `CuspidalPairSemilocalRatioStatement`

The statement quantifies over:

- a number field `F` and a nontrivial unitary character `ψ` of `𝔸` trivial on `F`;
- actual cuspidal realizations `T`, `T'` of `GL_(r+1)`, `GL_(t+1)`, with spectral
  presentations `P`, `P'` whose finite components are irreducible and admissible;
- a finite set `S` of finite places that contains both exceptional sets and outside which
  `ψ_v` has conductor `𝒪_v` (`FiniteAdditiveSupport ψ S`);
- finite pair L-data `c` and archimedean parameters `dR`, `dR'`, `dC`, `dC'` of `T`, `T'`.

Put `semilocalL(s) = L_∞(s) ∏_(v ∈ S) c.finiteL v s`. Here `L_∞` is the product of the
archimedean pair factors of the parameters, the same expression as in
`CuspidalPairPoleStatement`. Then:

- (`r = t`) the family `(x, x', Φ) ↦ Ψ_(S∪∞)(s; W_x, W'_x', Φ)`
  (`partialEqualWhittakerIntegral`), over `x`, `x'` spherical outside `S` and `Φ`
  Schwartz–Bruhat and standard outside `S`, has the semi-local ratio property for
  `semilocalL`;
- (`t < r`) the same for `(x, x') ↦ Ψ_(S∪∞)(s; W_x, W'_x')`
  (`partialUnequalWhittakerIntegral`, `W_x` of `T`);
- (`r < t`) the same for `(x, x') ↦ Ψ_(S∪∞)(s; W'_x', W_x)` (`W'_x'` of the larger group
  `T'`), still with `semilocalL` built in the order `(T, T')`.

Here `W_x = cuspWhittaker F T ψ.complex x` is the `ψ`-Whittaker function of the larger
group and the other one is taken with `ψ⁻¹`, as in `EqualEulerFactorizationStatement` and
`UnequalEulerFactorizationStatement`. In equal rank, `Φ ∈ schwartzBruhat` is a finite sum
of products `Φ_∞ ⊗ Φ_f`. Each `Φ_∞` is a Schwartz function of all archimedean coordinates
jointly, so it need not be a product over the infinite places.

## 3. Why the statement holds (provenance of the semi-local form)

The argument is Cogdell's (Cog04 pp.219–222), with the local theory at the places of `S`
and at all infinite places together. Steps 3–5 below, for joint archimedean Schwartz
functions, are internal: the sources treat one place at a time.

**Reduction to semi-local data.** The Library's partial integral `Ψ_(S∪∞)` is the global
Whittaker integral over the classes of points `g` with `g_v ∈ N_m(F_v) GL_m(𝒪_v)` at every
finite `v ∉ S`. For vectors spherical outside `S` and `Φ` standard outside `S`, the
integrand there depends only on the components of `g` at `S ∪ ∞`. The unipotent characters
of `W` and `W'` cancel, and the vectors are fixed by the integral points. So up to a positive
constant, which comes from the normalization of the quotient measure, `Ψ_(S∪∞)` is the
semi-local integral over `N_m(F_(S∪∞)) \ GL_m(F_(S∪∞))`, where `GL_m` is the group of
integration (`m = n` in equal rank, the smaller group in unequal rank).

The space of an actual realization is the algebraic tensor product of its finite factor
and the actual irreducible admissible (`K`-finite) source subspaces at the infinite places
(`CuspidalOperatorRealization.allPlaceTensorEquiv`). The Whittaker function of a pure
tensor is the product of the local Whittaker functions (Cog04 p.218). Hence the
restrictions of `W` and `W'` to the places of `S ∪ ∞` are finite sums of products
`∏_(v ∈ S ∪ ∞) W_v(g_v)`, with `K`-finite `W_v` at the infinite places.

On the points integral outside `S`, each `Φ_f` is a locally constant compactly supported
function of the coordinates at `S`. Such a function is a finite sum of products over the
places of `S`. By linearity it therefore suffices to treat
`Ψ_S(s) · Ψ_∞(s; Φ_∞)`. Here `Ψ_S = ∏_(v ∈ S) Ψ_v(s; W_v, W'_v, Φ_v)` and

`Ψ_∞(s; Φ_∞) = ∫_(N(F_∞) \ GL_n(F_∞)) ∏_(v | ∞) W_v(g_v) W'_v(g_v) Φ_∞(e_n g_∞) |det g_∞|^s dg_∞`

is the archimedean integral, with fixed pure `W_∞`, `W'_∞` and a joint Schwartz function
`Φ_∞`. In unequal rank there is no `Φ`, and the archimedean part is directly the product
`∏_(v | ∞) Ψ_v`.

**(a) Entire multiples on a common half-plane.**

1. *Places of `S`.* `Ψ_v = e_v L_v` with `e_v` entire (Theorem 3.1), for `Re s > σ_v`
   (Cog04 p.212, items 1 and 3). The bound `σ_v` depends only on `Π_v` and `Π'_v`.
2. *Infinite places, pure `Φ_∞ = ⊗_v Φ_v`.* By Fubini, `Ψ_∞ = ∏_v Ψ_v = (∏_v e_v) L_∞`,
   and each `e_v` is entire (Jac09 Theorem 2.1(ii); Cog04 Theorem 3.5).
3. *Continuity of the normalized integrals.* Let `O(ℂ)` be the Fréchet space of entire
   functions, with uniform convergence on compact sets. For each `v | ∞`, the map
   `Φ_v ↦ e_v(Φ_v) = Ψ_v(·; W_v, W'_v, Φ_v) / L_v` from `S(F_v^n)` to `O(ℂ)` is
   continuous and linear. By Jac09 Theorem 2.3(ii), `Φ_v ↦ Ψ_v` is continuous into `L(τ_v)`.
   Let `K` be compact inside a strip `A ≤ Re s ≤ B`, and let `P` have as zeros the poles of
   `L_v` in the strip, with multiplicity. Then `P L_v` is holomorphic and has no zeros
   there, because archimedean L-factors are products of Gamma factors (Jac09 Appendix §16).
   So `sup_K |f / L_v| ≤ μ_(P,A,B)(f) · sup_K |P L_v|^(-1)`. The same bound shows that
   `f ↦ (f / L_v)(s₀)` is continuous on `L(τ_v)`.
4. *Extension to joint `Φ_∞`.* Two standard functional-analytic facts are used; neither
   comes from the registered sources. First, `S(F_∞^n)` is the completed projective tensor
   product of the spaces `S(F_v^n)` (nuclearity of Schwartz spaces). Second, `O(ℂ)` is a
   Fréchet algebra. The continuous multilinear map `(Φ_v)_v ↦ ∏_v e_v(Φ_v)` therefore
   extends uniquely to a continuous linear map `E : S(F_∞^n) → O(ℂ)`. Finite sums of pure
   tensors are dense in `S(F_∞^n)`. If such sums converge to `Φ_∞`, their multipliers
   converge to `E(Φ_∞)` uniformly on compact sets of `s`.
5. *Agreement with the integral.* Let `σ_∞` be in the range of convergence of
   Jac09 §5.1 at every infinite place. For `Re s > σ_∞`, both `Φ_∞ ↦ E(Φ_∞)(s) L_∞(s)`
   and `Φ_∞ ↦ Ψ_∞(s; Φ_∞)` are continuous linear forms on `S(F_∞^n)`. The first is
   continuous because evaluation at `s` is continuous on `O(ℂ)`. For the second, a
   Schwartz semi-norm `ν` gives `|Φ_∞(x)| ≤ ν(Φ_∞) ∏_v (1 + ‖x_v‖²)^(-N)`, since
   `∏_v (1 + ‖x_v‖²) ≤ (1 + ‖x‖²)^d` with `d` the number of infinite places. Jacquet's
   majorization (Lemma 3.5 and (5.1)) uses `Φ` only through such a bound, so
   `|Ψ_∞(s; Φ_∞)|` is at most `ν(Φ_∞)` times a product over `v | ∞` of convergent local
   majorants. The two forms agree on pure tensors by step 2, so they agree everywhere.
   Hence `Ψ_∞(s; Φ_∞) = E(Φ_∞)(s) L_∞(s)` with `E(Φ_∞)` entire.
6. *Summing.* On `Re s > σ`, with `σ = max(max_(v ∈ S) σ_v, σ_∞)`,
   `Ψ_(S∪∞) = E · semilocalL` with `E` a finite sum of products of entire functions. The
   bound `σ` depends only on the local components, not on the datum. Both sides are
   holomorphic there, because the integrals converge absolutely.

**(b) A nonvanishing multiplier at a given `s₀`.** Take pure local data everywhere: at
`S ∪ ∞` the data below, outside `S` the spherical vectors, and `Φ_∞ = ⊗_v Φ_v`. The
multiplier at `s₀` is then a nonzero constant times `∏_(v ∈ S ∪ ∞) e_v(s₀)`. It remains
to make each factor nonzero (Cog04 pp.221–222).

- *At `v ∈ S`.* The ratios span `ℂ[q^s, q^(-s)]`, which contains `1` (Theorem 3.1). So
  some datum has `e_v(s₀) ≠ 0`.
- *At `v | ∞`.* The local component is an irreducible induced representation with ordered
  exponents. Jac09 Theorem 2.6 realizes `L_v` as one integral (`n' < n`) or as a finite sum
  `Σ_i Ψ(s, W_i, Φ_i)` (`n' = n`), with smooth `f_i` in the completed tensor product.
  Then `Σ_i e(s; W_i, Φ_i) = 1`, so some `i` has `e(s₀; W_i, Φ_i) ≠ 0`. Fix that `Φ_i`.
  The form `f ↦ e(s₀; W_f, Φ_i)` on `I ⊗̂ I'` is continuous (Jac09 pp.8–9; Cog04 p.218;
  step 3 for the division by `L_v` and the evaluation at `s₀`). It is not zero. `K`-finite
  vectors are dense in each induced representation, and the algebraic tensor product is
  dense in its completion. Hence `K`-finite pure tensors `f_1 ⊗ f_2` span a dense
  subspace, and one of them has `e_v(s₀) ≠ 0`. For `n' = n - 1, n`, Jac09 Theorem 2.7 gives
  such `K`-finite data directly.
- The resulting pure tensor of local data is a global datum of the family, because it is
  spherical (and standard) outside `S`. Its multiplier at `s₀` is nonzero.

**Order of the factors.** The L-factor of the pair is symmetric in the two factors. So for
`r < t` the integral of `(T', T)` is compared with `semilocalL` in the order `(T, T')`.

## 4. Scope

- Only the semi-local statement is formulated. The finite-sum identity `L_v = Σ Ψ_v` is not
  stated. At an archimedean place, Jac09 Theorem 2.6 realizes `L_v` by smooth data in the
  completed tensor product `I ⊗̂ I'`, which need not be finite sums of pure tensors.
  Jac09 Theorem 2.7 gives `K`-finite finite-sum realizations only in the equal and
  adjacent ranks `n' = n` and `n' = n - 1` (see also Cog04 pp.217–218, p.221).
- The finite pair L-data `c` are arbitrary: `c.finiteL v` is the JPSS pair L-factor of the
  local components (`IsAutomorphicPairLPolynomial`), which does not depend on the additive
  character (Cog04 p.213).

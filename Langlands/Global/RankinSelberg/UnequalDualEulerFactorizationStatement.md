# Partial Euler factorization of the unequal-rank dual global Whittaker integral

`Langlands.Global.RankinSelbergGlobal.UnequalDualEulerFactorizationStatement` is the partial
Euler factorization, at the unramified places, of the dual global Whittaker integral
`Ψ̃(s; ρ(w_(n,m)) W̃, W̃')` of a pair of cusp forms on `GL_n × GL_m` with `m < n`. The
partial L-function in it is the one of the contragredient pair. It is a Prop-valued
statement. Nothing here proves it.

## Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in Bernstein–Gelbart (eds.),
*An Introduction to the Langlands Program* (2004), registered as
`cogdell-2004-analytic-theory-gln` (PDF SHA-256 `8117f145…`, PDF page = printed page + 3).

* §2.2, printed p.207 (PDF p.210): the dual integral. With `φ̃(g) = φ(w_n ᵗg⁻¹)`, the
  integral `Ĩ(1 − s; φ̃, φ̃')` unfolds to `Ψ̃(1 − s; ρ(w_(n,m)) W̃_φ, W̃'_φ')`, with
  `w_(n,m) = diag(I_m, w_(n−m))` and `W̃(g) = W(w_n ᵗg⁻¹) ∈ W(π̃, ψ⁻¹)`. Here `Ψ̃` has an
  extra inner integral over `x ∈ M_(n−m−1,m)(𝔸)` of
  `W([[h,0,0],[x,I_(n−m−1),0],[0,0,1]])`. `Ψ̃(s; W, W')` converges absolutely for
  `Re s ≫ 0`. For factorizable vectors it is the product of the local integrals `Ψ̃_v`.
* §4.1, proof of Theorem 4.1, printed p.220 (PDF p.223): "for appropriate `φ` and `φ'`",
  `Ĩ(1 − s; φ̃, φ̃') = (∏_(v ∈ S) Ψ̃_v(1 − s; ρ(w_(n,m)) W̃_v, W̃'_v) / L(1 − s, π̃_v × π̃'_v)) · L(1 − s, π̃ × π̃')`.
  Equivalently, `Ψ̃ = (∏_(v ∈ S) Ψ̃_v) · L^S(1 − s, π̃ × π̃')`.
* Theorem 3.2, printed p.214 (PDF p.217), the local functional equation,
  `Ψ̃_v(1 − s; ρ(w_(n,m)) W̃_v, W̃'_v) = ω'_v(−1)^(n−1) γ(s, π_v × π'_v, ψ_v) Ψ_v(s; W_v, W'_v)`,
  and Theorem 3.3, printed p.215 (PDF p.218), the unramified computation with
  `ε(s, π_v × π'_v, ψ_v) = 1`. For `v ∉ S`, `ω'_v(−1) = 1` (p.220). Together they give
  `Ψ̃_v(s; ρ(w_(n,m)) W̃_(o,v), W̃'_(o,v)) = L(s, π̃_v × π̃'_v)` for the normalized spherical
  data.

The consumer of this statement is the proof of the partial functional equation
`Langlands.Global.CuspidalPairPartialGammaEquationStatement` (Task 6190). It needs the
factorization on both sides of the global functional equation. The task contract asks
only for the ordinary side (`UnequalEulerFactorizationStatement`). This statement is the
dual side, which the source uses on p.220.

## The statement

`F`, `ψ`, `t < r`, `T`, `T'` and `S` are as in `UnequalEulerFactorizationStatement`, with
`FunctionalEquationComparison.FiniteAdditiveSupport ψ S`. In addition:

* `Td`, `Td'` are actual cuspidal realizations with
  `Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization` and
  the same for `Td'`, `T'`. So `Td` realizes `π̃` and `Td'` realizes `π̃'` (module
  `Langlands.Automorphic.Contragredient`).
* `Pd`, `Pd'` are spectral presentations of `Td`, `Td'` with exceptional sets contained in
  `S`.

Then there exists `σ : ℝ` with the following property. Take any vectors `x : T.Space`,
`x' : T'.Space` fixed by `GL(𝒪_v)` at every finite `v ∉ S` (`IsSphericalOutside`). Let
`W = cuspWhittaker F T ψ.complex x` and `W' = cuspWhittaker F T' ψ.complex⁻¹ x'`, and set

* `Wdual = translateFunction F n (unfoldingWeyl F h) (dualFunction F n W)`, that is,
  `g ↦ W(w_n ᵗ(g w_(n,m))⁻¹)`. This is `ρ(w_(n,m)) W̃`.
* `W'dual = dualFunction F m W'`, that is, `g ↦ W'(w_m ᵗg⁻¹)`. This is `W̃'`.

These are exactly the functions in the dual half of the published
`UnequalUnfoldingStatement`. Then for every `s` with `σ < Re s`:

1. `DualWhittakerAbsolutelyConvergent F h Wdual W'dual s` holds: the iterated integral
   `Ψ̃(s; Wdual, W'dual)` converges absolutely, including the inner integrals.
2. `∑_(v ∉ S) ‖L̃_v(s) − 1‖` converges, where `L̃_v(s) = partialEulerFactor Pd Pd' hPd hPd' v s`.
3. There is `p` with `HasProd (fun v => L̃_v(s)) p` and
   `dualWhittakerIntegral F h Wdual W'dual s = partialDualWhittakerIntegral F h S Wdual W'dual s * p`.

The source evaluates `Ψ̃` at `1 − s` with `Re s ≪ 0`. In the variable of this statement
that is the right half-plane `σ < Re s` for `Ψ̃(s)`. Every convergence claim is in the
conclusion.

## Normalizations and comparison with the source

* **Contragredient spectra.** `W̃ = dualFunction F n W` lies in the `ψ⁻¹`-Whittaker
  model of `π̃`, and `W̃'` lies in the `ψ`-Whittaker model of `π̃'`. At `v ∉ S` the local
  factor is therefore `L(s, π̃_v × π̃'_v)`. The spectra of `Pd`, `Pd'` at `v ∉ S` are the
  Satake parameters of the local components of `Td`, `Td'`, that is, of `π̃_v`, `π̃'_v`.
  The reason is the one given for `T` in `UnequalEulerFactorizationStatement`: `Td` is
  irreducible. So `partialEulerFactor Pd Pd'` is the factor
  `det(I − q_v^(−s) A_(π̃_v) ⊗ A_(π̃'_v))^(−1)`, with the same Satake normalization (Gross
  (1998), (3.14), through `Unramified.standardHeckeScalar`). Presenting the
  contragredients through their own realizations and presentations avoids any Library
  comparison of the spectra of `T` and `Td`.
* **The partial dual integral.** `partialDualWhittakerIntegral` restricts only the outer
  variable `h` to the classes with `h_v ∈ N_m(F_v) GL_m(𝒪_v)` for all finite `v ∉ S`. Its
  inner integral over `M_(n−m−1,m)(𝔸)` is unrestricted. At such a place write `h_v = u k`
  with `u ∈ N_m(F_v)` and `k ∈ GL_m(𝒪_v)`, and let `W_o` be the normalized spherical
  function, here `ρ(w_(n,m)) W̃_(o,v)`, which is again spherical because `w_(n,m)` is
  integral. Then `[[u k,0,0],[x,I,0],[0,0,1]]` equals
  `diag(u, I) · [[I,0,0],[x k⁻¹,I,0],[0,0,1]] · diag(k, I)`. After the change of variables
  `x ↦ x k`, which preserves measure, the local inner integral is the character value at
  `u` times `∫ W_o([[I,0,0],[x,I,0],[0,0,1]]) dx`.

  This last integral equals `vol(M_(n−m−1,m)(𝒪_v))`. The function `W_o` vanishes on
  `diag(t) k` unless `|t_1| ≤ … ≤ |t_n|`, because `ψ_v` has conductor `𝒪_v`. For
  `g = [[I,0],[x,I]] ∈ GL_(n−1)`, the maximum norm of the `j × j` minors of the last `j`
  rows of `g` is `|t_(n−j) ⋯ t_(n−1)|`, with `t_n = 1`. These minors include `1` and the
  entries of the last `j` rows of `x`. So `W_o` can be nonzero only if `x` is integral,
  and there `W_o = 1`. The character values at `u` cancel against `W̃'_(o,v)(u k)`, and
  `|det h_v| = 1`. Hence, as in the ordinary case, `Ψ̃_(S∪∞)` is the global measure
  constant times the local dual integrals at `S ∪ ∞`, times local volumes that occur
  identically in the full integral. The identity therefore holds for every normalization
  of `whittakerQuotientMeasure` and `rectangleMeasure`.
* **Vectors, uniformity, `S`.** These are as in `UnequalEulerFactorizationStatement`. The
  conditions `IsSphericalOutside` are imposed on `x ∈ T` and `x' ∈ T'`. The map
  `φ ↦ φ̃` sends `GL(𝒪_v)`-invariant forms to `GL(𝒪_v)`-invariant forms, because
  `w_n ∈ GL_n(𝒪_v)` and `GL_n(𝒪_v)` is stable under `ι`. Both sides are linear in `x` and
  in `x'`. `σ` is chosen before the vectors.

## Deviations from the source

* The task contract lists the factorization only for `Ψ`. This statement adds the dual
  side, which Cogdell uses on p.220 and the consumer Task 6190 needs.
* Cogdell obtains the unramified dual local integral from the local functional equation.
  The statement asserts only the global identity, so a proof may use that route or a
  direct computation.
* `HasIrreducibleAdmissibleComponents` is not assumed, as in the ordinary statement.
* Cogdell's `S` contains the archimedean places. Here `S` is finite and the infinite
  places are always kept in `Ψ̃_(S∪∞)`.

## Provenance

The statement transcribes Cogdell pp.207, 214–215 and 220 onto the Library's actual
realizations, contragredient realizations, spectral presentations and the published dual
Whittaker integral of `Langlands.Global.RankinSelberg.WhittakerIntegrals`. The support
argument above is a standard computation (Iwasawa decomposition and the support of
spherical Whittaker functions). It is given only to explain why the restriction is placed
on `h` alone. It is not part of the Lean statement.

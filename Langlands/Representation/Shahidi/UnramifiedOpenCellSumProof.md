# Proof of the unramified value of the two-block open-cell sum

Module `Langlands.Representation.Shahidi.UnramifiedOpenCellSumProof`.

## Result

`Langlands.Shahidi.unramifiedOpenCellSum : UnramifiedOpenCellSumStatement.{u}` proves the
statement of `Langlands.Representation.Shahidi.UnramifiedOpenCellSumStatement` unchanged: for
ranks `r`, `t` and bounds `A`, `B`, the abscissa `σ = openCellAbscissa r t A B =
2(r+t+1) + 2(r+1) max(A,0) + 2(t+1) max(B,0) + (r+1)(t+1) + 1` works uniformly: for every
`p`-adic field `K` (residue cardinality `q`), every unitary additive character `ψ` of conductor
`𝒪` (additive conductor `0`), every uniformizer `ϖ`, all `a ∈ (ℂˣ)^(r+1)`, `c ∈ (ℂˣ)^(t+1)` with
`|a_i| ≤ q^A` and `|c_j⁻¹| ≤ q^B`, every `s` with `σ < Re s` and every `f` with the stated
transformation law
`f(u(X) diag(m₁, m₂) k) = δ_P(m₁, m₂)^(1/2 + s/N) W°(m₁; a) W°(m₂; c)` (`k` integral,
`N = r + t + 2`),

`∑_(Y ∈ M_((t+1)×(r+1))(K) / M_((t+1)×(r+1))(𝒪)) f(w u'(Y)) conj ψ(Y_(t,0))
  = ∏_(i,j) (1 − a_i c_j⁻¹ q^(−(1+s)))`

as an unconditionally convergent sum.

## The implemented proof

Write `m = r + 1`, `n = t + 1`, `N = m + n`.

1. **Reduction to shell identities** (`OpenCellGeometry`, `OpenCellValue`, `OpenCellBounds`,
   `OpenCellCount`, `OpenCellSum`, `OpenCellAssembly`). For `w u'(Y) = lower(Y) w` the Iwasawa
   weights of the two blocks of `lower(Y)` are `λ ≥ 0` and `μ ≤ 0` with
   `∑ λ_i = −∑ μ_j = D(Y)` (the depth), and `ϖ^D Y` is integral, so there are at most
   `q^(m n D)` classes of depth `D`. Bounds for Shintani's formula give
   `|summand| ≤ C ρ^D` with `q^(m n) ρ ≤ 1/2` when `σ < Re s`; hence the sum converges
   absolutely and uniformly, and it suffices to prove the *shell identities*
   (`ShellIdentity`): the classes of depth `D` sum to the degree-`D` coefficient
   `shellCoefficient (pairParameter q a c s) D` of `∏_(i,j) (1 − a_i c_j⁻¹ q^(−(1+s)))`
   (`unramifiedOpenCellSum_of_shellIdentity`).

2. **Shell sums as Jacquet functions** (`OpenCellHaar`, `OpenCellLift`, `OpenCellJacquet`,
   `OpenCellPieces`, `OpenCellShellSum`). The function `f` is the lift of the Levi function
   `fullΦ a c s = δ_P^(1/2 + s/N) W°(·; a) ⊗ W°(·; c)`. Restricting a Levi function to
   first-block degree `v(det m₁) = D` gives its degree piece, and the Jacquet integral
   `J(g) = ∫ F(w u'(Y) g) conj ψ(Y_(t,0)) dY` (Haar measure with `vol(M(𝒪)) = 1`) of the degree-`D`
   piece at `g = 1` is the shell sum of depth `D` (`shellIdentity_iff`).

3. **Reduction to `s = 0`** (this module). The twist is absorbed into the parameters:
   `fullΦ a c s = fullΦ (q^(−s n/N) a) (q^(s m/N) c) 0` (`fullΦ_twist`, using
   `W°(m; X a) = X^(v(det m)) W°(m; a)` and `δ_P = q^(m v(det m₂) − n v(det m₁))`), and the pair
   parameters agree (`pairParameter_twist`). So the shell identities follow from the identities
   `CoreAt r t` at `s = 0`.

4. **`CoreAt r t` for all ranks** (`coreAt_all`, by induction on `r`).
   - *Rank one* (`OpenCellBaseMatrix` … `OpenCellBaseShell`). For `m = 1`, `ψ` of conductor `𝒪`
     and every Whittaker-type function `Ψ` on `GL_n`, the open-cell integral of the lift of
     `shellΦ d Ψ`, the Levi function `[v(det m₁) = d] Ψ(m₂)`, is computed by induction on `n`,
     peeling off the last coordinate (`integral_baseIntegrand`): it is
     `baseValue ϖ t d Ψ`, which is `0` for `d < 0` and for `d > n`, and for `0 ≤ d ≤ n` equals
     `(−1)^d q^(α) Ψ(ϖ^(κ))` with `κ = (0, …, 0, −1, …, −1)` (`d` entries `−1`).
     On the depth-`D` shell the normalized Levi function `δ^(1/2 + s/N) W°(·; a) ⊗ Ψ` is
     `baseCoef t D a s = (q^(−N D))^(1/2 + s/N) a₀^D` times `shellΦ D Ψ`, so its normalized
     degree-`D` integral is `baseCoef t D a s · baseValue ϖ t D Ψ`
     (`jacquetFunction_degreePiece_prodΦ_rankOne`). For example, with `m = n = 1`, `D = 1`,
     `s = 0`, `a₀ = 1` and `Ψ ≡ 1` on `GL_1`, the `shellΦ` integral is `−1` and the normalized
     integral is `−q⁻¹`. For `Ψ = W°(·; c)`, `baseCoef_mul_baseValue` identifies this product with
     the degree-`D` coefficient `(−a₀ q^(−(1+s)))^D e_D(c⁻¹)` in two cases: for `D ≤ t + 1` by the
     Schur evaluation `s_κ(c) = e_D(c⁻¹)` (`satakeSchur_baseKappa`, valid only in this range) and
     the constant identity `baseConstant_eq`; for `D > t + 1` both sides vanish, the base value by
     its support and the coefficient because there are no `D`-element subsets of the `t + 1`
     indices. This gives the shell identities (`shellIdentity_rankOne`, `coreAt_zero`).
   - *Shintani uniqueness and convergence* (`OpenCellHeckeSplit`, `OpenCellHecke`,
     `OpenCellHeckeRelation`, `OpenCellShintani`, `OpenCellJacquetConvergence`). The lift of
     `fullΦ` satisfies the minuscule Hecke relations of the Satake parameter
     `χ = (a q^(−s n/N), c q^(s m/N))`; when the Jacquet integrals converge at the torus points
     (true for parameters `(X a, c)` with `|X|` small), the Library's uniqueness theorem
     `Conductor.eq_smul_sphericalWhittaker` gives `J = J(1) W°(·; χ)`. With the degree
     pieces this yields the graded identity `∑_e X^e J_e(g) = J_(X a)(1) W°(g; χ(X a, c))`
     (`exists_hasSum_degreePiece`), and under `CoreAt r t` the value
     `J_(X a)(1) = ∏ (1 − X a_i c_j⁻¹ q⁻¹)` (`OpenCellGraded`).
   - *Three-block transitivity* (`OpenCellThreeBlockCoordinates`, `OpenCellThreeBlock`,
     `OpenCellThreeBlockSection`, `OpenCellThreeBlockMeasure`, `OpenCellThreeBlockFubini`). For
     the block sizes `(1, d + 1, t + 1)` and a parameter `a = (a₁, a')`, the open-cell integral
     through the `(d+2, t+1)` parabolic of the degree-`D` piece of `δ^(1/2) J_(e₁) ⊗ W°(·; c)`
     (`J_(e₁)` the Jacquet function of a degree piece on the first block) equals the integral
     through the `(1, d+t+2)` parabolic of the degree-`e₁` piece of `δ^(1/2) W°(·; a₁) ⊗ J'_(D−e₁)`
     (`jacquetFunction_threeBlock`). Both are the integral of the same three-block section over
     the open cell; on degree pieces every integral is over a compact set, and the two iterated
     integrals are related by the measure-preserving change of variables
     `(Y, z) ↦ (Y_a, [Y_b − Y_a z; z])`.
   - *The induction step* (`OpenCellPowerSeries`, `OpenCellInductionSeries`,
     `OpenCellInductionAlgebra`, `OpenCellInduction`). Using the rank-one formula on the
     right-hand route and the graded identities for the ranks `(0, d)` and `(d, t)`, the
     coefficients `A(D, e₁)` of transitivity have the two generating series of
     `threeCoef_series_left` and `threeCoef_series_right`; the product identity
     `sum_threeBlock_identity` and uniqueness of power-series coefficients give, for small
     nonzero `X`, `P_D(X a₁, a'; c) = T_D(X a₁, a'; c)` between the shell sum and the expected
     coefficient. Both sides are Laurent polynomials in `X`, so they agree at `X = 1`
     (`coreAt_step`).

5. **Conclusion.** `openCellShellIdentity` combines steps 2–4 for all data, and
   `unramifiedOpenCellSum` applies step 1.

The route differs from the sources: Casselman and Shalika obtain the value of the Whittaker
function of an unramified principal series for general groups (the full product over all
positive roots); here the two-block value, with the inducing Whittaker functions normalized at
the identity so that only the crossing roots contribute, is proved directly by a rank-one
computation and induction in stages, with Shintani's formula and the Library's uniqueness
theorem for spherical Whittaker functions.

## Modules

The proof uses the helper modules, all in `Langlands.Representation.Shahidi`, in dependency
order: `OpenCellGeometry`, `OpenCellValue`, `OpenCellBounds`, `OpenCellCount`, `OpenCellSum`,
`OpenCellAssembly`, `OpenCellHaar`, `OpenCellColumn`, `OpenCellLift`, `OpenCellBaseMatrix`,
`OpenCellBaseLift`, `OpenCellBaseStep`, `OpenCellBaseValues`, `OpenCellBaseInduction`,
`OpenCellBaseSchur`, `OpenCellBaseCoef`, `OpenCellBaseShell`, `OpenCellHeckeSplit`,
`OpenCellHecke`, `OpenCellHeckeRelation`, `OpenCellJacquet`, `OpenCellShintani`,
`OpenCellJacquetConvergence`, `OpenCellPieces`, `OpenCellThreeBlockCoordinates`,
`OpenCellShellSum`, `OpenCellPowerSeries`, `OpenCellGraded`, `OpenCellThreeBlock`,
`OpenCellThreeBlockSection`, `OpenCellThreeBlockMeasure`, `OpenCellThreeBlockFubini`,
`OpenCellInductionSeries`, `OpenCellInductionAlgebra`, `OpenCellInduction`. Each has a page
beside it.

## Sources

- W. Casselman and J. Shalika, *The unramified principal series of p-adic groups II. The
  Whittaker function*, Compositio Math. 41 (1980) (`casselman-shalika-1980-whittaker`), §5 (from
  printed p. 223) and Theorem 5.4, printed p. 227 (PDF page 22): the unramified Whittaker
  function satisfies `W_χ(1) = ζ(χ)`. For split `GL_N` (the first local-root case, `q_α = q`,
  `q_(α/2) = 1`) this specializes to `∏_(α > 0) (1 − q^(−1) χ(a_α))`.
- F. Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981) (`shahidi-1981-certain-l`),
  §2.3, printed pp. 324–325 (PDF pages 29–30): for `G = GL_(n+m)` and the Levi `GL_n × GL_m`
  the adjoint action of the L-group of the Levi on the Lie algebra of the dual unipotent radical
  is irreducible, the tensor product of the standard representation of `GL_n(ℂ)` and the
  contragredient of the standard representation of `GL_m(ℂ)`, with the single constant
  `a₁ = m + n = N`. Proof of Theorem 5.1, printed p. 352 (PDF page 57):
  `W_v(e_v) = ∏_j L(1 + a_j s, π_v, r_j)⁻¹` for the induced Whittaker functional, with the
  spherical value of the inducing data normalized to one. The target twists by `δ_P^(s/N)`, so
  in its normalization the shift `1 + a₁ s` of the source becomes `1 + s`; for the crossing roots
  the twisted ratio is `a_i c_j⁻¹ q^(−s)`, and the identity proved here is the resulting product
  for the upper two-block parabolic. Because the inducing Whittaker functions `W°(·; a)`,
  `W°(·; c)` are normalized to `1` at the identity, the factors `1 − q^(−1) χ(a_α)` of the roots
  `α` inside the two blocks, which occur in the full split `GL_N` product of Casselman–Shalika,
  are removed: only the `(r+1)(t+1)` crossing roots remain. (For block sizes `(2, 1)` the
  Borel value has the extra factor `1 − q^(−1) a₀/a₁`.)
- F. Shahidi, *Fourier transforms of intertwining operators and Plancherel measures for GL(n)*,
  Amer. J. Math. 106 (1984) (`shahidi-1984-fourier`), notation and equation (0.2), printed
  pp. 70–72: the Jacquet integral in the coordinates `w`, `U'` used here (block Weyl matrix,
  exchanged radical and conjugated standard character; the only simple-root entry of the
  radical is the last row and first column of `Y`).
- T. Shintani, *On an explicit formula for class-1 "Whittaker functions" on GL_n over P-adic
  fields*, Proc. Japan Acad. 52 (1976) (`shintani-1976-class-one-whittaker`), §1, equations
  (1)–(4), printed pp. 180–181: the
  characterization (equivariance, Hecke eigen-equations, value `1` at the identity) and the
  explicit formula behind the Library's `GeneralLinear.Spherical.sphericalWhittaker`.

# The `O(N)`-integral in coordinates of a standard parabolic subgroup of `GL_N(ℝ)`

Lean module: `Langlands.Representation.Archimedean.RealLeviParabolicIntegrationStatement`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It
states one proposition, `RealLeviParabolicIntegrationStatement`, and does not prove it. The module
also defines block diagonal matrices and proves a few elementary lemmas about them. The proposition
is the integration formula for the Langlands lemma along an arbitrary standard parabolic subgroup
`Q` of `GL_N(ℝ)`. It generalizes the published `RealBlockParabolicIntegrationStatement` (module
`RealBlockParabolicIntegrationStatement`), which is the case of two blocks. See "Use" below.

The block data and the opposite unipotent radical come from the module
`RealLeviChartIntegralStatement`: `c` blocks of sizes `sz : Fin c → ℕ`, positions
`Fin (∑ i, sz i)` listed block after block (`finSigmaFinEquiv`), `pos sz i a` the position of the
index `a` of the block `i`, `Coord sz` the pairs `(p, q)` of positions with `cls q < cls p`, and
`lowerGL sz X = n̄(X) ∈ GL_N(ℝ)` the unipotent lower block triangular matrix with the entries `X`
below the diagonal blocks.

## Definitions

In the namespace `Langlands.Archimedean.RealLeviChart`:

* `blockDiagHom sz` is the ring homomorphism `(A_0, …, A_{c−1}) ↦ diag(A_0, …, A_{c−1})` from
  `∀ i, Matrix (Fin (sz i)) (Fin (sz i)) ℝ` to the `N × N` matrices. It is Mathlib's
  `blockDiagonal'RingHom` followed by the reindexing `Matrix.reindexAlgEquiv` along
  `finSigmaFinEquiv`.
* `blockDiagHom_apply` gives the formula `reindex finSigmaFinEquiv finSigmaFinEquiv
  (blockDiagonal' A)`. `blockDiagHom_pos_pos_self` says that the entry at
  `(pos i a, pos i b)` is `A i a b`. `blockDiagHom_pos_pos_of_ne` says that the entry at
  `(pos i a, pos j b)` is `0` for `i ≠ j`.
* `blockDiagGL sz` is the group homomorphism
  `(g_0, …, g_{c−1}) ↦ diag(g_0, …, g_{c−1})` from `∀ i, GL_{sz_i}(ℝ)` to `GL_N(ℝ)`.
  It is `Units.map` of `blockDiagHom sz`, composed with Mathlib's `MulEquiv.piUnits.symm`, and
  `blockDiagGL_val` says that its underlying matrix is `blockDiagHom sz` of the underlying matrices.

## The statement

`RealLeviParabolicIntegrationStatement`: for all `c` and all block sizes `sz : Fin c → ℕ`
(`N = ∑ i, sz i`) there is a real `C > 0` with the following property. Let `F : GL_N(ℝ) → ℂ` be
smooth (`ContMDiff` for the manifold structure `matrixModel ℝ N` of `GL_N(ℝ)`) and satisfy
`F(diag(z) u g) = ∏ᵢ |zᵢ|^{(N−1) − 2i} F(g)` for all `z ∈ (ℝˣ)^N`, `u` upper unipotent and `g`.
This is the published `MaximalParabolicIntegration.IsModulusCovariant`: `F` lies in the smooth
principal series of the modulus character of the upper triangular Borel subgroup. Then:

1. for every `κ = (κ_0, …, κ_{c−1})` with `κ_i ∈ O(sz_i)` (`unitaryCompact ℝ (sz i)`), the function
   `X ↦ F(n̄(X) diag(κ_0, …, κ_{c−1}))` is integrable on `Coord sz → ℝ` (product Lebesgue measure);
2. `∫_{O(N)} F(κ) dκ = C · ∫_{K_M} ∫_{Coord sz → ℝ} F(n̄(X) diag(κ_0, …, κ_{c−1})) dX dκ`.

Here the integral over `O(N)` uses the Haar probability measure `RealPrincipalSeriesDuality.haarK N`.
The integral over `K_M = ∏ᵢ O(sz_i)` (the type `∀ i, unitaryCompact ℝ (sz i)`) uses the product
`Measure.pi` of the Haar probability measures `haarK (sz i)`. All the orthogonal groups carry
the Borel σ-algebra `measurableSpaceK`.

Edge cases. If `c ≤ 1`, then `Coord sz` is empty and `n̄(X) = 1`. For `c = 1` the map
`κ_0 ↦ diag(κ_0)` is a reindexing isomorphism `O(sz_0) ≅ O(N)` of compact groups, which carries
the Haar probability measure to the Haar probability measure, so the formula holds with `C = 1`.
For `c = 0`, and more generally for `N = 0`, both sides are `F(1)` and `C = 1`. For `c = 2` with blocks of sizes `a` and
`k`, the statement is the published `RealBlockParabolicIntegrationStatement` for `a, k`, with
`X ∈ M_{k×a}(ℝ)` and `κ_0 ∈ O(a)`, `κ_1 ∈ O(k)`, up to the identification of the coordinates and of
`Measure.pi` over `Fin 2` with the iterated integral.

## Provenance

The statement is derived. It is the standard integration formula relating the Haar measure of
`K = O(N)` to the Lebesgue measure of `N̄_Q × K_M` on functions induced from the modulus
character. It holds because `B N̄_Q K_M = Q N̄_Q` is open and dense in `GL_N(ℝ)` with a null
complement. No specific literature statement is claimed, and the constant `C` is not identified.

Why it is true (the same argument as for two blocks; see the Markdown of
`RealBlockParabolicIntegrationStatement`):

1. Average `F` over `K_M` on the left: `F^♮(g) = ∫_{K_M} F(m g) dm`. By the published
   `KIntegralInvariance` for every block `GL_{sz_i}(ℝ)`, the average is left `Q`-covariant with the
   modulus character of `Q`, and `∫_K F = ∫_K F^♮`.
2. For continuous functions in the principal series of the modulus character of `Q`, the
   `K`-integral is a positive multiple of the `N̄_Q`-integral. Both are `GL_N(ℝ)`-invariant
   functionals on this space.
3. `diag(κ) n̄(X) = n̄(Ad(diag κ) X) diag(κ)`, and conjugation by `diag(κ)` maps the coordinates
   `X` by a linear map that preserves the Frobenius norm, hence preserves Lebesgue measure. So
   `F^♮(n̄(X)) = ∫_{K_M} F(n̄(Ad(κ)X) diag(κ)) dκ`, and Fubini gives the order of integration in the
   statement.

Integrability for every (not only almost every) `κ` follows from
`|F(n̄(X) κ)| ≤ sup_K |F| · E(n̄(X))`. Here
`E(g) = |det g|^{N−1} · ∏_{l=1}^{N−1} G_l(g)^{−1}`, with `G_l` the Gram determinants of the module
`RealLeviChartIntegralStatement`. It is right `K`-invariant, because `G_l(g k) = G_l(g)`. It
satisfies `E(b g) = δ_B(b) E(g)` for every upper triangular `b` with diagonal `t`, because
`G_l(b g) = (∏_{i ≥ l} t_i²) G_l(g)`, and `|det b|^{N−1} ∏_{l=1}^{N−1} ∏_{i ≥ l} |t_i|^{−2}` is
`∏_i |t_i|^{N−1−2i} = δ_B(b)`. With the Iwasawa decomposition `g = b k` this gives the bound
`|F(g)| = δ_B(b) |F(k)| ≤ sup_K |F| · E(g)`. The determinant factor matters in general (for
`N = 2`, `E(2·1) = 1` while `G_1(2·1)^{−1} = 1/4`), but every matrix to which the bound is applied
below (`n̄(X)`, `n̄_B(Y)`, `m(Z)`) is lower unitriangular, so has determinant `1`, and there
`E = ∏_{l=1}^{N−1} G_l^{−1}`. The `N̄_Q`-integral of `E(n̄(X))` is finite by
`RealLeviChartIntegrableStatement` with every `γ_l = −1` (the factor `l = 0` is
`G_0(n̄(X))^{−1} = 1`).

Intended proof (for a proof task). It needs no induction on the number `c` of blocks and does not
use `RealBlockParabolicIntegrationStatement`. Write `n̄_B(Y)` for the lower unitriangular `N × N`
matrix with the entries `Y_{pq}` (`q < p`) below the diagonal, and `m(Z)` for the block diagonal
lower unitriangular matrix with the entries `Z_{pq}` (`q < p` in the same block) inside the
diagonal blocks.

1. Borel coordinates: `∫_{O(N)} F = C_N ∫_Y F(n̄_B(Y)) dY` with `C_N > 0`. Induction on `N` with
   the Library's maximal-parabolic formula `MaximalParabolicIntegration.integral_eq_chart`
   (blocks of sizes `N − 1` and `1`), applied to the Levi slices of `F`. The induction step uses
   `diag(n̄_B(Y'), 1) J(v) = n̄_B(Y)`, where `J(v)` is the identity matrix with the first `N − 1`
   entries of its last row replaced by `v`, and `Y` consists of `Y'` and the last row `v`.
2. Levi-Borel coordinates: `∫_{K_M} F(diag(κ)) dκ = C_M ∫_Z F(m(Z)) dZ` with `C_M > 0`. Apply
   step 1 to every block, through the Levi slices of `F` (whose modulus factors are `1` on
   `K_M` and on `m(Z)`), one block after the other.
3. For each `κ`, the substitution `X ↦ Ad(diag κ) X` preserves Lebesgue measure (as in "Why it
   is true", step 3), and `diag(κ) n̄(X) = n̄(Ad(diag κ) X) diag(κ)`. With Fubini,
   `∫_{K_M} ∫_X F(n̄(X) diag(κ)) dX dκ = ∫_X ∫_{K_M} F(diag(κ) n̄(X)) dκ dX`. Step 2, applied to
   the right translate `F(· n̄(X))`, turns this into `C_M ∫_X ∫_Z F(m(Z) n̄(X)) dZ dX`.
4. The shear. Inside the blocks the entries of `m(Z) n̄(X)` are those of `m(Z)`. Below the blocks
   they are `X'_{pq} = ∑_r m(Z)_{pr} X_{rq}`, the entries of `m(Z) (n̄(X) − 1)`. So
   `m(Z) n̄(X) = n̄_B(Y)`, where `Y` consists of `Z` and `X'`. For fixed `Z`, the linear map
   `X ↦ X'` is block triangular, with identity diagonal blocks, for the order of the coordinates
   by decreasing row, because `m(Z)` is lower unitriangular. So it has determinant `1`, and the
   map `(Z, X) ↦ Y` preserves Lebesgue measure. This map is not orthogonal in general. Hence
   `∫_X ∫_Z F(m(Z) n̄(X)) dZ dX = ∫_Y F(n̄_B(Y)) dY`.
5. By steps 1, 3 and 4, the formula holds with `C = C_N / C_M`.

The Fubini steps use the integrable bound `sup_K |F| · E(n̄(X))` above and its analogues
`sup_K |F| · E(n̄_B(Y))` and `sup_K |F| · E(m(Z))`. The integrability of `E(n̄_B(Y))` is the
instance of `RealLeviChartIntegrableStatement` with all blocks of size `1`. `E(m(Z))` is the
product over the blocks of the analogous functions of the blocks, because `m(Z)` is block
diagonal with unipotent blocks, so its integrability follows from the same instances for the
blocks.

## Use

In Task 6749 the formula is applied to `F(y) = u(y) h(y)`, with `h` in a principal series and `u`
in its dual, and to the translates of `F` by the elements `d_s = diag(s^{cls p})` of the center of
the Levi factor. It computes the leading term of the `O(N)`-pairing in the single-step Langlands
lemma along the parabolic subgroup `Q` whose blocks are the tie classes of the Langlands order.

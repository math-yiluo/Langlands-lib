# Proof that a Taylor condition on `O(n)` makes principal-series functions polynomial along a root group

Lean module: `Langlands.Representation.Archimedean.RealTaylorLeftPolynomialProof`.
Main theorem: `Langlands.Archimedean.realTaylorLeftPolynomial : RealTaylorLeftPolynomialStatement`.
The helper lemmas are in the namespace
`Langlands.Archimedean.RealTaylorLeftPolynomialProof`.

## The statement proved

`RealTaylorLeftPolynomialStatement` (module `RealTaylorLeftPolynomial`) concerns the following
data:

- `p + 1 < n` and `k : ℕ`;
- functions `χ : ℕ → ℝˣ → ℂ` with `χ_{p+1}(x) = x^k χ_p(x)` for `x > 0`;
- a function `h` in the smooth principal series `principalSeries ℝ n χ`.

Write `E = E_{p+1,p}` (`lowerRootMatrix`) and `e(t) = 1 + t E` (`lowerRootElement`). Suppose that
for every `κ ∈ O(n)` the `k`-fold right derivative along `E` at `1` of the right translate of `h`
by `κ` vanishes. The statement then asserts: for every `g`, `t ↦ h(e(t) g)` is a complex
polynomial in `t` of degree `< k`.

## Notation

- `φ_g(t) = h(e(t) g)` is the orbit function (`orbitFun`).
- `H(g) = φ_g^{(k)}(0)`, the `k`-th derivative at `0` (`iteratedDeriv`).
- `c(a) = principalSeriesCharacter ℝ n χ a` is the factor in `h(diag(a) u g) = c(a) h(g)`.
- `U(x) = 1 + x E_{p,p+1}` (`upperRootElement`).

## Proof

**Case `k = 0`.** The hypothesis says `h(κ) = 0` for `κ ∈ O(n)`. By
`eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact` (module `RealStandardModuleAdmissible`),
`h = 0`, and `q = 0` works.

**Case `k ≥ 1`.** The steps follow.

1. **The hypothesis is `H(κ) = 0`.** For a smooth `F`, `s ↦ F(e(s))` has derivative
   `(R(E) F)(e(t))` at `t` (`hasDerivAt_lowerRoot`). The proof extends `F` to all matrices
   (`unitsExtension`), uses `rightDerivative_eq_fderiv` and the chain rule, and uses
   `e(t) E = E`, since `E² = 0`. By induction with `contMDiff_rightDerivative`, the `m`-th
   derivative of `s ↦ F(e(s))` is `s ↦ (R(E)^m F)(e(s))` (`iteratedDeriv_lowerRoot`). Taking `F`
   the right translate of `h` by `κ` and `s = 0` gives
   `iterate_rightDerivative_rightTranslation`. In particular `φ_g` is smooth
   (`contDiff_orbitFun`).
2. **Torus.** `e(t) diag(a) = diag(a) e(r t)` with `r = a_p / a_{p+1}`
   (`lowerRootElement_mul_diagonalUnits`, checked entrywise). Hence
   `φ_{diag(a) g}(t) = c(a) φ_g(r t)` (`orbitFun_diagonalUnits`), and
   `H(diag(a) g) = c(a) r^k H(g)` by `iteratedDeriv_const_mul_field` and
   `iteratedDeriv_comp_const_smul`.
3. **Unipotent radical.** Let `N` be upper unipotent with `N_{p,p+1} = 0`. Then
   `e(t) N e(-t)` is upper unipotent (`conj_mem_upperUnipotent`). Its entries are computed in
   `conj_lowerRoot_apply`, and the case analysis uses `N_{p,p+1} = 0`. Hence
   `φ_{N g} = c(1) φ_g` (`orbitFun_unipotent`) and `H(N g) = c(1) H(g)`.
4. **Decomposition of `u`.** Every upper unipotent `u` is `N U(x)` with `x = u_{p,p+1}` and `N`
   as in step 3 (`exists_upperUnipotent_decomp`).
5. **Root group.** Let `y = 1 + t x ≠ 0`. Then (`lowerRootElement_mul_upperRootElement`)
   `e(t) U(x) = diag(y⁻¹ at p, y at p+1) U(x y) e(t / y)`. This is checked entrywise after
   expanding both sides with the products of matrix units. The character lemma
   `principalSeriesCharacter_mulSingle_idxQ` says the following, for `y > 0`: the factor of `y`
   at position `p + 1` is `y^(k-1)` times the factor of `y` at position `p`. Its proof reindexes
   the product by the transposition of `p` and `p + 1`. It uses `χ_{p+1}(y) = y^k χ_p(y)`,
   `χ_{p+1}(1) = χ_p(1)` and `|y|^{s - 1} = |y|^s / y`. Applying the covariance twice, the
   factors of `y⁻¹` and `y` at position `p` cancel. This gives (`orbitFun_upperRoot`), for
   `1 + t x > 0`:
   `φ_{U(x) g}(t) = (1 + t x)^(k-1) φ_g(t / (1 + t x))`.
6. **Bol's identity.** `iteratedDeriv_bol`: if `ψ` is `C^k` with `k ≥ 1`, then the `k`-th
   derivative at `0` of `t ↦ (1 + t x)^(k-1) ψ(t / (1 + t x))` is `ψ^{(k)}(0)`. Proof:
   - Let `T` be the Taylor polynomial of order `k` of `ψ` at `0` (`taylorPoly`), with
     coefficients `c_j`. Then `ψ - T = o(s^k)` (`taylor_isLittleO_univ`).
   - Composing with `s = t / (1 + t x) = O(t)` and multiplying by the bounded factor
     `(1 + t x)^(k-1)` gives an `o(t^k)` term.
   - The rest is computed exactly (`bolPoly_identity`). Here
     `W = ∑_{j ≤ k} c_j X^j (1 + x X)^(k-1-j)`, with natural subtraction, so the term `j = k` is
     `c_k X^k`. Then `(1 + t x)^(k-1) T(t / (1 + t x)) - W(t) = c_k t^k ((1 + t x)⁻¹ - 1)`, which is
     also `o(t^k)`.
   - `W` has degree `≤ k` and `t^k`-coefficient `c_k` (`bolPoly_coeff`).
   - Lemma `iteratedDeriv_eq_of_isLittleO` says: if `f` is `C^k` on an open interval around `0`
     and `f - q = o(t^k)` for a polynomial `q` of degree `≤ k`, then `f^{(k)}(0) = k! q_k`.
     Its proof compares `q` with the Taylor polynomial of `f` (`taylor_isLittleO`). It uses
     `eq_zero_of_isLittleO_pow`: a polynomial of degree `≤ k` that is `o(t^k)` on the punctured
     neighbourhood of `0` is zero. That lemma is proved by induction on `k`, dividing by `X`.
     Applied to `W`, it gives `k! c_k = ψ^{(k)}(0)`.

   With step 5, the two functions agree near `0` (`EventuallyEq.iteratedDeriv_eq`). So
   `H(U(x) g) = H(g)`.
7. **`H = 0`.** By the Iwasawa decomposition
   (`exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact`), every `g` is
   `diag(a) N U(x) κ` with `κ ∈ O(n)`. By steps 1–6, `H(g)` is a multiple of `H(κ) = 0`.
8. **Shift.** `φ_g(s + t) = φ_{e(t) g}(s)`, by `e(s) e(t) = e(s + t)`. So `φ_g^{(k)}(t) =
   H(e(t) g) = 0` for every `t` (`iteratedDeriv_orbitFun_shift`, `iteratedDeriv_comp_add_const`).
9. **Polynomiality.** `exists_poly_of_iteratedDeriv_eq_zero`: a smooth `f : ℝ → ℂ` whose `k`-th
   derivative vanishes identically equals its Taylor polynomial of order `k - 1`, which has
   degree `< k`. This follows from Taylor's theorem with integral remainder
   (`taylor_integral_remainder`); `iteratedDerivWithin_eq_iteratedDeriv` converts derivatives
   within `[0, t]`. Applied to `φ_g`, it gives the polynomial `q`.

## Remarks

The route is the classical one: `H` is the image of `h` under the `k`-th power of the left
derivative along `E`. With the exponent condition it is invariant under the upper root group;
this is Bol's identity. It transforms under the torus and the unipotent radical of the
parabolic subgroup by scalars, and it vanishes on `O(n)`. The Lean proof avoids differentiating
in two variables: it uses only one-variable Taylor expansions and exact matrix identities.

## Provenance and authorship

This is an internal proof of the existing Library statement, developed by Worker 5731
in Task 7070 and reused from its shared draft revision 1. All calculus, matrix, and
character helper claims are proved in this module from the imported Library and
Mathlib results. Worker 264 checked the exact target and protected inputs and
prepared this pair for independent review in Task 7254. The functions `χ` retain
the full scope of the statement: no multiplicativity or normalization is assumed.
The cancellation in `orbitFun_upperRoot` follows directly from the covariance of
`h`, so it needs neither property of `χ`.

# Reduction of the complex-place Rankin–Selberg functional equation to local premises

Lean module: `Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction`
(namespace `Langlands.Global.RankinSelbergGlobal`; the inverse character is in
`Langlands.LocalFactor.Archimedean.ComplexCharacterData`; universe `u` for the number field).

## Statement

```
def ComplexPlaceFunctionalEquationReductionStatement : Prop :=
  ComplexLocalUnequalFunctionalEquationStatement →
    ComplexLocalEqualFunctionalEquationStatement → ComplexPlaceWhittakerModelStatement.{u} →
    ComplexPlaceMinusOneStatement.{u} → ComplexPlaceContragredientParameterStatement.{u} →
    ComplexPlaceFunctionalEquationStatement.{u}
```

The module also states the reduction for each rank separately:

* `ComplexUnequalFunctionalEquationReductionStatement`: the unequal-rank local premise, the
  bridge, the minus-one and the contragredient premises imply
  `ComplexUnequalFunctionalEquationStatement`;
* `ComplexEqualFunctionalEquationReductionStatement`: the same with the equal-rank local
  premise and `ComplexEqualFunctionalEquationStatement`.

`ComplexPlaceFunctionalEquationStatement` (Library module
`Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement`) is the conjunction of
the two rank statements. They are Jacquet 2009, Theorem 2.1 (i)–(iii), at one complex place
`w` of a number field `F`, for the archimedean restrictions `W(g) = W_x(ι_w(g) a)` of global
Whittaker functions of actual cuspidal realizations (`IsComplexPlaceWhittaker`).

The theorems `complexUnequalFunctionalEquationReduction`,
`complexEqualFunctionalEquationReduction` and `complexPlaceFunctionalEquationReduction` prove
the three implications. None of the five premises is proved in this module.

## Local objects

All objects below are new. They are used only to state the premises.

* `ComplexCharacterData.inv d`: the inverse character. Its character is
  `z ↦ χ(z)⁻¹` (`(ContinuousMonoidHom.inv ℂˣ).comp d.character`), its weight is `-d.weight`
  and its exponent is `-d.exponent`. The field `character_eq` follows from that of `d`:
  `((z/‖z‖)^k ‖z‖^(2e))⁻¹ = (z/‖z‖)^(-k) ‖z‖^(2(-e))`. The simp lemmas `inv_weight`,
  `inv_exponent` and the lemma `inv_character_apply` (`χ⁻¹(z) = χ(z)⁻¹`) are proved.
* `complexCentralSign ds = ∏_j χ_j(-1)`, the product over the list of the characters at
  `-1 ∈ ℂˣ`. For the standard module of `ds` (Library `complexStandardModule`), `-1 ∈ GL_n(ℂ)`
  acts by this scalar: its functions satisfy `f(diag(a) u g) = ∏_j χ_j(a_j) δ^(1/2)(a) f(g)`,
  and `δ^(1/2)(-1) = 1`. This is Jacquet's `ω_(π_(σ,u))(-1)`.
* `complexMatrixHeight g = ∑_(i,j) (|g_ij|² + |(g⁻¹)_ij|²)`. This is Jacquet's height
  `‖g‖_H = Tr(g ᵗg) + Tr(g⁻¹ g^ι)` of (2.1), p.3, read for `GL_n(ℂ)` with the conjugate
  transpose. Only the class of moderate-growth bounds it defines matters below.
* `complexWhittakerCharacter a u = ψ_a(∑_(i<r) u_(i,i+1))` with
  `ψ_a = complexScaledCharacter a : z ↦ exp(2πi Tr_(ℂ/ℝ)(a z))`. On the upper unipotent group
  this is Jacquet's `θ_ψ` of (2.2), p.3, for `ψ = ψ_a`. The function is defined on all of
  `GL_(r+1)(ℂ)`; the premises use it only on `N_(r+1)(ℂ)`.
* `IsComplexWhittakerIntertwiner r ds a B`, for a linear map `B` from the `U(r+1)`-finite
  functions of the standard module of `ds` (Library `complexStandardKFinite (r + 1) ds`) to
  functions on `GL_(r+1)(ℂ)`. It is the conjunction of five clauses, for every `f`:
  1. `B f (u g) = complexWhittakerCharacter a u · B f (g)` for `u` in
     `GeneralLinear.upperUnipotent (r + 1) ℂ`;
  2. `B f` is smooth (`ContMDiff` for the Library's `matrixModel ℂ (r + 1)`);
  3. moderate growth: `‖B f (g)‖ ≤ C · complexMatrixHeight g ^ N` for some `C : ℝ`, `N : ℕ`;
  4. for `k ∈ U(r+1)` and `f'` with the same underlying function as the right translate of
     `f` by `k`, `B f'` is the right translate of `B f` by `k`;
  5. for a real direction `X ∈ 𝔤𝔩_(r+1)(ℂ)` and `f'` with the same underlying function as the
     right derivative `rightDerivative X f`, `B f' = rightDerivative X (B f)`.

  Clauses 4 and 5 say that `B` is a `(𝔤, K)`-module map. They are stated with a second
  function `f'` so that no membership proof appears in the statement; this is the shape in
  which the Library's `HasComplexPlaceParameter` provides its equivariance.
* `complexWhittakerModel r ds a`: the complex span (`⨆`) of the ranges of all such `B`. It is
  a submodule of the functions on `GL_(r+1)(ℂ)`.

## The premises

### Local functional equations

`ComplexLocalUnequalFunctionalEquationStatement`: for `t < r`, lists `d`, `d'` of lengths
`r + 1`, `t + 1`, `a ∈ ℂˣ`, `D : ComplexQuotientMeasureData t`, and `W ∈ complexWhittakerModel r
d a`, `W' ∈ complexWhittakerModel t d' (-a)`, there are `σ`, `M`, `Md` with the nine clauses of
the conclusion of `ComplexUnequalFunctionalEquationStatement`. The only differences are in the
last clause:

* the dual `L`-factor is that of `d.map inv`, `d'.map inv` instead of that of the contragredient
  parameters `dd`, `dd'`;
* the sign is `complexCentralSign d' ^ r` instead of `complexMinusOneScalar T' w ^ r`.

The integrals, measures, `ε`-factor and the forms of all clauses are copied from the target.

`ComplexLocalEqualFunctionalEquationStatement`: the same for lists `d`, `d'` of length `r + 1`,
`D : ComplexQuotientMeasureData r`, a Schwartz function `Φ`, and the clauses of the conclusion of
`ComplexEqualFunctionalEquationStatement`.

Why they are expected to hold. They are Jacquet 2009, Theorem 2.1 (i)–(iii) (p.6), for the
generic induced representations `π_(σ,u)` (p.4) with all `d_i = 1`, in the conventions of the
target:

* Jacquet's theorem holds for every `u`, with no irreducibility assumption. Every list of
  characters of `ℂˣ` is of the form `σ_i α^(u_i)` with `σ_i` unitary. Jacquet induces
  normalized from the lower Borel subgroup; the Library's standard module is normalized
  induction from the upper Borel subgroup. The map `f ↦ f(w_n ·)` identifies the upper
  induced representation of `(χ_1, …, χ_n)` with the lower induced representation of
  `(χ_n, …, χ_1)`, and the `L`- and `ε`-factors of a pair of lists are invariant under
  permutations of the lists (Library `complexPairLFactor_perm`).
* `ω_(π_(σ',u'))(-1) = ∏_j χ'_j(-1) = complexCentralSign d'`, and the dual `L`-factor of
  Jacquet's equation is `L(1 − s, σ̃_u ⊗ σ̃'_(u'))`, the factor of the inverse characters.
* The conversion of Jacquet's signs and Fourier transform to the target's sign `ω'(−1)^r` and
  the target's `ε` is in the Markdown of
  `ArchimedeanFunctionalEquationStatement` (section "The central sign in the Library's
  conventions"); it applies unchanged here.
* Membership in Jacquet's `W(π_(σ,u) : ψ_a)`: let `B` satisfy `IsComplexWhittakerIntertwiner`.
  Clauses 1 and 5 give that `f ↦ B f (1)` is a `θ`-equivariant linear form on the
  `(𝔤, K)`-module of `K`-finite vectors. Clause 3 (moderate growth) lets it extend to a
  continuous `ψ`-form on the Casselman–Wallach completion, which is Jacquet's `I_(σ,u)`
  (Casselman–Wallach, as recalled on p.3; Wallach, *Real reductive groups II*, ch. 11). By
  uniqueness of the `ψ`-form (p.4, from Wallach II, Theorem 15.4.1) it is `c λ`. Then
  `B f` and `c W_f` have the same derivatives at `1` of all orders (clauses 4 and 5). Both are
  `Z(𝔤)`-finite and `K`-finite smooth functions, hence real-analytic, and `GL_(r+1)(ℂ)` is
  connected, so `B f = c W_f`. Hence `complexWhittakerModel r d a ⊆ W(π_(σ,u) : ψ_a)`. For
  `-a`, `ψ_(-a) = ψ̄_a`, which gives the model `W(π' : ψ̄)` of the second function.

### Bridge

`ComplexPlaceWhittakerModelStatement`: let `T` be an actual cuspidal realization of `GL_(r+1)`,
`ψ` a unitary character of `𝔸_F` trivial on `F` with component `ψ_a` at the complex place `w`
(`IsComplexAdditiveComponent`), and `d` with `HasComplexPlaceParameter T.realization w d`. Every
`W` with `IsComplexPlaceWhittaker F T ψ.complex w W` lies in `complexWhittakerModel r d a`, and
every `W` with `IsComplexPlaceWhittaker F T ψ.complex⁻¹ w W` lies in `complexWhittakerModel r d
(-a)`.

Why it is expected to hold. Write `W(g) = W_x(ι_w(g) b)` with `x ∈ T.Space` and a finite adelic
point `b`.

* `T` is irreducible and cuspidal, so as a `(𝔤_w, K_w)`-module `T.Space` is a direct sum of
  copies of the irreducible generic component `π_w` (tensor product theorem).
* `HasComplexPlaceParameter` gives an injective `(𝔤, K)`-map `A` from the `K`-finite standard
  module of `d` into `T.Space`. Its image is semisimple and `π_w`-isotypic. The minimal
  `U(r+1)`-type of a principal series of `GL_(r+1)(ℂ)` has multiplicity one, so the standard
  module is irreducible and isomorphic to `π_w`.
* Hence `x` is a finite sum `∑ A_i(f_i)` of images of injective `(𝔤, K)`-maps `A_i` from the
  standard module of `d`, and `W = ∑ B_i(f_i)` with `B_i f = (g ↦ W_(A_i f)(ι_w(g) b))`.
* Each `B_i` is a Whittaker intertwiner. Clause 1: `ψ(ι_w(u)) = ψ_a(∑ u_(i,i+1))` for
  `u ∈ N(ℂ)`. Clause 2: automorphic forms are smooth at `w`. Clause 3 (polynomial growth, with
  some `C` and `N` depending on `f`): no unitary central character is assumed, so the cusp
  form `φ = A_i f` need not be bounded. (For `GL_1` over an imaginary quadratic field, the
  realization by the normalized idelic norm is allowed, its parameter is `χ(z) = |z|²`, and
  its Whittaker restriction `W(z) = |z|²` is unbounded.) Instead use that `φ` is an
  automorphic form: on each slice `a ↦ φ(a b')` (`a` in the archimedean group, `b'` a finite
  adelic point) it is bounded by `C_(b') H(a)^(d_(b'))`, with `H` the Library's archimedean
  height `ArchimedeanGL.matrixHeight` (Library `IsAutomorphicForm`, `HasPolynomialGrowth`).
  The Whittaker coefficient is `W_φ(h) = ∫_(N(F)\N(𝔸)) φ(n h) ψ(n)⁻¹ dn` with `|ψ| = 1`, and
  the integral can be taken over a compact set `Ω_∞ × Ω_f ⊂ N(𝔸_∞) × N(𝔸_f)` of
  representatives. For `h = ι_w(g) b` and `n = n_∞ n_f`, `φ(n h) = φ(n_∞ ι_w(g) · n_f b)`.
  `φ` is right invariant under an open compact subgroup `K_f`, and the compact set `Ω_f b` is
  covered by finitely many cosets `b'_j K_f` (`j = 1, …, m`), so for `n_f ∈ Ω_f` the value
  `φ(a · n_f b)` equals `φ(a b'_j)` for some `j`. The height satisfies `H(n_∞ a) ≤ c H(a)` for
  `n_∞` in the compact `Ω_∞` (norms of a product and of its inverse are submultiplicative). The
  entries of `g` and `g⁻¹` are bounded by `‖g‖_H^(1/2)`, and Jacquet's `‖g‖_H` is `≥ 2`
  (by Cauchy–Schwarz, `r + 1 = tr(g g⁻¹)` is at most the product of the Frobenius norms of `g`
  and `g⁻¹`), so `H(ι_w(g)) ≤ c' ‖g‖_H`. Hence
  `|W(g)| ≤ C ‖g‖_H^N` with `N = max_j d_(b'_j)`. In the `GL_1` example
  `‖z‖_H = |z|² + |z|⁻²`, and `W(z) = |z|² ≤ ‖z‖_H` (`N = 1`).
  Clauses 4 and 5: `A_i` carries right translation and right derivatives to the compact and Lie
  actions at `w`, the Whittaker coefficient (an integral over the compact `N(F)\N(𝔸)`) commutes
  with right translation and with differentiation, and `ι_w(k)` commutes with the finite adelic
  point `b`.
* For `ψ⁻¹` the component at `w` is `ψ_(-a)`, and the same argument gives the second claim.

### Minus-one

`ComplexPlaceMinusOneStatement`: if `T` has the parameter `d` at `w`, then
`complexMinusOneScalar T w = complexCentralSign d`.

Why it is expected to hold. `T` is irreducible, so `-1 ∈ U(r+1)` at `w` acts by a scalar (the
value at `-1` of the central character at `w`); `complexMinusOneScalar` is then that scalar. On
the standard module, right translation by `-1` is multiplication by `∏_j χ_j(-1)` (see
`complexCentralSign`). The map `A` of `HasComplexPlaceParameter` is injective, carries right
translation by `-1` to the compact action of `-1`, and its domain is nonzero. So the two scalars
agree.

### Contragredient parameter

`ComplexPlaceContragredientParameterStatement`: if `Td` is contragredient to `T`
(`IsContragredientOf`), and `d`, `dd` are parameters of `T`, `Td` at `w`, then `dd` is a
permutation of `d.map inv`.

Why it is expected to hold. As in the bridge, the standard modules of `d` and `dd` are
irreducible and isomorphic to `π_w` and to the component of `Td` at `w`, which is the
contragredient `π̃_w`. The contragredient of the principal series of `(χ_j)` is the principal
series of `(χ_j⁻¹)` (Jacquet p.5 for the semisimplifications; here everything is irreducible).
Irreducible principal series of `GL_n(ℂ)` are isomorphic exactly when their characters agree up
to a permutation (Zhelobenko's classification; the pair `(λ_L, λ_R)` of a list of characters
`z^(λ_L) z̄^(λ_R)` is determined up to simultaneous Weyl-group conjugation). Hence `dd` is a
permutation of `d.map inv`.

## The proof

`complexUnequalFunctionalEquationReduction`: given the premises `hloc`, `hmodel`, `hsign`,
`hdual` and all data of `ComplexUnequalFunctionalEquationStatement`:

1. `hmodel` turns `hW : IsComplexPlaceWhittaker F T ψ.complex w W` into
   `W ∈ complexWhittakerModel r d a` (using the parameter `d` of `T`), and
   `hW' : IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W'` into
   `W' ∈ complexWhittakerModel t d' (-a)`.
2. `hloc` applied to these and to the lengths `hd.1`, `hd'.1` gives `σ`, `M`, `Md` and nine
   clauses. The first eight are the first eight clauses of the target verbatim.
3. `hdual` gives `dd ~ d.map inv` and `dd' ~ d'.map inv`. The Library lemma
   `complexPairLFactor_perm` gives
   `complexPairLFactor dd dd' = complexPairLFactor (d.map inv) (d'.map inv)`.
4. `hsign` for `T'` gives `complexMinusOneScalar T' w = complexCentralSign d'`.
5. Rewriting the target's last clause with 3 and 4 turns it into the last clause of `hloc`.

`complexEqualFunctionalEquationReduction` is the same proof with the equal-rank premise and the
Schwartz function `Φ`. `complexPlaceFunctionalEquationReduction` pairs the two.

## Provenance

Our own reduction. The target is Jacquet 2009, Theorem 2.1 (i)–(iii), for global data; the
reduction separates its local content (the local premises, Jacquet's theorem for induced
representations) from the global-to-local identification (bridge, minus-one, contragredient),
which the target's Markdown describes in prose (section "Why the functions are in Jacquet's
Whittaker models"). The local objects `complexMatrixHeight`, `complexWhittakerCharacter` and
the `ψ`-equivariance of `IsComplexWhittakerIntertwiner` follow Jacquet (2.1), (2.2) on p.3;
`complexWhittakerModel` is a `K`-finite substitute for Jacquet's `W(π_(σ,u) : ψ)` (p.4),
defined without the Casselman–Wallach completion, which the Library lacks.

## Sources

* H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
  `jacquet-2009-archimedean-rankin-selberg` (PDF page = printed page): p.3 ((2.1) height,
  moderate growth, Casselman–Wallach completion, (2.2) `θ_ψ`, `ψ`-forms), p.4 (`π_(σ,u)`,
  uniqueness of the `ψ`-form, `W(π_(σ,u) : ψ)`), p.5 (`W̃`, contragredients, `γ`), p.6
  (integrals (2.4)–(2.6), Theorem 2.1).
* N. Wallach, *Real reductive groups II* (1992), ch. 11 and Theorem 15.4.1, as cited by
  Jacquet p.3–4 (not in the project's literature; used only in the truth argument for the
  local premises).

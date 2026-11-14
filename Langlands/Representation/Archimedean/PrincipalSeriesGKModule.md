# The `(𝔤, K)`-module of `K`-finite principal-series functions

Module: `Langlands.Representation.Archimedean.PrincipalSeriesGKModule`.

## Purpose and provenance

This module is internal infrastructure for proving
`Langlands.Archimedean.ComplexLanglandsQuotientStatement` and its real analogue
`Langlands.Archimedean.RealLanglandsQuotientStatement`. The proof of the complex statement needs
the `U(n)`-finite functions of the standard module `complexStandardModule n ds` as a
`(𝔤𝔩_n(ℂ), U(n))`-module, the Harish-Chandra module of the classical principal series, in the
exact sense of the Library predicate `IsComplexGKModule`. This module constructs that structure:
`U(n)` acts by right translation and `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)` acts by right derivatives. It proves the four
clauses of `IsComplexGKModule`, and also the four clauses of `IsRealGKModule` in the real case.
Finally it proves that the identity map satisfies the Library predicate
`IsComplexStandardIntertwining`.

The mathematics is standard. The `K`-finite vectors of a smooth representation of a real Lie
group form a `(𝔤, K)`-module under the restricted `K`-action and the derived action of `𝔤`. This is
textbook background (for example Knapp, *Representation Theory of Semisimple Groups: An Overview
Based on Examples*, Chapter VIII). The module claims nothing beyond these facts about the Library
definitions `principalSeries`, `kFiniteFunctions`, `rightDerivative`, `Whittaker.rightTranslation`,
`IsComplexGKModule`, `IsRealGKModule` and `IsComplexStandardIntertwining`, so it cites no
literature sources. `kFiniteRep`, `kFiniteLie` and their specializations are auxiliary
definitions of this formalization.

This module imports `Langlands.Representation.Archimedean.PrincipalSeriesStability`, which
proves that the `K`-finite functions are closed under right translation by `K` and under right
derivatives. That module is the separate staged candidate `0715f927-9d27-4968-bfac-83b2ed2650ca`
and must be integrated first.

Throughout, `F` is an `RCLike` field (`ℝ` or `ℂ`), `N` is a natural number, `GL_N(F)` is
`Langlands.GeneralLinear N F` with the manifold structure `matrixModel F N`, and smooth means
`ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞`. `K = unitaryCompact F N` is `U(N)` for `F = ℂ` and
`O(N)` for `F = ℝ`, as a subgroup of `GL_N(F)`. The Library's `(𝔤, K)`-module predicates let
the matrix unitary group `Matrix.unitaryGroup (Fin N) F` act. The two groups are identified
through `Unitary.toUnits`. `R(k)` is right translation, `(R(k) f)(g) = f(g k)`, and
`R(X) = rightDerivative (matrixModel F N) X`.

## Proof route

The Lie bracket. In matrix coordinates (`unitsExtension f`, the extension of `f` by zero to all
matrices, from `PrincipalSeriesStability`) the right derivative is
`(R(X) f)(g) = Df̃(g)(g X)`. Differentiating once more gives
`R(X) R(Y) f (g) = D²f̃(g)(g X, g Y) + Df̃(g)(g X Y)` (`rightDerivative_rightDerivative`). The
second derivative of a smooth function is symmetric (Mathlib's
`ContDiffAt.isSymmSndFDerivAt`), so `R(X) R(Y) − R(Y) R(X) = R(XY − YX)`
(`rightDerivative_commutator`). `X ↦ R(X)` is real linear, and its complex-linear extension
`z ⊗ X ↦ z R(X)` to `ℂ ⊗_ℝ 𝔤𝔩_N(F)` is therefore a Lie algebra homomorphism into the
endomorphisms of the `K`-finite functions. On `ℂ ⊗_ℝ 𝔤𝔩_N(F)` the bracket is
`[z ⊗ X, w ⊗ Y] = z w ⊗ (XY − YX)`.

`K`-finiteness. A `K`-finite function `f` has a finite-dimensional span of right translates
`R(k) f`, `k ∈ K`. The orbit span of `f` under `kFiniteRep` maps injectively into that span, so
it is finite-dimensional.

Continuity and the derivative clause. Point evaluations separate the vectors of a
finite-dimensional space `S` of functions. Hence every linear functional `ℓ` agrees on `S` with
a finite combination `∑ cᵢ ev_{pᵢ}` of point evaluations (`exists_sum_of_separating`, by
duality in finite dimensions). Take `S` to be the orbit span of `f`, together with `R(X) f` for
the derivative clause. Then `ℓ(R(k) f) = ∑ cᵢ f(pᵢ k)`, which is continuous in `k`. Along a
curve `γ` in `K` through `1` with entrywise derivative `X`, the derivative of `f(p γ(t))` at
`t = 0` is `Df̃(p)(p X) = (R(X) f)(p)` by the chain rule.

The adjoint clause. `R(k) R(X) f = R(k X k⁻¹) R(k) f` is `rightTranslation_rightDerivative` from
`PrincipalSeriesStability`. For a unitary `k`, `k⁻¹ = k*`.

## Declarations

All declarations are in the namespace `Langlands.Archimedean`.

### Functionals and the Lie bracket of right derivatives

- `exists_sum_of_separating e S he ℓ`: for linear functionals `e g : V →ₗ[ℂ] ℂ` indexed by
  `g : G`, a finite-dimensional subspace `S`, and the hypothesis that a vector `s ∈ S` with
  `e g s = 0` for all `g` is `0`: every linear functional `ℓ` has `m`, points `p : Fin m → G`
  and coefficients `c : Fin m → ℂ` with `ℓ s = ∑ i, c i * e (p i) s` for every `s ∈ S`.
- `rightDerivative_add_left`, `rightDerivative_smul_left`: `R(X + Y) f = R(X) f + R(Y) f` and
  `R(r • X) f = r • R(X) f` for real `r`, for every function `f`.
- `contDiffAt_unitsExtension`: for smooth `f`, `unitsExtension f` is `ContDiffAt ℝ ∞` at every
  invertible matrix.
- `rightDerivative_rightDerivative hf X Y g`: for smooth `f`,
  `R(X) (R(Y) f) g = D²f̃(g)(g X)(g Y) + Df̃(g)(g X Y)`, where `f̃ = unitsExtension f` and `D` is
  `fderiv ℝ`.
- `rightDerivative_commutator hf X Y`: for smooth `f`,
  `R(X) (R(Y) f) − R(Y) (R(X) f) = R(X * Y − Y * X) f`.

### The generic construction

The section `Generic` fixes a complex subspace `V` of functions `GL_N(F) → ℂ` with three
hypotheses: `hV`, every element of `V` is smooth; `hVK`, `V` is stable under right translation
by every `k ∈ unitaryCompact F N`; `hVX`, `V` is stable under every right derivative
`R(X)`, `X ∈ M_N(F)`. Its declarations take `V`, `hV`, `hVK`, `hVX` as explicit arguments when
used.

- `kFiniteSubrepresentation V hVK` (definition): `kFiniteFunctions V (unitaryCompact F N)` as a
  subrepresentation of `Matrix.unitaryGroup (Fin N) F` acting on functions by
  `k ↦ R(Unitary.toUnits k)`.
- `kFiniteRep V hVK` (definition): the resulting representation of
  `Matrix.unitaryGroup (Fin N) F` on `kFiniteFunctions V (unitaryCompact F N)`.
  `kFiniteRep_apply_coe` states that `kFiniteRep V hVK k f` is the function
  `R(Unitary.toUnits k) f`.
- `kFiniteFunctions_mem_smooth`: every element of `kFiniteFunctions V (unitaryCompact F N)` is
  smooth.
- `kFiniteDerivative V hV hVK hVX X` (definition): the complex-linear endomorphism `f ↦ R(X) f`
  of `kFiniteFunctions V (unitaryCompact F N)`. `kFiniteDerivative_apply_coe` states its value.
- `kFiniteRealDerivative` (definition): `X ↦ kFiniteDerivative … X` as a real-linear map from
  `M_N(F)` to the complex endomorphisms.
- `kFiniteLinear` (definition): its complex-linear extension
  `ℂ ⊗[ℝ] M_N(F) →ₗ[ℂ] Module.End ℂ (kFiniteFunctions V (unitaryCompact F N))`,
  `z ⊗ X ↦ z • R(X)` (`kFiniteLinear_tmul`).
- `kFiniteDerivative_commutator`: `R(X) R(Y) − R(Y) R(X) = R(X * Y − Y * X)` as endomorphisms.
- `kFiniteLie V hV hVK hVX` (definition): `kFiniteLinear` as a complex Lie algebra
  homomorphism `(ℂ ⊗[ℝ] Matrix (Fin N) (Fin N) F) →ₗ⁅ℂ⁆ Module.End ℂ (kFiniteFunctions V
  (unitaryCompact F N))`. The source bracket is the base change of the commutator bracket of
  matrices, the target bracket is the commutator of endomorphisms. `kFiniteLie_tmul`:
  `kFiniteLie … (z ⊗ X) = z • kFiniteDerivative … X`. `kFiniteLie_one_tmul_apply_coe`:
  `kFiniteLie … (1 ⊗ X) f` is the function `R(X) f`.
- `kFiniteEval V g` (definition) is evaluation at `g` as a linear functional, with
  `kFiniteEval_apply`. `eq_zero_of_kFiniteEval`: a `K`-finite function whose evaluations all
  vanish is `0`.

The four clauses of `IsComplexGKModule` / `IsRealGKModule`:

- `kFiniteRep_isFiniteVector V hVK f`: every `f` is a finite vector of `kFiniteRep V hVK`
  (`FiniteVectors.IsFiniteVector`).
- `kFiniteRep_continuous V hV hVK f ℓ`: `k ↦ ℓ (kFiniteRep V hVK k f)` is continuous on
  `Matrix.unitaryGroup (Fin N) F`, for every complex-linear functional `ℓ`. It uses
  `continuous_unitary_toUnits`, continuity of `Unitary.toUnits` into `GL_N(F)`.
- `kFiniteRep_hasDerivAt V hV hVK hVX h0 hγ f ℓ`: for a curve
  `γ : ℝ → Matrix.unitaryGroup (Fin N) F` with `γ 0 = 1` whose entries `t ↦ γ t i j` have
  derivative `X i j` at `0`, the function `t ↦ ℓ (kFiniteRep V hVK (γ t) f)` has derivative
  `ℓ (kFiniteLie V hV hVK hVX (1 ⊗ₜ X) f)` at `0`. Auxiliary results:
  `hasDerivAt_matrix_of_entries` (a matrix curve with entrywise derivatives `X i j` has
  derivative `X`, for the operator norm on matrices) and `hasDerivAt_mul_unitary_curve` (for
  smooth `f`, `t ↦ f (p * Unitary.toUnits (γ t))` has derivative `(R(X) f)(p)` at `0`).
- `kFiniteRep_kFiniteLie V hV hVK hVX k X f`:
  `kFiniteRep V hVK k (kFiniteLie … (1 ⊗ₜ X) f) = kFiniteLie … (1 ⊗ₜ (k * X * star k))
  (kFiniteRep V hVK k f)`.

### `(𝔤, K)`-modules

- `isComplexGKModule_kFinite V hV hVK hVX` (`F = ℂ`, `N = n`):
  `IsComplexGKModule n (kFiniteRep V hVK) (kFiniteLie V hV hVK hVX)`.
- `isRealGKModule_kFinite V hV hVK hVX` (`F = ℝ`, `N = n`):
  `IsRealGKModule n (kFiniteRep V hVK) (kFiniteLie V hV hVK hVX)`.

### The principal series

For `χ : ℕ → Fˣ → ℂ`, `V = principalSeries F N χ` satisfies the three hypotheses: its elements
are smooth by definition, and it is stable under right translation and right derivatives by
`rightTranslation_mem_principalSeries` and `rightDerivative_mem_principalSeries`.

- `principalSeriesRep F N χ` (definition): `kFiniteRep` for `V = principalSeries F N χ`, a
  representation of `Matrix.unitaryGroup (Fin N) F` on
  `kFiniteFunctions (principalSeries F N χ) (unitaryCompact F N)`.
  `principalSeriesRep_apply_coe`: `principalSeriesRep F N χ k f` is `R(Unitary.toUnits k) f`.
- `principalSeriesLie F N χ` (definition): `kFiniteLie` for `V = principalSeries F N χ`.
  `principalSeriesLie_one_tmul_apply_coe`: `principalSeriesLie F N χ (1 ⊗ₜ X) f` is `R(X) f`.
- `isRealGKModule_principalSeries n χ`:
  `IsRealGKModule n (principalSeriesRep ℝ n χ) (principalSeriesLie ℝ n χ)`.
- `isComplexGKModule_principalSeries n χ`:
  `IsComplexGKModule n (principalSeriesRep ℂ n χ) (principalSeriesLie ℂ n χ)`.

### The complex standard modules

`complexStandardModule n ds` is by definition
`principalSeries ℂ n (complexPositionCharacter ds)`.

- `complexStandardRep n ds` (abbreviation): `principalSeriesRep ℂ n (complexPositionCharacter
  ds)`, a representation of `Matrix.unitaryGroup (Fin n) ℂ` on
  `kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)`.
- `complexStandardLie n ds` (abbreviation): `principalSeriesLie ℂ n (complexPositionCharacter
  ds)`, a Lie algebra homomorphism from `ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ` to the endomorphisms
  of the same space.
- `isComplexGKModule_complexStandardModule n ds`:
  `IsComplexGKModule n (complexStandardRep n ds) (complexStandardLie n ds)`. The
  `U(n)`-finite functions of the standard module form the Harish-Chandra module of the
  classical principal series.
- `isComplexStandardIntertwining_id n ds`:
  `IsComplexStandardIntertwining n (complexStandardRep n ds) (complexStandardLie n ds) ds
  LinearMap.id`. The identity of `kFiniteFunctions (complexStandardModule n ds) (unitaryCompact
  ℂ n)` intertwines right translation by `k ∈ unitaryCompact ℂ n` with
  `complexStandardRep n ds` at the matrix of `k`, and the right derivative `R(X)` with
  `complexStandardLie n ds (1 ⊗ₜ X)`.

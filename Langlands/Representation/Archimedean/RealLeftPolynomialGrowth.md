# Growth on functions that are polynomial along a lower root group

Lean module: `Langlands.Representation.Archimedean.RealLeftPolynomialGrowth`
(namespace `Langlands.Archimedean`).

This module makes two definitions and proves elementary facts about them. It then defines one
statement, `RealLeftPolynomialGrowthStatement`. The statement is not proved here.

Notation:

- `𝔤 = ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ` and `U = U(𝔤)`.
- `I(ds) = kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`, the
  `O(n)`-finite functions of the real standard module of `ds`.
- `φ = envelopingAction (realStandardLie n ds)`, the action of `U` on `I(ds)`.
- `U_d = degreeFiltration ℂ 𝔤 d`, the elements of degree at most `d`.

## Definitions

- `lowerRootMatrix n p hp`, for `hp : p + 1 < n`, is the matrix unit `E_{p+1,p}` of
  `𝔤𝔩_n(ℝ)`. It is `Matrix.single ⟨p + 1, hp⟩ ⟨p, _⟩ 1`: entry `1` in row `p + 1` and column `p`
  (rows and columns counted from `0`), all other entries `0`. It is a root vector for the
  negative of the simple root at positions `p, p + 1` of the upper triangular Borel subalgebra.
- `lowerRootElement n p hp t` is the element `e(t) = 1 + t E_{p+1,p}` of `GL_n(ℝ)`
  (`Langlands.GeneralLinear n ℝ`), with inverse `1 - t E_{p+1,p}`. The inverse identities hold
  because `E_{p+1,p}² = 0`.

## Proved facts

- `lowerRootMatrix_mul_self`: `E_{p+1,p} * E_{p+1,p} = 0`, from
  `Matrix.single_mul_single_of_ne` since `p ≠ p + 1`.
- `smul_lowerRootMatrix_mul_self`: `(s E) * (t E) = 0`.
- `lowerRootElement_val`: the underlying matrix of `e(t)` is `1 + t • E_{p+1,p}`; this holds
  by `rfl`.
- `lowerRootElement_add`: `e(s) e(t) = e(s + t)`. Expand `(1 + sE)(1 + tE)` (private ring
  identity `one_add_mul_one_add`) and use `(sE)(tE) = 0`. So `t ↦ e(t)` is a one-parameter
  subgroup. Since `E² = 0` it equals `t ↦ exp(t E)`, but the module does not use this.

The private lemmas `one_add_mul_one_sub`, `one_sub_mul_one_add` and `one_add_mul_one_add` are the
identities `(1 + x)(1 - x) = 1 - x x`, `(1 - x)(1 + x) = 1 - x x` and
`(1 + x)(1 + y) = 1 + (x + y) + x y` in any ring, proved by `noncomm_ring`.

## The statement

```lean
def RealLeftPolynomialGrowthStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock) (p k : ℕ) (hp : p + 1 < n)
    (Y : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))),
    (∀ h ∈ Y, ∀ g : Langlands.GeneralLinear n ℝ, ∃ q : Polynomial ℂ, q.degree < k ∧
      ∀ t : ℝ, (h : Langlands.GeneralLinear n ℝ → ℂ) (lowerRootElement n p hp t * g) =
        q.eval (t : ℂ)) →
    ∃ C : ℝ, ∀ d : ℕ,
      (Module.finrank ℂ ((degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) d).map
        (LinearMap.lcomp ℂ _ Y.subtype ∘ₗ
          (envelopingAction (realStandardLie n ds)).toLinearMap)) : ℝ) ≤
        C * ((d : ℝ) + 1) ^ (n * (n - 1) - 1)
```

In words: let `ds` be any list of real blocks, `p + 1 < n` and `k : ℕ`. Let `Y` be a subspace of
`I(ds)` such that for each `h ∈ Y` and each `g ∈ GL_n(ℝ)` the function `t ↦ h(e(t) g)` on `ℝ` is
given by a complex polynomial `q` of degree `< k`. Then there is a constant `C`, independent of
`d`, such that for every `d`

`dim { u|_Y : u ∈ U_d } ≤ C (d + 1)^(n (n - 1) - 1)`.

Here `u|_Y = φ(u) ∘ Y.subtype : Y → I(ds)` is the restriction of the operator of `u` to `Y`.
`LinearMap.lcomp ℂ _ Y.subtype` sends `T` to `T ∘ Y.subtype`. The dimension is that of the
image of `U_d` under the linear map `u ↦ u|_Y` into `Hom(Y, I(ds))`.

The statement makes no assumption on `ds`: no rank or ordering condition, and `realRank ds`
need not equal `n`. Nothing requires `Y` to be a `(𝔤, K)`-submodule. If `k = 0`, then `Y = 0`
(a polynomial of degree `< 0` is zero), and the statement holds with `C = 0`.

## Provenance

This is an internal statement. It is one of three statements whose
combination, proved in module `RealLinkedJacquetFunctional`
(`realLinkedQuotientGrowth_of_split`), gives `RealLinkedQuotientGrowthStatement`. The
exponent is one less than the exponent `n (n - 1) = 2 dim 𝔫` of `U / Ann I(ds)`. That exponent
appears in `RealStandardAnnihilatorGrowthStatement` (module `RealStandardAnnihilatorGrowth`).

The statement is a counting argument in the noncompact picture. No single published reference
states it. The facts used are standard: the noncompact picture of an induced representation and
the action of `𝔤` on it by first-order differential operators with polynomial coefficients
(Knapp, *Representation Theory of Semisimple Groups*, 1986, Chapter VII). Vogan uses the same
kind of count to prove that the Gelfand–Kirillov dimension of an induced module is that of the
inducing module plus `dim N` (Vogan 1978, Invent. Math. 48, Lemma 6.5, printed p. 94).

## Suggested proof route

This route is not part of this module and is recorded only as guidance.

1. Let `N̄` be the lower unipotent subgroup, of dimension `m = n (n - 1) / 2`. The functions of
   the standard module are left equivariant under the upper triangular Borel subgroup `B`.
   `B N̄` is open and dense in `GL_n(ℝ)`, so each function is determined by its restriction to
   `N̄`.
2. `N̄ = e(ℝ) ⋉ N̄'`, where `N̄'` is the normal subgroup of lower unitriangular matrices with
   entry `(p + 1, p)` equal to `0`. The map `(y, n̄') ↦ e(y) n̄'` is a polynomial isomorphism with
   polynomial inverse. In these coordinates, the restriction of `h ∈ Y` is polynomial in `y` of
   degree `< k`.
3. On restrictions to `N̄`, `X ∈ 𝔤` acts by a first-order differential operator. Its coefficients
   are polynomial, of bounded degree. So `u ∈ U_d` acts by `Σ_{|α| ≤ d} c_α ∂^α` with
   polynomials `c_α` of degree at most `c d`, where `c` depends only on `n`.
4. On `Y`, every term with `∂_y^j` for `j ≥ k` vanishes. Hence `u|_Y` lies in the span of the
   operators `x^β ∂^α` with `|β| ≤ c d`, `|α| ≤ d` and `α_y < k`. There are
   `O(d^m · k d^(m - 1)) = O(d^(2m - 1))` of these, and `2m - 1 = n (n - 1) - 1`.

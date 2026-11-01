# Tail-product coordinates on the diagonal torus

Module `Langlands.Representation.GodementJacquet.WhittakerTorusCoordinates`,
namespace `Langlands.GodementJacquet.WhittakerTorus`.

For an `(n + 1)`-tuple `x` in a commutative monoid, the tail products are

`τ(x)_j = ∏_{k ≥ j} x_k`,  `j = 0, …, n`.

For `a = τ(x)`, the adjacent ratios `a_j / a_(j+1)` (`j < n`) are the
coordinates `x_j`, and the last coordinate `a_n` is `x_n`. The determinant
`∏_j a_j` is `∏_k x_k^(k+1)`. The module proves these identities, makes `τ` a
topological group automorphism of `G^(n+1)` for a commutative topological
group `G`, and proves
that on the units of a nonarchimedean local field `τ` preserves the product
of the normalized multiplicative Haar measures. It also proves a
Schwartz–Bruhat lemma for functions of the form `φ(x_0, …, x_(n-1)) · Ψ(τ(x))`
and closure properties of finite functions.

## Source and provenance

The content is internal and derived. It serves the reduction of
`ModelWhittakerRationalityStatement` (convergence and rationality of every
full-matrix Whittaker integral on the coefficient model) to
`FiniteFunctionMellinStatement`. In the Iwasawa decomposition, a full-matrix
Whittaker integral becomes an integral over the diagonal torus of
`J(a) · W(a k) · |det a|^s · δ(a)^(-1)`, where `J` is a Schwartz–Bruhat
function of the diagonal entries and the torus expansion of `W(a k)` is a
finite sum of finite functions of `a` times test functions of the adjacent
ratios `a_j / a_(j+1)`. In the coordinates `x = τ⁻¹(a)` the ratios become the
coordinates `x_0, …, x_(n-1)`, so the product of the two test functions has
the shape of `initTail_mem`, and the determinant weight becomes
`∏_k |x_k|^((k+1) s)`. That is the form of the integrals in
`FiniteFunctionMellinStatement`, with weights `m k = k + 1`.

The coordinates themselves are standard. Jacquet, Piatetski-Shapiro and
Shalika, *Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983), printed
page 391, equation (4), write `a = diag(a_1 a_2 ⋯ a_r, a_2 ⋯ a_r, …, a_r)`,
which is `a = τ(x)` with the indices shifted by one, and printed page 392 uses
them to obtain the weight `|a_1 a_2^2 ⋯ a_r^r|^s` and the Mellin integrals
(5)–(6). The same authors, *Automorphic forms on GL(3) I*, Ann. of Math. 109
(1979), printed page 183, equation (2.3.2), use them to define gauges. The
contribution of this module is the implementation: the general algebraic and
topological API of `τ`, the normalized-Haar argument for
`measurePreserving_tailProd`, the finite-function closure lemmas, and the
Schwartz–Bruhat lemma `initTail_mem`. The last one concerns the case of a test
function `J` of all diagonal entries, as for the full-matrix integrals; in the
1983 proof on printed pages 391–392 the Schwartz–Bruhat factor is `Φ(a_r)`, a
function of the last coordinate only. The lemma explains why the coordinates
matter in that case: in the ordinary diagonal coordinates, the product of `J`
and a test function of the ratios need not be Schwartz–Bruhat. For `n + 1 = 2`, `J = 1{|a_0| ≤ 1, |a_1| ≤ 1}`
and the ratio cut-off `1{|a_0 / a_1| ≤ 1}`, the product is the indicator
function of `|a_0| ≤ |a_1| ≤ 1`, which is not locally constant at the origin.
In the coordinates `a = τ(x) = (x_0 x_1, x_1)` the same product is
`1{|x_0| ≤ 1} · J(τ(x))`, which `initTail_mem` covers.

## Declarations

### Algebra (commutative monoids and groups)

- `tailProd x j`: the product of `x k` over `k ≥ j` (a `Finset.filter` over
  `Fin (n + 1)`).
- `tailProd_last`: `τ(x)_n = x_n`.
- `tailProd_castSucc`: `τ(x)_i = x_i · τ(x)_(i+1)` for `i < n`.
- `tailProd_mul`, `tailProd_one`: `τ` is multiplicative.
- `map_tailProd`: monoid homomorphisms (and absolute values, through
  `MonoidHomClass`) commute with `τ`.
- `prod_tailProd`: `∏_j τ(x)_j = ∏_k x_k^(k+1)`. Proof: exchange the two
  products (`Finset.prod_comm'`); the index `k` occurs for the `k + 1`
  indices `j ≤ k`.
- `adjRatio a`: the tuple `(a_0/a_1, …, a_(n-1)/a_n, a_n)`, defined with
  `Fin.snoc`; simp lemmas `adjRatio_castSucc`, `adjRatio_last`.
- `adjRatio_tailProd`, `tailProd_adjRatio`: the two maps are inverse to each
  other in a commutative group. The proofs go by `Fin.lastCases` and by
  reverse induction `Fin.reverseInduction` with `tailProd_castSucc`.
- `tailProd_div_tailProd`: `τ(x)_i / τ(x)_(i+1) = x_i` for `i < n`.
- `tailProdEquiv`: `τ` as a `MulEquiv` with inverse `adjRatio`.

### Topology

- `continuous_tailProd`: `τ` is continuous (finite products of coordinate
  projections) in a topological monoid.
- `continuous_adjRatio`: `adjRatio` is continuous in a topological group.
- `tailProdHomeomorph`: `τ` as a `ContinuousMulEquiv`;
  `coe_tailProdHomeomorph` identifies its coercion with `tailProd`.

### Measure

Let `E` be a nonarchimedean local field (`IsNonarchimedeanLocalField`) with
second countable topology, and `Eˣ` carry any Borel measurable structure.

- `measurePreserving_tailProd`: `τ` preserves
  `Measure.pi (fun _ => localMultiplicativeHaar E)` on `(Eˣ)^(n+1)`.
  Proof: the image measure under the continuous group automorphism is left
  invariant and finite on compacts, so Mathlib's uniqueness theorem
  `Measure.isMulLeftInvariant_eq_smul` writes it as `c • μ` with
  `c = haarScalarFactor`. The set `U = (O^×)^(n+1)` of tuples of integral
  units has `μ U = 1` (each factor has mass `1` by the normalization of
  `localMultiplicativeHaar`), and `τ⁻¹(U) = U`: tail products of units are
  units, and conversely `x_i = τ(x)_i / τ(x)_(i+1)` and `x_n = τ(x)_n`. Hence
  `c = 1`.
- `coe_tailProd_units`: the value in `E` of a tail product of units is the
  tail product of the values.

### Weights

- `ofReal_prod_cpow`: `(∏ f i)^s = ∏ (f i)^s` for nonnegative real `f i` and
  complex `s` (induction on the finset with `Complex.mul_cpow_ofReal_nonneg`).
- `cpow_abv_prod_tailProd`: for an absolute value `abv` on a field `E`, a
  tuple `x` and `s ∈ ℂ`,
  `abv(∏_j τ(x)_j)^s = ∏_k abv(x_k)^((k+1) s)`.
  Proof: split both sides with `ofReal_prod_cpow`, apply `prod_tailProd` to
  the tuple `abv(x_k)^s`, and use `Complex.cpow_nat_mul`.

### Schwartz–Bruhat functions

- `initTail_mem`: let `E` be a topological field (topological ring
  structure suffices). For Schwartz–Bruhat functions `φ` on `E^n` and `Ψ` on
  `E^(n+1)`, the function `x ↦ φ(x_0, …, x_(n-1)) · Ψ(τ(x))` lies in
  `schwartzBruhatSubmodule (Fin (n + 1) → E)`. Here `τ` is the tail product
  in the multiplicative monoid of `E`, so zero entries are allowed. Proof:
  the function is locally constant as a product of compositions of locally
  constant functions with continuous maps. Its support lies in the compact
  box whose last factor is the projection of `tsupport Ψ` to the last
  coordinate (because `τ(x)_n = x_n`) and whose other factors are the
  coordinate projections of `tsupport φ`.

### Finite functions

`IsFiniteFunction η` (for `η : A → ℂ` on a topological monoid `A`) means that
`η` is continuous and the complex span of its left translates
`a ↦ η(b a)` is finite-dimensional. This is the predicate used verbatim in
`FiniteFunctionMellinStatement` and `CoefficientTorusExpansion`; the module
names it only to state closure lemmas.

- `IsFiniteFunction.of_mul_apply`: a continuous `η` with
  `η(b a) = c(b) η(a)` (for example a quasi-character) is finite; the span of
  its translates lies in the line through `η`.
- `IsFiniteFunction.comp`: pull-back along a continuous monoid homomorphism
  `f : A →* B` preserves finiteness. The span of the translates of `η ∘ f` lies
  in the image of the span for `η` under the linear map `LinearMap.funLeft`.
- `IsFiniteFunction.mul`: products of finite functions are finite. The span
  of the translates of `η₁ η₂` lies in the product `S₁ * S₂` of the two spans
  in the algebra of functions, which is finitely generated
  (`Submodule.FG.mul`).

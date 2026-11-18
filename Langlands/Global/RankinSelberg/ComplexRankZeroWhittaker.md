# The Whittaker model of a character of `GL₁(ℂ)`

Helper module for the rank-one (`r = 0`) case of the complex equal-rank local functional
equation, which is the premise `LocalE` in the Library's reductions of
`Langlands.Global.RankinSelbergGlobal.ComplexPlaceFunctionalEquationStatement`. Authored by
Worker 822. Every declaration is proved. There are no hypotheses beyond those stated and no
new axioms.

All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.ComplexRankZero`. The module imports the Library
modules `ComplexPlaceFunctionalEquationReduction`, which defines
`IsComplexWhittakerIntertwiner` and `complexWhittakerModel`, and
`ComplexTemperedComplement`, which supplies the product rule for right derivatives. It
also imports Mathlib's `Mathlib.Analysis.Normed.Module.Connected`.

The size of the matrices is written `0 + 1`, as in the Library's `r + 1` at `r = 0`. The
module declares a local instance `Unique (Fin (0 + 1))` and sets
`backward.isDefEq.respectTransparency false`, which the Library's smooth structure on
`GeneralLinear (0 + 1) ℂ` needs here.

## Main result

`exists_eq_of_mem_complexWhittakerModel`: let `c : ComplexCharacterData` and `a ∈ ℂˣ`. If
`W : GL₁(ℂ) → ℂ` lies in `complexWhittakerModel 0 [c] a` then there is `C ∈ ℂ` with

  `W g = C · χ_c(det g)` for every `g ∈ GL₁(ℂ)`.

Here `χ_c = c.character` is the character `z ↦ (z/|z|)^m |z|^(2t)` of `ℂˣ` and `det` is the
Library's `GeneralLinear.determinant`. The model `complexWhittakerModel 0 [c] a` is the span
of the ranges of all Whittaker intertwiners `B` of the `U(1)`-finite standard module of the
one-element list `[c]`. For `GL₁` the unipotent group is trivial, so the Whittaker character
plays no role. The proof uses only two of the intertwiner conditions: `B f` is smooth, and
`B` commutes with the right derivatives `R(X)`.

This is the statement "the Whittaker model of a character of `GL₁` is spanned by the
character itself". Jacquet (2009) treats it as evident and does not state it separately.

## Declarations

### The character `χ_d ∘ det` (section `Character`, for `d : ComplexCharacterData`)

- `characterFunction d : GL₁(ℂ) → ℂ` is `g ↦ χ_d(det g)`.
- `characterFunction_mul`, `characterFunction_one`: it is multiplicative and takes the value
  `1` at `1`.
- `characterFunction_mul_inv`: `χ_d(det g) · χ_{d⁻¹}(det g) = 1`, where `d.inv` is the
  Library's inverse character data.
- `diagonalUnits_determinant`: the diagonal matrix with entry `det g` is `g` itself.
- `principalSeriesCharacter_rankOne`: the Library's modulus-twisted principal-series
  character of the list `[d]` on `GL₁` is `a ↦ χ_d(a₀)`. The modulus character of the
  Borel subgroup of `GL₁` is trivial.
- `eq_mul_characterFunction`: every `f` in the standard module
  `complexStandardModule (0 + 1) [d]` satisfies `f g = f(1) · χ_d(det g)`. This is the
  left-equivariance condition of the principal series, applied to the diagonal element
  `det g` (which is `g`) and the evaluation point `1`.
- `characterFunction_mem`: `χ_d ∘ det` lies in the `U(1)`-finite module
  `Automorphic.complexStandardKFinite (0 + 1) [d]`. By the Library's
  `complexStandardNontrivial` this module has a nonzero element `f`. By the previous lemma
  `f = f(1) · χ_d ∘ det` with `f(1) ≠ 0`, so `χ_d ∘ det = f(1)⁻¹ · f`.
- `contMDiff_characterFunction`: `χ_d ∘ det` is smooth. This follows from the previous lemma.
- `rightDerivative_characterFunction`: for `X ∈ M₁(ℂ)`,
  `R(X)(χ_d ∘ det)(g) = χ_d(det g) · R(X)(χ_d ∘ det)(1)`. This is the Library lemma
  `rightDerivative_mul_left_of_eq` applied to the left translate
  `h ↦ χ_d(det(g h)) = χ_d(det g) · χ_d(det h)`.
- `rightDerivative_const`: the right derivative of a constant function is `0`.
- `rightDerivative_add_inv`: `R(X)(χ_d ∘ det)(1) + R(X)(χ_{d⁻¹} ∘ det)(1) = 0`. Apply the
  product rule (`ComplexTemperedComplement.rightDerivative_mul_fun`) to the constant
  product `(χ_d ∘ det) · (χ_{d⁻¹} ∘ det) = 1` at `1`.

### Connectedness

- `isConnected_setOf_isUnit`: the set of invertible `1 × 1` complex matrices is connected.
  It is the image of `ℂ \ {0}` under the continuous map `z ↦ (z)`. The set `ℂ \ {0}` is
  connected by Mathlib's `isConnected_compl_singleton_of_one_lt_rank`, since `ℂ` has real
  dimension `2`.

### Whittaker intertwiners (section `Intertwiner`)

- `characterVector c` is `χ_c ∘ det` as an element of the `U(1)`-finite standard module of
  `[c]`.
- `eq_of_rightDerivative`: let `F : GL₁(ℂ) → ℂ` be smooth and suppose that
  `R(X)F(g) = μ_X · F(g)` for all `X` and `g`, where `μ_X = R(X)(χ_c ∘ det)(1)`. Then
  `F g = F(1) · χ_c(det g)`. Proof: put `ψ = F · (χ_{c⁻¹} ∘ det)`. It is smooth
  (`ComplexJacquetLimit.contMDiff_mul_fun`). By the product rule and the two previous
  derivative lemmas, `R(X)ψ = 0` for every `X`. Extend `ψ` by zero to all matrices
  (`unitsExtension`). The Library lemma `rightDerivative_eq_fderiv` identifies the Fréchet
  derivative of the extension at an invertible `y` in direction `v` with `R(y⁻¹ v)ψ(y)`,
  which is `0`. The invertible matrices form an open (`isOpen_setOf_isUnit_matrix`) and
  connected set. So the extension is constant there by Mathlib's
  `IsOpen.is_const_of_fderiv_eq_zero`, and `ψ(g) = ψ(1) = F(1)`. Finally
  `F = ψ · (χ_c ∘ det)`.
- `intertwiner_characterVector`: if `B` is a Whittaker intertwiner of `[c]` for `a`
  (`IsComplexWhittakerIntertwiner 0 [c] a B`), then
  `B(χ_c ∘ det)(g) = B(χ_c ∘ det)(1) · χ_c(det g)`. The function `B(χ_c ∘ det)` is smooth
  (second intertwiner condition). By `rightDerivative_characterFunction`,
  `R(X)(χ_c ∘ det) = μ_X · (χ_c ∘ det)`. The last intertwiner condition (commuting with
  `R(X)`) and linearity of `B` give `R(X)B(χ_c ∘ det) = μ_X · B(χ_c ∘ det)`. Now apply
  `eq_of_rightDerivative`.
- `exists_eq_of_mem_complexWhittakerModel` (main result above). Every element `f` of the
  `U(1)`-finite module equals `f(1) · characterVector c`, by `eq_mul_characterFunction`.
  So by `intertwiner_characterVector` the range of every intertwiner `B` lies in the span
  of `χ_c ∘ det`. Hence the supremum `complexWhittakerModel 0 [c] a` does too, and a
  member of a one-dimensional span is a scalar multiple of its generator.

## Source

Jacquet, H., *Archimedean Rankin–Selberg integrals*, in *Automorphic Forms and
L-functions II: Local Aspects*, Contemp. Math. 489 (2009), 57–172 (literature id
`jacquet-2009-archimedean-rankin-selberg`). This module covers the rank-one Whittaker
models that Jacquet's Theorem 2.1 uses at `n = n' = 1`; the statement and proof here are
elementary and internal to this formalization.

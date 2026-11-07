# The dual unequal-rank integral under change of additive character

Lean module: `Langlands.Representation.RankinSelberg.UnequalRankDualCharacterChange`.

This module provides the matrix identities, measure scalings and model-function
identities used to move the original and the dual (transformed) unequal-rank
integrals from an additive character `ψ` to `ψ^a(x) = ψ(a x)`. It is the
matrix and integral layer of the change of additive character for the JPSS
pair factors (Cogdell and Piatetski-Shapiro 1994, Lemma 2.1 and its proof,
printed pages 161–163). The printed proof states the change of variables
without the explicit matrices. The corrections `R` and `E` below, their
identities and the bookkeeping of the central characters were worked out for
this formalization. They do not follow a printed computation.

Notation. `F` is a field, `n < r`, `π` acts on a space `V` through
`GL_(r+1)(F)` and `σ` on `W` through `GL_(n+1)(F)`. `d_a = characterChangeElement a m`
is `diag(a^m, a^(m-1), ..., a, 1)` in `GL_(m+1)(F)`, `w` the long Weyl element,
`w' = blockWeylAt n r hnr = diag(I_(n+1), w_(r-n))`, and `ι` the inverse
transpose. The functionals `ℓ_a = characterChangeFunctional ψ π a ℓ` and
`ℓ'_a = characterChangeInverseFunctional ψ σ a ℓ'` are `v ↦ ℓ(π(d_a) v)` and
`u ↦ ℓ'(σ(d_a) u)`.

## Matrices

- `blockCorrectionAt a n r`: the diagonal matrix `R` in `GL_(r+1)(F)` with
  entries `a^(r-n)` in the first `n+1` places and `a^(r-i)` at place `i ≥ n+1`,
  that is `diag(a^(r-n) I_(n+1), a^(r-n-1), ..., a, 1)`. Simp lemmas
  `blockCorrectionAt_val` and `blockCorrectionAt_inv_val` give its matrix and
  the matrix of its inverse.
- `blockCorrectionAt_add`: at `r = n + d` it equals the Library's
  `characterChangeBlockCorrection a n d`.
- `inverseTranspose_of_diagonal`: if `g⁻¹` is a diagonal matrix, then
  `ι(g) = g⁻¹`. Consequences: `inverseTranspose_characterChangeElement`
  (`ι(d_a) = d_a⁻¹`), `inverseTranspose_blockCorrectionAt_inv` (`ι(R⁻¹) = R`)
  and `inverseTranspose_scalar'` (`ι(c I) = c⁻¹ I`).
- `weylLong_conj_characterChangeElement_inv`: `w d_a⁻¹ w = (a^m I)⁻¹ d_a` in
  `GL_(m+1)(F)`, proved entrywise. `weylLong_mul_characterChangeElement_inv` is
  the same identity in the form `w d_a⁻¹ = (a^m I)⁻¹ d_a w`.
- `scalar_mul_comm'`: scalar matrices commute with every matrix.
- `appendScalar_val`: the embedded block matrix `diag(b I_(n+1), I_(r-n))`
  (built with `appendIdentity` and `GeneralLinear.reindex`) is the diagonal
  matrix with `b` in the first `n+1` places and `1` elsewhere.
- `blockWeylAt_conj_val`: if `g` is diagonal with entries `f`, then
  `w' g w'` is diagonal with entries `f ∘ tailRev n r`, the reversal of the
  last `r-n` places. Proof by the permutation form `blockWeylAt_eq`.
- `blockWeylAt_blockCorrectionAt_scalar`: with
  `E = diag(a^(-(r-n+1)) I_(n+1), I_(r-n))`,
  `w' R w' E R = a^(r-n-1) I_(r+1)`. Proof: the left side is diagonal by the
  two previous lemmas, and each diagonal entry is computed by cases on whether
  the place is below `n+1`.
- `inverseTranspose_mul_blockWeylAt`: `ι(g w') = ι(g) w'`, since `ι(w') = w'`.
- `weylLong_inverseTranspose_correction`: for every `g` in `GL_(r+1)(F)`,
  `w ι(d_a g R⁻¹ w') E R = (a^(n+1) I)⁻¹ d_a (w ι(g w'))`. Proof: expand `ι`
  of the product, use `R w' E R = w' a^(r-n-1)` (from the previous identity and
  `w' w' = 1`), move `w` past `d_a⁻¹` and collect the scalars
  `a^(-r) a^(r-n-1) = a^(-(n+1))`.

## Measures

- `measure_pi_const_smul`: for a σ-finite measure `m` and `c ≥ 0`, the product
  of `card ι` copies of `c • m` is `c^(card ι)` times the product of copies of
  `m`.
- `rectangularMeasure_eq_smul`: if `ν' = κ • ν` with `ν` σ-finite, then
  `rectangularMeasure ν' j t = κ^(j t) • rectangularMeasure ν j t`.

## Integrals

- `unequalRankIntegral_congr_smul`: if the two additive characters are equal,
  `ρ₂ = κ • ρ₁`, `W₂ = c W₁` and `W₂' = c' W₁'` pointwise, then the unequal-rank
  integrals satisfy `I(W₂, W₂', s) = κ c c' I(W₁, W₁', s)` for the measures
  `ρ₂` and `ρ₁`. `unequalRankIntegralAt_congr_smul` is the same statement for
  the rank-transported integral `unequalRankIntegralAt`.
- `characterChangeFunctionAt ψ a n r W`: the function `g ↦ W(d_a g R⁻¹)`,
  a Whittaker function for `ψ^a` (`characterChangeFunctionAt_apply`). At
  `r = n + (j + k + 1)` it is the Library's
  `unequalRankCharacterChangeFunction ψ a n j k W`
  (`characterChangeFunctionAt_add`).
- `unequalRankIntegralAt_characterChange`: suppose the quotient measure has the
  character-change law (`HasCharacterChangeMeasureLaw`), the rectangular measure
  has the rectangular law (`HasCharacterChangeRectangularMeasureLaw`), and
  `|det d_a| = q^(-e)`. Then the integral of block `(j, k)` for `ψ^a`, the
  function `characterChangeFunctionAt ψ a n r W` and the left translate of `W'`
  by `d_a` equals `unequalRankCharacterChangeScalar abv a n j k · q^(e s)`
  times the integral for `ψ` of `W` and `W'`. Here `q^(e s)` is
  `spectralPoint q s ^ (-e)`. Proof: the Library theorem
  `unequalRankIntegral_characterChange_monomial`, after `subst` of the rank
  equation.
- `dualIntegralAt_translate'`: JPSS (2.11.2) for the dual integral of block
  `(k, j)`. Suppose the quotient measure is right invariant and the rectangular
  measure scales by `determinantWeight abv (ι g) (-k)` under right
  multiplication by `ι g`. If `W₂(h) = W₁(h diag(g, I))` and `W₂'(h) = W₁'(h g)`,
  then the integral for `ψ^(-1)` of the first dual function of `W₂` translated
  by `w'` and the second dual function of `W₂'` is
  `determinantWeight abv (ι g) ((k+j+1)/2 - s - k)` times the same integral for
  `W₁` and `W₁'`. Proof: the Library law `unequalRankIntegralAt_translate`
  applied to `ι g`, together with `inverseTranspose_mul_embedding` and
  `inverseTranspose_involutive` for the two functions.

## Model functions

- `modelMap_characterChangeFunctional`: the model function of `v` for `ℓ_a` is
  `characterChangeFunctionAt ψ a n r` of the model function of `π(R) v` for `ℓ`.
- `modelMap_characterChangeInverseFunctional`: the model function of `u` for
  `ℓ'_a` is the left translate by `d_a` of the model function of `u` for `ℓ'`.
- `firstDual_modelMap_characterChangeFunctional`: let `ω_π` be a central
  character of `π` (`Classification.HasGLCentralCharacter`). The first dual
  function of the model function of `v` for `ℓ_a`, translated by `w'`, is
  `ω_π(a)^(n+1)` times `characterChangeFunctionAt (ψ.scale (-1)) a n r` of the
  translate by `w'` of the first dual function of the model function of
  `π(E) π(R) v` for `ℓ`. Proof: `weylLong_inverseTranspose_correction` and the
  central character on the scalar `(a^(n+1) I)⁻¹`.
- `secondDual_modelMap_characterChangeInverseFunctional`: let `ω_σ` be a
  central character of `σ`. The second dual function of the model function of
  `u` for `ℓ'_a` is `ω_σ(a)^n` times the left translate by `d_a` of the second
  dual function of the model function of `u` for `ℓ'`. Proof:
  `w ι(d_a h) = (a^n I)⁻¹ d_a w ι(h)` and the central character.

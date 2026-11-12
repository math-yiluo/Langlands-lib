# A Jacobian criterion for polynomial rings over a formally smooth residue field

This helper module for the proof of
`Langlands.CommutativeAlgebra.FiniteTypeIntGRingStatement` proves the
"cotangent independence implies Jacobian independence" half of the Jacobian
criterion. All declarations are in the namespace
`Langlands.CommutativeAlgebra.FiniteTypeIntGRing`. Throughout, `R₀` is a
commutative ring, `τ` a finite type with decidable equality, and
`R₀[X] = MvPolynomial τ R₀`; `pderiv v` is Mathlib's partial derivative with
respect to `X v`.

## Statements

- `algHom_sub_eq_sum_pderiv K hK φ₁ φ₂ hφ p` (first-order Taylor expansion):
  let `E` be a commutative `R₀`-algebra and `K` an ideal of `E` with
  `a b = 0` for all `a, b ∈ K`. If two `R₀`-algebra maps
  `φ₁ φ₂ : R₀[X] → E` satisfy `φ₁ (X v) - φ₂ (X v) ∈ K` for every `v`, then
  for every polynomial `p`,
  `φ₁ p - φ₂ p = ∑ v, φ₁ (∂p/∂X_v) * (φ₁ (X v) - φ₂ (X v))`.
- `linearIndependent_pderiv_of_linearIndependent_cotangent g hgm hg`
  (**Jacobian criterion**): let `L` be a local ring with maximal ideal `𝔪` and
  residue field `κ`, which is an `R₀[X]`-algebra and an `R₀`-algebra
  compatibly (`IsScalarTower R₀ R₀[X] L`), and assume that `κ` is formally
  smooth over `R₀`. Let `g : ι → R₀[X]` be a finite family of polynomials
  whose images in `L` lie in `𝔪` (hypothesis `hgm`) and have linearly
  independent classes in `𝔪/𝔪²` over `κ` (hypothesis `hg`). Then the
  gradient vectors `(v ↦ residue (∂ g j/∂X_v)) : τ → κ`, for `j ∈ ι`, are
  linearly independent over `κ`.

This is one direction of the Jacobian criterion for smoothness in the form
used for formal fibres. The module is internal to the project's proof and
does not follow a specific reference; it avoids Mathlib's Kähler-differential
interface by working with an explicit square-zero section.

## Proofs

**Taylor expansion.** Induction on `p` (`MvPolynomial.induction_on`). For
constants both sides vanish, and the formula is additive. For `p · X w`,
put `δ = φ₁ p - φ₂ p` and `ε = φ₁ (X w) - φ₂ (X w)`. By the induction
hypothesis `δ` is a combination of elements of `K`, so `δ ∈ K` and
`δ ε = 0`. The Leibniz rule for `pderiv` and `pderiv_X` reduce the right-hand
side to `φ₁ p * ε + φ₁ (X w) * δ`, while the left-hand side is
`φ₁ p φ₁ (X w) - φ₂ p φ₂ (X w)`. Their difference is `-δ ε = 0`
(`linear_combination`).

**Jacobian criterion.** Put `E = L ⧸ 𝔪²` and let `π : E → κ` be the
`R₀`-algebra map induced by the residue map. It is surjective, and its kernel
`K` is the image of `𝔪`, so products of two elements of `K` vanish and `K` is
nilpotent. Formal smoothness of `κ` over `R₀` lifts the identity of `κ`
through `π`: Mathlib's `Algebra.FormallySmooth.liftOfSurjective` gives an
`R₀`-algebra map `s : κ → E` with `π ∘ s = id`. Consider the two `R₀`-algebra
maps `R₀[X] → E`

- `φ₁ p` = the class of the image of `p` in `L`, and
- `φ₂ p = s (residue (image of p))`.

Both reduce under `π` to the residue of the image of `p`, so
`φ₁ p - φ₂ p ∈ K` for every `p`. For each `j` the image of `g j` lies in `𝔪`,
so `φ₂ (g j) = s 0 = 0`, and the Taylor expansion gives
`φ₁ (g j) = ∑ v, φ₁ (∂ g j/∂X_v) * (φ₁ (X v) - φ₂ (X v))`.

Now let `c : ι → κ` satisfy `∑ j, c j • (gradient of g j) = 0` and lift each
`c j` to `a j ∈ L`. Modulo `𝔪²`, `∑ j, a j * g j` equals
`∑ v, (∑ j, a j φ₁ (∂ g j/∂X_v)) * (φ₁ (X v) - φ₂ (X v))`. For each `v` the
inner sum lies in `K`, because its image under `π` is
`∑ j, c j * residue (∂ g j/∂X_v) = 0`. The second factor also lies in `K`, so
every summand vanishes and `∑ j, a j * g j ∈ 𝔪²`. By
`linearIndependent_toCotangent_iff` (module `JacobianQuotient`) and
hypothesis `hg`, every `a j ∈ 𝔪`, so every `c j = 0`.

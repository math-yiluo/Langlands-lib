# Laurent evaluation at nonzero points and linear Laurent lifts

Authors: Worker 233 and Worker 759. Written for task
`28187cfe-fdc3-4489-8631-36882b53e61a`. Its intended consumer is the proof task
`1f6f86ac-1105-4f57-b067-1fe692fb2683` for the published statement
`Langlands.RankinSelberg.EqualRankContinuedFormsStatement`.

This module is an internal algebraic interface for constructing the continued
equal-rank trilinear forms. It works with these published objects, all in
namespace `Langlands.RankinSelberg`:

- the Laurent coefficient ring `LaurentCoefficients = LaurentPolynomial ℂ`;
- the rational function field `RationalFunctions = RatFunc ℂ`;
- the injective ring map `laurentToRatFunc`, which sends the Laurent variable
  `T 1` to `RatFunc.X`;
- the spectral point `spectralPoint q s = (q : ℂ) ^ (-s)` of
  `RationalContinuation`.

None of these is redefined. The module imports only
`Langlands.Representation.RankinSelberg.RationalZeta` and
`Langlands.Representation.RankinSelberg.RationalContinuation`. It contains no
measure theory, representation theory, epsilon factor or analytic hypothesis.
All declarations below are in namespace `Langlands.RankinSelberg`.

## Evaluation of Laurent coefficients

`laurentEval (x : ℂˣ) : LaurentCoefficients →ₐ[ℂ] ℂ` is Mathlib's
`LaurentPolynomial.eval₂ (RingHom.id ℂ) x`, packaged as a complex algebra
homomorphism. The extra algebra field (`commutes'`) holds because an embedded
constant `algebraMap ℂ _ c = C c` evaluates to `c`.

Evaluation is total on Laurent coefficients at nonzero points, so no
hypothesis is needed. A Laurent polynomial is a finite combination of the
monomials `T m` with `m ∈ ℤ`. Because `x` is a unit, `T m ↦ x ^ m` is defined
for every integer `m`, including negative ones, and this gives a ring
homomorphism. Equivalently, a Laurent polynomial has poles only at `0`, and a
unit is never `0`. This differs from evaluating a general rational function,
which may have a pole at `x`; see the next section.

- `laurentEval_apply`: the defining formula through `eval₂` (proved by `rfl`).
- `laurentEval_T` (simp): `laurentEval x (T m) = (x : ℂ) ^ m` for every integer
  `m`; this is the integer power in `ℂ`.
- `laurentEval_C` (simp): `laurentEval x (C c) = c`.
- `laurentEval_toLaurent` (simp): for a polynomial `p`,
  `laurentEval x (Polynomial.toLaurent p) = p.eval x`, which is ordinary
  polynomial evaluation.
- `laurentEval_smul`: `laurentEval x (c • a) = c * laurentEval x a` for a
  complex scalar `c`, since `c • a = C c * a`.

## Relation with evaluation of rational functions

Mathlib's `RatFunc.eval` is total. It evaluates the reduced numerator and the
reduced denominator, then divides, so at a pole it returns a junk value. Every
statement below either assumes or proves that the relevant denominator does
not vanish.

- `laurentToRatFunc_regular (x : ℂˣ) (a)`: the denominator
  `(laurentToRatFunc a).denom` does not vanish at `x`.
- `eval_laurentToRatFunc (x : ℂˣ) (a)`: `RatFunc.eval (RingHom.id ℂ) x
  (laurentToRatFunc a) = laurentEval x a`.
- `laurentToRatFunc_regular_and_eval`: both facts together.

The two facts are proved together by Mathlib's induction principle
`LaurentPolynomial.induction_on_mul_T`. It writes every Laurent polynomial as
`p.toLaurent * T (-n)`, with `p` a polynomial and `n` a natural number. Such an
element maps to the quotient `p / X ^ n` of embedded polynomials. The public
lemma `regular_and_eval_div` treats an arbitrary quotient `N / D` with
`D.eval z ≠ 0`. The reduced denominator of `N / D` divides `D`
(`RatFunc.denom_div_dvd`), so it does not vanish at `z`. The value is computed
by evaluating the product `(N / D) * D = N` with `RatFunc.eval_mul`. That
lemma has two denominator hypotheses: the regularity just proved and the
trivial denominator of the embedded polynomial `D`. At a nonzero `x`,
`X ^ n` does not vanish, which supplies `D.eval x ≠ 0`.

## The evaluation bridge with a separate guard

`laurentEval_eq_of_laurentToRatFunc_eq` takes a unit `x`, a Laurent
polynomial `a`, a polynomial `P` and a rational function `R` (the last three
implicit). Its hypotheses are

- `ha : laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * R`;
- `hR : R.denom.eval x ≠ 0`.

It concludes `laurentEval x a = P.eval x * RatFunc.eval (RingHom.id ℂ) x R`.

The only denominator hypothesis is about the rational function `R`. Nothing is
assumed about the product `P * R`; it is regular at `x` in any case, because
it is the image of a Laurent polynomial. The guard `hR` is needed because
`R` itself may have poles. Some may be cancelled by zeros of `P`, and
evaluating `R` at such a point would give a junk value.

The proof rewrites `laurentEval x a` as `RatFunc.eval x (laurentToRatFunc a)`
using `eval_laurentToRatFunc`, then substitutes `ha`. It evaluates the actual
product with `RatFunc.eval_mul`, which needs two facts: the embedded
polynomial `P` has denominator `1`, and the guard `hR` holds for `R`. Finally
`RatFunc.eval_algebraMap` turns the evaluation of `P` into `P.eval x`. No
evaluation at a pole occurs.

## Spectral units

- `spectralUnit {q : ℕ} (hq : 0 < q) (s : ℂ) : ℂˣ` is `spectralPoint q s`
  packaged as a unit (`Units.mk0`). It is nonzero because `(q : ℂ) ≠ 0`
  (`Complex.cpow_ne_zero_iff`).
- `coe_spectralUnit` (simp): `(spectralUnit hq s : ℂ) = spectralPoint q s`.
- `spectralPoint_sub_one_sub {q : ℕ} (hq : 0 < q) (s : ℂ)`:
  `spectralPoint q (1 - s) = ((q : ℂ))⁻¹ * (spectralPoint q s)⁻¹`. Indeed
  `spectralPoint q (1 - s) = q ^ (s - 1)` and `(spectralPoint q s)⁻¹ = q ^ s`.
  The identity `q ^ (s - 1) = q ^ s / q` for nonzero `q` (`Complex.cpow_sub`)
  then gives the claim.

## Linearity of the embedding

`LaurentCoefficients` and `RationalFunctions` carry their Mathlib complex
module structures.

- `laurentToRatFunc_smul`: `laurentToRatFunc (c • a) = c • laurentToRatFunc a`.
  Both scalar actions are multiplication by an embedded constant:
  `c • a = C c * a` and `c • r = RatFunc.C c * r`. The ring map sends
  `LaurentPolynomial.C c` to `RatFunc.C c`.
- `laurentToRatFuncLinear : LaurentCoefficients →ₗ[ℂ] RationalFunctions` is
  `laurentToRatFunc` as a complex-linear map. It satisfies
  `laurentToRatFuncLinear_apply` (simp): `laurentToRatFuncLinear a =
  laurentToRatFunc a`.

## Linear Laurent lifts of trilinear families

Let `M`, `M'` and `S` be complex modules in independent universes. Each is
assumed to be an additive commutative monoid with a `Module ℂ` structure,
since no negation is needed. This includes every complex vector space. Let
`D : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions` be a trilinear family of
rational functions and `P : ℂ[X]` a polynomial. The hypothesis `h` says that
for all `f f' Φ` some Laurent polynomial `a` satisfies
`laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * D f f' Φ`.

`laurentLift P D h : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] LaurentCoefficients` sends
`(f, f', Φ)` to the Laurent polynomial chosen from `h f f' Φ` (by
`Classical.choose`, in the private `liftValue`).

- `laurentLift_spec`: `laurentToRatFunc (laurentLift P D h f f' Φ) =
  algebraMap ℂ[X] RationalFunctions P * D f f' Φ`.
- `eq_laurentLift (ha : laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions
  P * D f f' Φ)`: then `laurentLift P D h f f' Φ = a`. Here `P`, `D` and `h`
  are explicit, while `f`, `f'`, `Φ` and `a` are implicit and inferred from
  `ha`.
- `laurentLift_eq_iff`: `laurentLift P D h f f' Φ = a` if and only if
  `laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * D f f' Φ`.

The chosen value is unique because `laurentToRatFunc` is injective
(`laurentToRatFunc_injective`), so the choice does not matter. Additivity and
homogeneity in each of the three arguments are proved by this uniqueness.
Take the third argument as an example. The image of `lift(f, f', Φ₁) +
lift(f, f', Φ₂)` under the additive map `laurentToRatFunc` is
`P * D f f' Φ₁ + P * D f f' Φ₂`. By linearity of `D` this equals
`P * D f f' (Φ₁ + Φ₂)`, which is the defining property of
`lift(f, f', Φ₁ + Φ₂)`. Injectivity then identifies the two Laurent
polynomials. The scalar case uses `laurentToRatFunc_smul` and
`mul_smul_comm`. The first and second arguments are handled the same way,
pointwise in the remaining arguments (`LinearMap.ext`).

Linearity is proved by injectivity, never by evaluation. The defining property
of the lift is an exact identity in the field of rational functions, and
injectivity turns it directly into an identity of Laurent polynomials.
Evaluation is unsuitable here. The values `D f f' Φ` are rational functions
that may have poles, where the totalized `RatFunc.eval` returns junk values.
An evaluation argument would therefore need a denominator guard at every point
used, plus a separate argument that agreement at the remaining points
determines a Laurent polynomial. The private declarations `liftValue`,
`liftInner` and `liftMiddle` build the map one argument at a time, with the
supporting private lemmas `liftValue_spec`, `eq_liftValue`, `liftInner_apply`
and `liftMiddle_apply`.

## Composition of trilinear maps

Here `M`, `M'`, `S`, `N`, `N'`, `U`, `A` and `B` are complex modules in
independent universes. As above, each is an additive commutative monoid with a
`Module ℂ` structure.

- `trilinearPostcomp (φ : A →ₗ[ℂ] B) (T : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] A)` is the
  trilinear map `(f, f', Φ) ↦ φ (T f f' Φ)`. It is defined as
  `T.compr₂ (LinearMap.compRight ℂ φ)`, where `LinearMap.compRight ℂ φ`
  postcomposes linear maps `S →ₗ[ℂ] A` with `φ`.
  `trilinearPostcomp_apply` (simp, by `rfl`):
  `trilinearPostcomp φ T f f' Φ = φ (T f f' Φ)`.
- `trilinearPrecomp (T : N →ₗ[ℂ] N' →ₗ[ℂ] U →ₗ[ℂ] A) (a : M →ₗ[ℂ] N)
  (b : M' →ₗ[ℂ] N') (c : S →ₗ[ℂ] U)` is the trilinear map
  `(f, f', Φ) ↦ T (a f) (b f') (c Φ)`. It is defined as
  `(T.compl₁₂ a b).compr₂ (LinearMap.lcomp ℂ A c)`.
  `trilinearPrecomp_apply` (simp, by `rfl`):
  `trilinearPrecomp T a b c f f' Φ = T (a f) (b f') (c Φ)`.

In the intended consumer, `trilinearPostcomp (laurentEval x).toLinearMap
(laurentLift P C hC)` evaluates a lifted trilinear continuation family at a
spectral unit `x`.

## Provenance

Internal and derived. The module has no literature source beyond the
formal-variable convention `X = q^(-s)` already used in `RationalZeta`. That
convention comes from H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin--Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367--464, Theorem 2.7(ii), printed page 390 (PDF page 25), which says the
integrals "are rational functions of `q^{-s}`" (registered source
`jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`). The
declarations here are the algebraic glue
needed to evaluate Laurent polynomial multiples of continued zeta integrals
at the spectral point `q^(-s)`, which is never zero. No numbered result of
that article is formalized here.

## Dependencies and checks

The module imports `Langlands.Representation.RankinSelberg.RationalZeta` (for
`LaurentCoefficients`, `RationalFunctions`, `laurentToRatFunc`,
`laurentToRatFunc_toLaurent`, `laurentToRatFunc_T` and
`laurentToRatFunc_injective`) and
`Langlands.Representation.RankinSelberg.RationalContinuation` (for
`spectralPoint`). Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` uses
Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The module compiles there without errors or warnings. Its declarations depend
only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

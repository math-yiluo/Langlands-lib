# Normalization of a rational gamma equation

Worker 216. This module proves an algebraic normalization step for a rational
gamma equation. It has no analytic input and adds no hypotheses beyond those
displayed below. The main theorem is
`Langlands.RankinSelberg.gammaNormalization_of_incidence`. The helper lemmas
are in the namespace `Langlands.RankinSelberg.GammaNormalization`.

## Provenance

The result is an internal algebraic generalization of the normalization step
in Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg convolutions*
(1983), §2.9, printed pp.395-396. There, the gamma factor of Theorem 2.7(iii)
is divided by the two L-factors. The quotient is shown to be a unit of the
Laurent ring in `q^{-s}`, hence a monomial `ε(s)`. The statement here is not a
verbatim source statement. It separates the purely algebraic part of that
argument. The two zeta modules, the gamma function and the sign are abstract
data. The incidence hypotheses replace the analytic facts that produce them.

The shape of the theorem is that of the Library proposition
`Langlands.RankinSelberg.GammaNormalizationStatement`. The module
`GammaNormalizationProof` derives that statement from the theorem here.

## Main theorem

Let `q : ℕ` with `1 < q`, `ζ : ℂˣ`, `e : ℕ`, `G : RationalFunctions`, sets
`S T : Set RationalFunctions` and polynomials `P Pdual : ℂ[X]`. Assume:

- `IsNormalizedGenerator S P` and `IsNormalizedGenerator T Pdual`;
- every `R ∈ S` has some `Rdual ∈ T` with `GammaFunctionalEquation q ζ e G R Rdual`;
- every `Rdual ∈ T` has some `R ∈ S` with `GammaFunctionalEquation q ζ e G R Rdual`.

Then there are `c : ℂˣ` and `m : ℤ` such that for every pair
`R Rdual : RationalFunctions`, `GammaFunctionalEquation q ζ e G R Rdual`
implies `NormalizedFunctionalEquation q P Pdual ζ c e m R Rdual`. The pair
`(c, m)` depends only on the data above. The conclusion quantifies over all
rational pairs, not only members of `S` and `T`. It holds on the full
domain of `NormalizedFunctionalEquation`, where only the reduced denominators
of `R` at `q^{-s}` and of `Rdual` at `q^{-(1-s)}` are required to be nonzero.

## Proof

Write `δ = q⁻¹` as a unit and `ρ = RationalReflection.subst δ`. This is the
algebra involution `X ↦ δ/X` of `RatFunc ℂ`.

1. `exists_laurent_subst`: the image of a Laurent polynomial under `ρ` is again
   such an image. The proof uses induction over Laurent polynomials. The
   monomial `a T^n` goes to `(a δ^n) T^{-n}`.
2. `rational_identity_of_gammaFunctionalEquation`: a gamma equation gives the
   rational identity `ρ(Rdual) = C(ζ^e) · (G · R)`. Both sides are regular and
   agree at `q^{-t}` for all real `t` outside a finite set: the zeros of the
   denominators of `R`, `G` and the reflected `Rdual`. These points are
   infinitely many, and `rationalFunction_eq_of_infinite_eval_eq` concludes.
   The evaluation of `ρ` uses `RationalEvaluation.eval_subst` and the identity
   `q⁻¹ / q^{-s} = q^{-(1-s)}`.
3. `subst_mem_zetaSpan`: for `f ∈ zetaSpan S`, `ρ(C(ζ^e) · (G · f)) ∈ zetaSpan T`.
   `exists_subst_eq_mul`: for `f ∈ zetaSpan T`, `ρ(f) = C(ζ^e) · (G · g)` for
   some `g ∈ zetaSpan S`. Both use induction over the span with step 2 on
   generators. Laurent scalars pass through `ρ` by step 1.
4. Apply step 3 to the generators. Let `Pr` and `Pdr` be the images of `P` and
   `Pdual`. The first incidence gives `ρ(Pr⁻¹ · C(ζ^e) · G) = b · Pdr⁻¹`, with
   `b` Laurent. Applying `ρ` and step 1 gives a Laurent `b'` with
   `C(ζ^e) · G · ρ(Pdr) = b' · Pr`. The second incidence gives a Laurent `d`
   with `Pr = d · (C(ζ^e) · G · ρ(Pdr))`. The field lemmas
   `mul_eq_of_mul_inv_eq` and `eq_mul_of_inv_eq` clear the nonzero
   denominators `Pr` and `ρ(Pdr)`. `mul_eq_one_of_cycle` gives
   `b' d = 1` after injectivity of `laurentToRatFunc`.
5. `exists_monomial_of_mul_eq_one`: a unit of `LaurentPolynomial ℂ` is
   `C c · T m` with `c : ℂˣ`. Clearing powers of `T`, a product of two
   polynomials is `X^(k+l)`. Since `X` is prime, each factor is associated to a
   power of `X`.
6. Therefore `C(ζ^e) · G · ρ(Pdr) = C c · X^m · Pr`. Fix a gamma pair
   `(R, Rdual)` and multiply by step 2's identity to obtain
   `ρ(Pdr · Rdual) = C c · X^m · (Pr · R)`. Evaluate at `q^{-s}`. The
   hypotheses of `NormalizedFunctionalEquation` make `Rdual` regular at
   `q^{-(1-s)}` and `R` regular at `q^{-s}`. Polynomials, constants and
   integer powers of `X` are regular at the nonzero point `q^{-s}`.
   `eval_algebraMap_polynomial` turns the evaluation of `Pr` and `Pdr` into
   polynomial evaluation. The result is the normalized equation with constant
   `(ζ^e)⁻¹ c`. The factor `ζ^e` is then reinserted, giving
   `ζ^e · epsilonMonomial q ((ζ^e)⁻¹ c) m s = c · (q^{-s})^m`.

The proof uses no evaluation of `G` in step 6, so removable poles of the
displayed gamma expression do not shrink the domain.

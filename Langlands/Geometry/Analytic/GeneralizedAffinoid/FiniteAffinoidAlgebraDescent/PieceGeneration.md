# Explicit generators of the right leg of an affinoid pushout

This helper module proves one lemma in the namespace
`Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout`.

`rightMap_coefficientMap_leftMap`: let `f : A → B` and `g : A → C` be bounded
`K`-algebra maps of presented affinoid algebras over a complete ultrametric
normed field `K`. Suppose that `b : Fin n → B` generates `B` over `A` with norm
control, that is, every `y ∈ B` equals `∑ₖ f(aₖ) bₖ` with `‖a‖ ≤ M‖y‖`. Then
the images `leftMap f g (bₖ)` generate the affinoid pushout `algebra f g` over
`C` through `rightMap f g`, with a norm-control constant `D > 0`.

## Provenance and proof

The Library's `FiniteBanachPushout.Proof` proves that `rightMap f g` is finite
Banach (`rightMap_isFiniteBanach`), but its statement does not name the
generators. This lemma repeats that argument with the generators made
explicit; it is an internal adaptation of the Library proof and does not cite
outside literature.

1. `tensorMap f g` from the completed tensor algebra is an admissible
   epimorphism (`tensorMap_isAdmissibleEpi`). Hence every `z` in the pushout
   has a preimage `y` with `‖y‖ ≤ H‖z‖`.
2. The image of the algebraic tensor product is dense. Choose `t ∈ B ⊗ C` close
   to `y`, and choose a tensor representation of `t` whose value is close to
   its seminorm.
3. The Library lemma `exists_coefficient_lift_representation` expands every
   `B`-factor through the generators `b` and gives coefficients `c` in `C`.
   Their combination `∑ₖ rightMap(cₖ) · leftMap(bₖ)` equals the image of `t`,
   and `‖c‖ ≤ N M (H + 1) ‖z‖`.
4. The resulting error is at most `‖z‖ / 2`. The Library's
   `exists_normControlledLifts_of_approx` turns these approximate solutions
   into exact ones with a uniform norm constant.

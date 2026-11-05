# Actual coefficient-tensor forms and inverse dual scaling

Author: Worker 200.

This unit reuses the existing Hermitian equivalence and positive smooth-dual
form to construct an invariant positive form on the actual coefficient tensor
of a canonical admissible smooth complex representation. It proves inverse
dual scaling and cancellation on the whole tensor after positive real rescaling.

## Source and scope

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI [10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082),
V.2, printed p.293 / PDF p.59, the paragraph before Lemma V.2.2.
The source uses Hermitian forms conjugate-linear in the first variable.
It equips the smooth dual with the induced positive form, and observes that
positive real scaling on the original representation gives reciprocal scaling
on that dual. This cancels in the product of the two forms.

This module proves that reciprocal scaling for the existing actual
`HarishChandraSchwartz.dualInvariantForm`, rather than selecting two unrelated
forms with an assumed reciprocal relation. It then constructs a positive
invariant form on the canonical tensor `CoefficientTensor A`, using `b` and
that actual dual form, and proves equality of the whole tensor forms after
positive rescaling. This is a derived internal prerequisite of the source
construction. It does not identify this generic tensor form with the source's
normalized product of the two parabolically induced integral forms.

## Objects and hypotheses

The group `G : Type uG` and the algebraic complex carrier `V : Type uV`
have independent universes. `rightFunctional_rescale` needs only a group,
an algebraic complex representation `ρ`, and an actual
`InvariantPositiveForm ρ`. `toSmoothDual_rescale` additionally uses a
topology on `G` and smoothness of `ρ`; it needs no continuity of group
operations.

The equivalence and dual-form identities use a topological group, an
admissible representation `ρ`, and the explicit cofinality condition

`∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
  IsCompact (L : Set G) ∧ L ≤ K`.

For the coefficient form, `A : SmoothRep ℂ G` is the canonical smooth
representation and `hA : IsAdmissible A.representation`. The same
cofinality condition is retained. No irreducibility, nonzero-carrier
assumption, norm or topology on the carrier, finite-dimensionality of the
whole carrier, or finite-length condition is imposed.

The scalar is an arbitrary real `a` with `ha : 0 < a`.

## Inverse dual scaling

The following declarations are in `Langlands.InvariantPositiveForm`.

* `rightFunctional_rescale` states
  `(b.rescale a ha).rightFunctional v = a • b.rightFunctional v`,
  with the real scalar embedded into the complex field.
  Extensionality reduces this to the definition of positive rescaling.
* `toSmoothDual_rescale` is the same equality in the actual smooth-dual
  subtype. Its proof is subtype extensionality applied to the functional law.
* `smoothDualEquiv_rescale` is the pointwise equality for the existing
  conjugate-linear equivalences, which apply as `toSmoothDual` by definition.
* `smoothDualEquiv_rescale_symm` states that the inverse for `a b` sends
  every smooth functional `ℓ` to `a⁻¹` times the inverse for `b`.
  Apply injectivity of the rescaled equivalence. Its conjugate-linearity,
  reality of `a⁻¹`, and the inverse identity reduce the result to
  `a * a⁻¹ = 1`.

Write `E = b.smoothDualEquiv hcof hρ`. The existing smooth-dual form is

`dualInvariantForm b hcof hρ (ℓ,m) = b(E.symm m, E.symm ℓ)`.

The swap of the two arguments is essential because `E` is conjugate-linear.
`Langlands.HarishChandraSchwartz.dualInvariantForm_rescale` proves equality
of the actual invariant positive forms:

`dualInvariantForm (a b) = a⁻¹ dualInvariantForm b`.

The proof applies form extensionality, substitutes the proved formula for
both inverse images, and uses conjugate-linearity in the first variable and
linearity in the second. There are two inverse factors from the inverse
images and one original factor `a`, leaving `a⁻¹`. The real-scalar
conjugation and the nonzero condition are proved from `ha`.

## Actual coefficient tensor form

The remaining declarations are in `Langlands.Plancherel`.

`coefficientTensorInvariantForm A hcof hA b` is

`b.tensorProduct (dualInvariantForm b hcof hA)`.

Its type is `InvariantPositiveForm (coefficientTensorAction A)`.
Thus it is positive definite on the original algebraic tensor
`A ⊗[ℂ] SmoothDual A.representation`, and invariant for the existing
external `G × G` action: the first coordinate acts on vectors and the
second acts on smooth functionals. This is the existing coefficient
tensor and action, not a newly introduced tensor or dual framework.

`coefficientTensorInvariantForm_inner_tmul` gives, for every pure pair,

`(v ⊗ ℓ, w ⊗ m) = b(v,w) * dualInvariantForm b(ℓ,m)`.

`coefficientTensorInvariantForm_rescale` proves equality of the forms on
all tensors after replacing `b` by `b.rescale a ha`. It rewrites the
actual dual by `dualInvariantForm_rescale` and applies the existing
all-tensor reciprocal cancellation theorem `tensorProduct_rescale_inv`.

## Reuse and remaining obligations

The module imports `CoefficientTensors`, `Unitary.PositiveFormTensor` and
`SquareIntegrableSemisimplicity`. It reuses the published actual
`rightFunctional`, `toSmoothDual`, `smoothDualEquiv`, and
`dualInvariantForm`; none is reconstructed. Tensor positivity and
external invariance come from `tensorProduct`, whose positivity reuses
the existing binary tensor-core theorem.

Admissibility is an explicit hypothesis here, not a theorem asserted for all
induced representations. The module proves independence under a specified
positive rescaling, not uniqueness of all invariant positive forms up to
such a rescaling. Actual parabolic integral forms and their Haar normalization,
induction-duality and product-induction comparisons, the source's inverse
formal-degree factor, representative independence of this positive form,
smooth spectral-family forms, and the analytic Plancherel obligations remain
separate. No whole-task completion condition is closed by this helper.

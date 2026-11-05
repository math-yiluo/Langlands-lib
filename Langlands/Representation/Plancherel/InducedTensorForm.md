# Actual induced tensor forms and positive rescaling

This module constructs a positive invariant form on the literal algebraic
tensor of normalized induction of `A` and normalized induction of its actual
smooth contragredient. It also gives computation, positive rescaling and
pullback laws for the existing compact quotient induced form. All integrations
retain the measure already chosen by that construction.

## Provenance and source boundary

This is a derived adapter of the existing normalized induction, compact
quotient integration, positive tensor and smooth-dual constructions. Its
motivation is Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), V.2, printed p.293 / PDF p.59, the paragraph
before Lemma V.2.2. That paragraph integrates the inducing Hermitian form,
constructs the form on induction of the smooth dual, and takes their tensor
product with the additional inverse formal-degree factor. The convention is
conjugate-linearity in the first argument. Reciprocal positive scaling of the
two inducing forms gives independence under a specified positive rescaling.

The form here includes both actual induced factors. It has no inverse
formal-degree factor and uses the literal Bruhat measure choice in the existing
`compactQuotientNormalizedInductionForm`. It does not identify that choice with
the task's fixed compact Haar normalization. The source's normalized form,
its identification with other coefficient-tensor models, and independence
between arbitrary invariant positive forms are therefore not claimed here.
No assertion about Lemma V.2.2 or the Plancherel formula follows from this unit.

## Setting and hypotheses

`G : Type uG` is a locally compact Hausdorff nonarchimedean topological group.
It has a Borel measurable space. Actual subgroups `P`, `M`, `U` are supplied
with `h : IsSemidirectDecomposition P M U`. The subgroup `U` is closed. For
integration, `P` is closed and locally compact and the actual left quotient
`Induction.LeftQuotient P` is compact. The modular-character assumptions are

- `hG : ∀ g : G, Measure.modularCharacter g = 1`;
- `hδ : ∀ q : P, Measure.modularCharacter q =
  (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0)`.

Thus `hδ` identifies the full positive Haar modulus of the actual radical with
the parabolic modular character. It is not a half-modulus assumption. The
induction is the existing `Aubert.General.normalizedInductionFunctor h hU`,
whose covariance uses the positive half modulus.

The computation, rescaling and pullback laws take a canonical smooth complex
Levi representation and a chosen invariant positive form. They require no
admissibility, irreducibility, nonzero-carrier assumption, finite length or
finite dimensionality. The group and carrier universes `uG`, `uV`, `uW` are
independent. In the pullback law the two Levi carriers can have different
universes. Their induced carriers are in the respective maximum with `uG`.
No norm or topology is imposed on either original complex carrier.

For the tensor form, the chosen inducing representation `A` additionally has
`hA : IsAdmissible A.representation` and `hcof : CompactOpenCofinal M`.
These are exactly the inputs used by the existing actual smooth-dual form;
no admissibility or irreducibility of an induced representation is assumed.
The action and tensor carrier alone need none of the integration, cofinality
or admissibility hypotheses.

## The existing induced form and its literal measure

The following three declarations are in `Langlands.Aubert.General`. Write

```lean
μ := Classical.choose (Induction.exists_compactQuotient_measure hG P hP)
```

for the literal measure on `(⊤ : Subgroup G)` already chosen in
`compactQuotientNormalizedInductionForm`. It depends on the existing group,
subgroup, topology and modular data, and not on the inducing form or its
carrier. The selected measure is supplied by the published compact quotient
Bruhat construction. In particular, this module does not replace it with a
new quotient measure or an arbitrarily scaled Haar measure.

`compactQuotientNormalizedInductionForm_inner` unfolds the existing definition:
for actual induced functions `f`, `j`, its inner product is

```text
∫ k, b.inner (f(k)) (j(k)) dμ(k).
```

Here evaluation is the existing
`Induction.eval P (inducingRepresentation h hU A)`. The proof is definitional
equality. The existing measure is positive on every open neighborhood of the
identity. Integration against it is unchanged by right translation for locally
constant functions satisfying `φ(q*x) = Δ_P(q) * φ(x)`. The actual induced
pairings satisfy this covariance by `normalizedInduction_pairing_covariant`
and the full modular identity `hδ`. These restricted integral identities give
invariance of the resulting form. No right-invariance assertion about the
measure on `G` is made.

`compactQuotientNormalizedInductionForm_rescale` states equality of actual
invariant positive forms:

```text
Iform(A, rescale(b,a)) = rescale(Iform(A,b),a),  a > 0.
```

It applies `InvariantPositiveForm.ext_inner`, the literal integral computation,
the definition of rescaling, and `integral_const_mul`. Both sides integrate
against exactly `μ`. No measure comparison or normalization identity is
assumed.

`compactQuotientNormalizedInductionForm_ofEquiv` states that pulling a form
back by an actual Levi representation equivalence and then inducing agrees
with pulling the induced form back by `normalizedInductionEquivOfEquiv`.
The form on the source is the actual `b.ofEquiv e`, not an independent form
assumed to match. The proof applies extensionality, unfolds both integrals
against the same measure, and uses the defining pointwise action of the
induced equivalence. It makes no claim of independence between arbitrary
choices of forms or equivalences.

## The two actual induced factors

The remaining declarations are in `Langlands.Plancherel`. The module imports
and reuses the existing `NormalizedInductionDualTensor h hU A` and
`normalizedInductionDualTensorAction` from
`Plancherel.NormalizedInductionDualTensor`. Their carrier is the literal tensor

```text
I_P^G(A) ⊗[ℂ] I_P^G(A.contragredient).
```

The existing external `G × G` action uses the first coordinate on the first
induced representation and the second on induction of the inducing smooth
dual. It is `Representation.tprod` of the two actions pulled back along the
projections. The imported definitions do not identify induction of the smooth
dual with the smooth dual of induction. No second carrier or action is defined
in this module. The named `normalizedInductionBruhatMeasure hP hG` in that
existing module is definitionally the literal chosen `μ` above.

`normalizedInducedDualTensorForm` applies the existing positive binary tensor
construction to `Iform(A,b)` and
`Iform(A.contragredient, dualInvariantForm b hcof hA)`. It is therefore an
actual positive definite Hermitian form invariant under that external action.
Its positivity uses the existing positive tensor core on arbitrary algebraic
carriers; it imposes no completion or finite-dimensionality hypothesis.

`normalizedInducedDualTensorForm_inner_tmul` gives the product of the two
actual induced inner products on pure tensors. Applying the preceding literal
integral computation to each factor gives the product of their integrals
against the same selected `μ`.

`normalizedInducedDualTensorForm_rescale` states equality of the entire tensor
forms after any specified strictly positive real rescaling of `b`. The existing
`HarishChandraSchwartz.dualInvariantForm_rescale` first gives reciprocal scaling
of its actual smooth-dual form. The induced-form rescaling law above then
propagates both scalars through the two actual inductions. Typed congruence
combines those equalities; `InvariantPositiveForm.tensorProduct_rescale_inv`
cancels them on all tensor pairs, including sums of pure tensors. The result
is not restricted to the pure-tensor computation.

## Remaining obligations

The closedness and compactness hypotheses and the full modular identity remain
visible geometric inputs here; the general rational parabolic realizations
must still be supplied. The fixed compact Haar normalization, source inverse
formal-degree factor, induction-duality and product-induction comparisons,
representative and arbitrary-form independence, smooth spectral-family forms,
Lemma V.2.2 and all seven whole-task completion conditions remain separate
obligations. This unit supplies the actual integral-form scaling and actual
two-induced-factor tensor construction needed for that later assembly.

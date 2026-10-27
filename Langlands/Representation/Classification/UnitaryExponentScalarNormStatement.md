# Scalar norms from arbitrary unitary exponent data

`Langlands.UnitaryExponentScalarNorm.{uG,uV}` is a closed proposition
definition. Let `ρ` be a representation on a nonzero complex vector space. If
an element `g` acts by a scalar `c`, and `ρ` has any unitary exponent witness
`u` for the positive character `ν`, the statement says that the absolute value
of `c` is the real power `ν(g) ^ u.exponent`. The file provides no proof. It
does not prove this norm identity, and it asserts no existence of forms,
exponents, scalar-acting elements or central characters.

## Quantifiers and hypotheses

The statement quantifies over:

- every group `G : Type uG` with `Group G`. No topology, measure, local
  compactness or finiteness condition is put on `G`;
- every complex vector space `V : Type uV` with `AddCommGroup V`,
  `Module ℂ V` and `Nontrivial V`. No norm, topology, completion or
  finite-dimensionality is put on `V`. The universes `uG` and `uV` are
  independent;
- every positive character `ν : G →* ℝ≥0ˣ`, a group homomorphism to the
  positive real numbers;
- every actual representation `ρ : Representation ℂ G V`;
- every `u : UnitaryExponentData ν ρ`, the published witness structure of
  `Langlands.Representation.Classification.Essential`, whose fields are a real
  number `u.exponent` and a form
  `u.form : InvariantPositiveForm (realPowerTwist ν (-u.exponent) ρ)`;
- every element `g : G` and every complex number `c : ℂ`.

The only hypothesis is `∀ v : V, ρ g v = c • v`: the operator of `g` is
multiplication by `c` on all of `V`.

There are no further hypotheses. In particular there is no irreducibility,
admissibility, smoothness, square-integrability or central-character
hypothesis. No nonzero vector is chosen, and `c` is not required to be
a unit. The form is an arbitrary field of the arbitrary witness `u`. It is
not replaced by a central character, and it is not compared with another form.

## Conclusion and the negative-twist sign

The conclusion is

`‖c‖ = ((ν g : ℝ≥0) : ℝ) ^ u.exponent`.

On the left, `‖c‖` is the absolute value of the complex number `c`. On the
right, `ν g` is coerced from `ℝ≥0ˣ` to `ℝ≥0` and then to `ℝ`, and is raised
to the real power `u.exponent` with `Real.rpow`. The base is a positive real
number, so the power is positive.

The sign comes from the published convention in `UnitaryExponentData`. The
form is invariant for the **negative**-exponent twist
`realPowerTwist ν (-u.exponent) ρ`, which acts on the same carrier `V` by

`(realPowerTwist ν (-e) ρ) g v = (ν(g) ^ (-e)) • ρ g v`, with `e = u.exponent`.

The published law `realPowerTwist_cancel_neg` (`UnitaryExponentData.reconstruct`)
gives `realPowerTwist ν e (realPowerTwist ν (-e) ρ) = ρ`. So `ρ` is the `+e`
twist of a representation that preserves the form. Informally, each `ρ g`
scales form lengths by `ν(g) ^ e`, which is why the statement asserts that a
scalar operator has absolute value `ν(g) ^ (+e)`. If the form were invariant
for the `+e` twist instead, the right-hand side would be `ν(g) ^ (-e)`. That
convention is not the one stated here.

## The exact telescope

This is the elementary calculation that the statement records. It is not
proved in this file. Fix a nonzero `v : V`, write `e = u.exponent`, write
`⟪·,·⟫` for `u.form.inner`, which is conjugate-linear in its first argument,
and put `k = ν(g) ^ (-e) · c`.

1. Scalar action through the twist:
   `(realPowerTwist ν (-e) ρ) g v = ν(g) ^ (-e) • ρ g v = ν(g) ^ (-e) • (c • v) = k • v`.
2. Invariance of `u.form` under the twisted action at `(v, v)`:
   `⟪k • v, k • v⟫ = ⟪v, v⟫`.
3. Sesquilinearity: `⟪k • v, k • v⟫ = conj(k) · k · ⟪v, v⟫`.
4. Positive definiteness: `⟪v, v⟫ ≠ 0` because `v ≠ 0`. Cancelling it gives
   `conj(k) · k = 1`, so `‖k‖ ^ 2 = 1` and `‖k‖ = 1`.
5. The factor `ν(g) ^ (-e)` is a positive real number, so
   `‖k‖ = ν(g) ^ (-e) · ‖c‖`, and `ν(g) ^ (-e) · ‖c‖ = 1`.
6. The real-power identity `ν(g) ^ (-e) = (ν(g) ^ e)⁻¹` (`Real.rpow_neg` for
   a nonnegative base) and positivity of `ν(g) ^ e` give `‖c‖ = ν(g) ^ e`.

So the exponents telescope as `-e + e = 0`. This is the same cancellation as
in `realPowerTwist_cancel_neg`, now read on the absolute values of a single
scalar.

The scalar does not have to be a unit. Step 4 forces `‖k‖ = 1`, so `k`, and
hence `c`, is nonzero. This is consistent with the genuine group action: each
`ρ g` is invertible, with inverse `ρ g⁻¹`, so it cannot be `0` on a nonzero
space.

## Why `Nontrivial V` is needed

If `V` is the zero space, then `ρ g v = c • v` holds for every `c`, because
both sides are `0`. The positive-definite form also gives no information. For
example, `c = 0` satisfies the hypothesis, but `ν(g) ^ e > 0`, so the
conclusion would be false. The hypothesis `Nontrivial V` supplies the nonzero
vector cancelled in step 4. The statement makes no assertion about the zero
carrier.

## Provenance (internal derived statement)

This exact statement is not quoted from any source. It is an internal,
elementary consequence of two published definitions:

- `InvariantPositiveForm` (`Langlands.Representation.Unitary.Basic`), a
  positive definite Hermitian form (`InnerProductSpace.Core ℂ V`) on the
  carrier that every action operator preserves;
- the real-power twist `realPowerTwist` (`Langlands.Representation.Twist.RealPower`),
  the actual twist by the positive character `g ↦ ν(g) ^ s`, together with its
  packaging in `UnitaryExponentData`
  (`Langlands.Representation.Classification.Essential`).

No source theorem is cited, so no literature or errata are involved. The
statement is a reusable step for comparisons of arbitrary positive-form
exponent witnesses, such as the published proposition
`Langlands.Classification.LinkedSegmentHeadExponentComparison`. That
proposition quantifies over arbitrary witnesses, so a proof of it is expected
to extract the norm information from every supplied form before it can use
scalar-character formulas. The Library proof
`ChosenUnitaryNormalizationProof` makes a similar inner-product calculation
inside a theorem that assumes square-integrability, and it exports no generic
helper. That proof is not a source for this statement.

The module imports only `Langlands.Representation.Classification.Essential`.
It does not depend on any linked-head comparison, square-integrable
nonlinkage, ordered conversion, exhaustion, classification, tempered-block
uniqueness, ordered-head existence or quotient-coverage result.

## Proof obligations

A proof must establish the identity for every `G`, `V`, `ν`, `ρ`, `u`, `g`
and `c` satisfying only the stated hypothesis. It must use the supplied form
`u.form`, with steps 1–6 above or an equivalent argument, and the real-power
identity. It may not add hypotheses or assume a central character or the
existence of other forms. Publishing this statement proves neither the norm
identity nor any linked-head exponent comparison.

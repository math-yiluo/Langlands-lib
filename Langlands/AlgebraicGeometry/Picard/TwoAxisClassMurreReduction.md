# Representability of the two-axis class presheaf from Murre's criterion

Module `Langlands.AlgebraicGeometry.Picard.TwoAxisClassMurreReduction` proves
two conditional theorems. It assumes none of its hypotheses globally and adds
no axioms.

## Theorems

`noetherianTwoAxisClassRepresentability_of_murre` takes

- `hM : UnramifiedFunctor.MurreCriterionStatement.{u, u + 1}`, Murre's
  criterion for presheaves valued in `Type (u + 1)`;
- the ten statements of `TwoAxisClassMurreConditionsStatement`, from
  `NoetherianTwoAxisClassSmallValuesStatement.{u}` to
  `NoetherianTwoAxisClassGenericNonLiftingStatement.{u}`,

and concludes the published
`NoetherianTwoAxisClassRepresentabilityStatement.{u}`.

`noetherianTwoAxisClassRepresentability_of_murreConditions` concludes the same
from `hM` and the bundled `NoetherianTwoAxisClassMurreConditionsStatement.{u}`.

## Proof

Let `R` be a noetherian ring in `Type u` and `A` an abelian scheme over
`Spec R`. Mathlib's instances make `Spec R` locally noetherian. Apply `hM` to
`S = Spec R` and `F = TwoAxisRigidifiedLineBundle.classPresheaf A`, valued in
`Type (u + 1)`. Its ten hypotheses are the ten condition statements
specialized to `R` and `A`. Its conclusion gives `Y : Scheme.{u}` and
`q : Y ⟶ Spec R` with a representation `F.RepresentableBy (Over.mk q)`, and
with `q` separated, locally of finite type and formally unramified. This is
literally the conclusion of `NoetherianTwoAxisClassRepresentabilityStatement`
for `R` and `A`.

The second theorem splits the conjunction into its ten components and applies
the first.

## Source

This is the reduction in the proof of Raynaud, LNM 119, Theorem III 4.4
(printed p.53). After reducing to a noetherian affine base, Raynaud concludes
from Murre's Theorem 4 (Séminaire Bourbaki exp. 294, printed p.256), whose
proof checks the conditions of Murre's Theorem 1. The citations are in the
paired Markdown of `MurreCriterionStatement` and
`TwoAxisClassMurreConditionsStatement`.

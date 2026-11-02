# Full Whittaker type from supplied square-integrable genericity

Author: Worker 192.

`Langlands.RankinSelberg.squareIntegrableWhittakerType_of_genericity`
proves the closed conditional proposition
`SquareIntegrableWhittakerTypeOfGenericityStatement.{uF,uV}` from
[its statement module](SquareIntegrableWhittakerTypeOfGenericityStatement.md).
The input
`Classification.SquareIntegrableGenericity.{uF,uV} F F.canonicalTopologicalData`
remains explicit. This result does not prove that genericity proposition
or the closed square-integrable pole-freeness theorem.

The proof concerns every prime and specified p-adic field with its canonical
topology, every continuous nontrivial unitary additive character, every
positive rank including one, and the original representation on
`V : Type uV`. The field universe `uF` and carrier universe `uV` remain
independent. No carrier topology or finite-dimensionality is required.

First, the published analytic square-integrability predicate supplies
admissibility through `IsSquareIntegrable.isAdmissible`.
`Langlands.glSquareIntegrableUnitarity` supplies an actual invariant positive
Hermitian form from irreducibility and square-integrability; unitarizability
is therefore not an extra assumption.

The smoothness clause of admissibility bundles the original action as
`A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (n + 1) F.Carrier)`.
`SmoothRep.universeLift.{uF} A` has carrier in `Type (max uF uV)`,
as required by the supplied genericity proposition.
The published `isIrreducible_universeLift_iff`,
`isSquareIntegrable_universeLift_iff`, and
`isUnitarizable_universeLift_iff` transport all three needed properties to
this actual lifted action. The square-integrability transport preserves
the existing central-quotient coefficient condition and all its Borel
Haar measure quantifiers.

Applying the explicit input to the lift and the same character gives
`Whittaker.IsGeneric` there.
`Whittaker.isGeneric_iff_of_equiv`, applied to the actual
`SmoothRep.universeLiftEquiv`, transports this conclusion back to the
original action on `V`.
Finally, `RankinSelberg.isOfWhittakerType_of_isGeneric` from `GenericModel`
uses published multiplicity one and the algebraic
`whittakerTypeFromMultiplicity` theorem. Its conclusion supplies
admissibility, finite generation over the group algebra, and a linear
equivalence of the full functional space with `ℂ`. The positive standard
character is preserved throughout.

The proof is internal assembly of these published declarations, adapted
from Worker 192's earlier private pole-freeness assembly helper. It reuses
the existing genericity-to-Whittaker-type construction by Lean name.
No source assertion or classification statement is used as a proof of
genericity, and no original literature theorem is newly asserted.

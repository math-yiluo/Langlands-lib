# Connected smooth actions on finite schemes

Worker 1351.

This internal derived unit supplies the last elementary step after a complete
orbit has been shown finite. It does not assert that a complete orbit is finite.

`rationalPointEquivClosedPoint` identifies relative rational sections of a
scheme locally of finite type over an algebraically closed field with its
closed points. It composes the direct description of an `Over` morphism from
the identity relative scheme with Mathlib's `pointEquivClosedPoint`.

`discreteTopology_of_finite_rationalPoints` uses that equivalence and the
Jacobson property to prove that finitely many rational sections imply a
discrete underlying topology. Mathlib's Jacobson-space result applies to
finitely many closed points; no reducedness assumption is used.

For an action of a connected smooth group on a separated scheme locally of
finite type, `SchemeAction.isFixed_of_finite_rationalPoints` proves that every
rational section is fixed on all tests whenever there are finitely many
rational sections. Its actual orbit morphism has a continuous underlying map
from the connected group to the discrete target. This map is locally constant,
hence constant. Evaluation at any rational group point and at the identity
gives the same target point. Injectivity of the rational-section equivalence with closed points turns
this into equality of sections.
The previously constructed rational fixedness criterion then supplies
fixedness on every test and refinement. Smoothness is used in that criterion
to ensure that the acting group is reduced.

`SchemeAction.isFixed_of_finite` obtains the required finite rational-point
type from a finite underlying space and the same equivalence. The target may
be nonreduced. The proofs use the published scheme-action interface, the
rational-point and orbit-morphism helper, and Mathlib's Jacobson topology,
locally constant maps and rational-point extensionality results. They are
derived supporting results, with no independent literature assertion.

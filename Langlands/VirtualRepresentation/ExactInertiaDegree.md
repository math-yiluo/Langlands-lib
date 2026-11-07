# Inertia dimension and unramifiedness on exact virtual groups

Author: Worker 1646. This is internal infrastructure for task
`f096b984-dff5-4425-861f-8f298e5896fb`, whose exact target is
`Langlands.ClassField.Global.RelativeWeilGroup.WeakInductionAssociationStatement`.
It derives a detection criterion from already published finite-dimensional
representations, actual invariant spaces, and exact virtual groups.

For an arbitrary group, a supplied normal subgroup `I`, and a predicate `P` on
finite-dimensional complex representations, `invariantsClassDegree` records the
integer dimension of the actual `I`-fixed space. Equivalences preserve this
dimension by the published `invariantsEquiv` and `rank_eq_of_equiv`.

If every object satisfying `P` has finite image of `I`, the published averaging
argument `FiniteRepresentation.isShortExact_invariants` makes the fixed-space
sequence short exact. The published `rank_eq_add_of_shortExact` therefore proves
exact additivity, and the universal exact quotient map `lift` descends this
dimension function to `invariantsDegree`. The integer-valued homomorphism
`inertiaCodimension` is total degree minus invariant degree.

For a genuine object, zero codimension is equivalent to its fixed space having
full dimension. Mathlib's `Submodule.eq_top_iff_finrank_eq` identifies this with
the fixed space being the whole carrier, hence with the actual `IsUnramified`
predicate. Applying the codimension homomorphism to a virtual identity shows
that a representation whose class is a finite sum of unramified genuine
classes is itself unramified. No semisimplicity of the whole group action is
assumed.

The final specialization concerns the actual local Weil group of any p-adic
field, in independent field and carrier universes. The published
`Langlands.Weil.Local.localWeilContinuity` supplies finite inertia image for
every continuous representation, so
`Langlands.Weil.Local.isUnramified_of_continuousClass_eq_sum` needs only a
continuous exact-class identity and unramifiedness of its summands.

This module neither constructs a local reciprocity map nor proves any pending
arithmetic restriction formula. Its provenance is the structural exactness and
dimension arguments just described.

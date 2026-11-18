# Finite free models for analytic open-subgroup cochain descent

This is an internal adapter between `TwistedFreeRepresentableCochain` and
`FiniteFixedCochainDescent`. It specializes the generic finite signed model to
the actual compact analytic lift system of an open subgroup. The argument uses
the published preservation of injectives by open-subgroup restriction. It does
not prove the existence of geometric tuple cones or compatible analytic lifts.

`OpenSubgroupFiniteFreeThreeTermModel` is the generic
`GlobalLift.FiniteFreeThreeTermModel` on the original quasi-étale site, with its
actual compact lift system for the subgroup action. Its three finite families
of globally lifted objects, eventual equivariance, signed boundaries, ordinary
comparison isomorphisms and both differential squares are supplied inputs.

For a coefficient quasi-étale `G`-sheaf and an ordinary cochain,
`cochainSections` evaluates the cochain on the middle free summands through the
model's specified comparison isomorphism. `FixesCochain` is the proposition that
these precise sections are fixed by the model's global actions after mapping
them into the original twisted site. `fixedSections` interprets that condition
as `GlobalLift.FixedSections` for the actual subgroup-restricted coefficient;
its values are unchanged.

`cochainLift` installs the subgroup's finite-refinement, sheafification and
pointwise Kan-extension instances from the full-group hypotheses. It applies
the generic finite model's `cochainLift`, using exactness of the ordinary chain
segment. The coefficient comparison is the actual
`quasiEtaleGSheafSubgroupRestrictionCompRestrictionIso`; its underlying
comparison is the identity, so the represented section equality follows from
the definition of `cochainSections` and composition with an identity.

`exactAt_of_openSubgroupFiniteFreeModels` assumes that the ordinary chain
segment is exact and that each ordinary cocycle admits an open subgroup and a
finite signed model satisfying `FixesCochain`. It constructs the exact
equivariant cochain lift, installs injectivity of the restricted coefficient
using the published open-subgroup restriction theorem, and applies
`EquivariantCochainLift.exists_primitive`. The resulting primitive proves
exactness of the ordinary module-valued Hom complex in that degree.

This is a conditional reduction with explicit finite-model and fixed-section
inputs. Neither those inputs nor ordinary segment exactness are deduced merely
from compactness in this module. It makes no claim that ordinary restriction
preserves injectives, and it does not assert the global comparison theorem.

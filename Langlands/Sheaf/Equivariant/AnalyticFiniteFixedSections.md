# Fixed sections for finite families of supplied analytic lifts

This is an internal specialization of the accompanying
`LocalActionFiniteFixedSections` construction to the published analytic
`liftSystem` and `liftAction`. It concerns an action `ρ` on an analytic space
over a complete ultrametric normed field, a morphism property `P`, and an
arbitrary admissibility predicate `Adm` on objects over that space. The group
has a topology. The construction requires no global continuity hypothesis,
compactness hypothesis, topology on the site or finite-refinement instance:
the individual action lifts and admissibility proofs are supplied as inputs.

`isAdmissible_liftAction` verifies directly from `liftSystem` that the full
local action associated to a supplied lift is admissible when its underlying
object satisfies `Adm`. The lift witnesses the defining existential, and its
restriction along the identity subgroup inclusion is the original action.

For a finite family of objects `U i`, supplied action lifts `l i`, admissibility
proofs, and sections of a discrete presheaf on the twisted category,
`finiteLiftFixedSections` produces `CommonFixedSections` below a prescribed
open subgroup `Q`. Its subgroup is contained in `Q` and every lift subgroup.
Every supplied section is fixed by this subgroup for the local action
`liftAction (l i)`. In that convention a group element `h` acts by the twisted
endomorphism with twist `h⁻¹` and underlying arrow `(l i).action h⁻¹`.
The proof applies the generic construction after verifying admissibility of
every full lift action.

For module coefficients over a commutative ring,
`iSup_liftFixedFamilySubmodule` applies the corresponding generic exhaustion
theorem: simultaneous fixed-family submodules, indexed by open subgroups
contained in `Q` and all lift subgroups, form a directed family whose supremum
is the whole product of the section modules. This is a submodule exhaustion,
not a categorical colimit construction.

For compact quasi-étale objects, use `P = quasiEtale` and
`Adm U = IsCompactSpace U.left`. A finite covering refinement carrying actual
source lifts can supply the family and admissibility data, and its common
acting subgroup can be used as `Q`. The generic
`fixed_restrict_of_intertwines` result can then transport fixedness along
arrows with supplied strict intertwining equalities.

This specialization does not construct lifts or covering refinements, prove
that compact objects form a basis closed under fiber products, identify
Čech nerve terms, or prove injective acyclicity or the global comparison
theorem. Its role is to synchronize the fixing subgroups for a supplied finite
family of sections.

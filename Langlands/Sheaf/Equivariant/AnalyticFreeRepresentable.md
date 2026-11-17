# Analytic actions and discrete free lifted representables

This internal adapter specializes `TwistedFreeRepresentableDiscrete` to
analytic actions. A continuous full action on a compact quasi-étale object,
equivariant over the base, gives an actual discrete lifted representable
provided compact-lift compatibility is supplied. That compatibility remains an
explicit, unproved geometric input.

For an ordinary object `U` of `P.Over ⊤ X` and an equivariant full action
`σ : G →* Aut U.left`, `actionGlobalLift U σ hσ` constructs a
`TwistedOver.GlobalLift`. Its arrow at `g` has twist `g⁻¹` and underlying
map `(σ g⁻¹).hom`. Multiplication follows from inversion and multiplication of
categorical automorphisms. No continuity is needed for this construction.
`fullActionLift` uses a supplied continuity proof to regard the same action as
an `ActionLift` with subgroup top.

`hasCompatibleCompactQuasiEtaleLifts_of_compatibilityStatement` applies the
published proposition `QuasiEtaleLiftCompatibilityStatement K` to the underlying
map of each ordinary over-category arrow. It assumes that proposition, the
Hausdorffness of the base and continuity of its action. It does not prove the
proposition.

`actionGlobalLift_eventuallyEquivariant` assumes
`HasCompatibleCompactQuasiEtaleLifts ρ`, compactness of `U`, continuity of `σ`
and its equivariance over the base. An admissible compact source action is a
restriction of an actual analytic lift. Apply compatibility to that lift and
`fullActionLift`, intersect the resulting open subgroup with the source
subgroup, and evaluate the intertwining equality at inverses. Twisted
extensionality then gives exactly the generic eventual-equivariance condition.
`actionGlobalLift_isDiscrete` applies the published equivalence with
representable discreteness.

`hasCompatibleCompactQuasiEtaleLifts_subgroup` transfers this same compatibility
condition to an open subgroup `H`. It first extends each `H`-lift to a
`G`-lift using `liftOfSubgroup`, applies the original compatibility condition,
and takes the inverse image of its resulting subgroup in `H`. Openness
follows by continuity of subgroup inclusion. This transfer requires neither
a proof of the Key Lemma nor a topological-group instance.

Assume local smallness of the ordinary quasi-étale category in universe `w`,
a commutative coefficient ring `R : Type w`, module sheafification on the
twisted site, and finite equivariant refinements for its compact lift system.
`actionDiscreteFreeSheaf` packages the free sheaf as an actual
`QuasiEtaleGSheaf ρ (ModuleCat R)` using the preceding eventual-equivariance
proof. `actionDiscreteFreeSheafOfMono` instead uses
`GlobalLift.eventuallyEquivariant_of_mono`: a monomorphic structure map
removes the compatibility, compactness and continuity premises, while retaining
the stated categorical and equivariance hypotheses.

For `a : ActionLift ρ U.hom` and a chosen open subgroup `H` contained in
`a.subgroup`, `liftGlobalLift` restricts the action to all of `H` and applies
`actionGlobalLift`. `liftGlobalLift_eventuallyEquivariant` combines
compatibility transfer with continuity of the restricted action.
`liftDiscreteFreeSheaf` then constructs the actual quasi-étale `H`-sheaf.
Its sheafification and finite-refinement hypotheses are explicitly imposed on
the subgroup's twisted site. As instances of the generic discrete free
construction, these objects have its fixed-section equivalence and ordinary
restriction isomorphism whenever the additional ordinary sheafification and
pointwise Kan extension hypotheses of that isomorphism hold.

The provenance is internal: these are compositions of the existing analytic
lift definitions, the explicit compact-lift compatibility condition and the
generic normalization construction. No new literature result is asserted, and
no analytic action or compatibility theorem is constructed. The general global
comparison and compatible exact Čech models remain open.

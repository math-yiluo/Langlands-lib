# Open-subgroup restriction preserves injectives

This internal categorical prerequisite specializes the discrete-sheaf induction
construction to quasi-étale analytic sheaves of modules. The group is small in
the module universe, the subgroup is open, and the compact local-action system
for the full group has finite equivariant refinements. Compactness of the base
space and continuity of its action are not needed for this prerequisite.

`quasiEtaleGSheafSubgroupInduction` is left Kan extension on the twisted sites
followed by sheafification, restricted to the discrete full subcategories.
Translation preserves the underlying analytic space of an object, so it
preserves the compactness condition used in the local-action system.
Smallness supplies the coset-indexed coproducts.

`quasiEtaleGSheafSubgroupInductionAdjunction` restricts the published ambient
induction-restriction adjunction along the two fully faithful inclusions.
The two squares commute by definition.

The induction functor preserves finite limits: after the target inclusion it
is the source inclusion followed by ambient induction. The source inclusion
preserves finite limits by the unconditional finite-limit closure of discrete
module sheaves. Ambient induction preserves finite limits because coproducts
of modules indexed by the subgroup cosets are exact. The fully faithful target
inclusion reflects limits, which gives the assertion in the discrete category.
The right adjoint therefore preserves injective objects, since its left adjoint
preserves monomorphisms.

All ingredients are derived from the existing subgroup induction, restriction,
and local-action constructions and Mathlib's adjunction and limit machinery.
No finite-refinement hypothesis on the subgroup is assumed. This module supplies
the restriction-of-injectives step; it does not assert vanishing of underlying
sheaf cohomology or prove the global comparison theorem.

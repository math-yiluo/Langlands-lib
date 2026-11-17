# Actual discrete coefficients in the ordinary compact-acyclicity reduction

The setup fixes a complete ultrametric normed base field `K : Type u`, a
normed extension `L : Type uL`, an actual analytic
`X : LocalizedCategory.{u, v, v}`, and supplied point axioms for every
`L`-valued point. A topological group `G : Type z` acts through analytic
automorphisms `ρ`. For `W = max u (v + 1) uL`, assume `Small.{W} G`,
admissible refinements for the distinguished lift system, and a commutative
ring `R : Type W`. Coefficients are arbitrary discrete diagrams of
`ModuleCat.{W} R` objects indexed by the lifted actual point family.

This internal adapter identifies the existing
`coefficientRestrictedSmoothPointProductFunctor` on a discrete diagram with the
actual independent-family sheaf used by the cutoff and c-softness proofs.
The identification is definitional: the diagram-to-family equivalence supplies
the coefficients, and taking the locally discrete coreflector followed by its
inclusion is the existing locally discrete subsheaf construction.

The concluding theorem supplies the exact ordinary compact-cohomology
vanishing for this coefficient functor when the underlying analytic space is
Hausdorff and `IsContinuousAction ρ` holds, from the explicit general
`CSoftAcyclicityStatement`. These two extra geometric hypotheses are needed for
the vanishing theorem, not for the definitional sheaf isomorphism.
The theorem applies to all coefficient diagrams, including the
injective diagrams needed by the Godement reduction. The general c-soft theorem
remains a premise until its independent proof is published. No local analytic
higher-direct-image vanishing is asserted.

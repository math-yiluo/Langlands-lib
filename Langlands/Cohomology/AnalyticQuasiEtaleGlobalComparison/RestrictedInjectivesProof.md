# Acyclicity after restriction of injective quasi-étale G-sheaves

`quasiEtaleRestrictedInjectivesAcyclic` proves
`QuasiEtaleRestrictedInjectivesAcyclicStatement` in all four universes of the
published statement. For a compact Hausdorff analytic base with continuous
action, the ordinary restriction of every injective discrete quasi-étale
equivariant sheaf of `R`-modules has zero ordinary quasi-étale cohomology
in each degree `q + 1`.

The finite equivariant refinement instance gives compatible finite covers
that refine covering sieves on compact objects admitting a local action
lift. The published `compactCompatibleTupleCones` theorem supplies a
limiting cone for every nonempty tuple of such a cover. Its vertex is
compact Hausdorff and carries a lift of the action. The binary construction
takes the inverse image of the cover target's analytic diagonal in the
product over the base, and iteration gives the tuple cones. Their
representatives give the finite free presentations of the Čech terms.
The published `quasiEtaleLiftCompatibility` theorem, applied with the
base's Hausdorffness and continuity of the action, supplies compatibility
of the local lifts along the morphisms used in the Čech complexes.

The proof uses `homAcyclic_of_compactTupleCones` for positive Hom exactness
against the ordinary restriction of the injective equivariant coefficient.
In each positive degree, the finite tuple models involve three adjacent
Čech terms. Discreteness lets one shrink to an open subgroup fixing the
finitely many sections of a cocycle, and lift compatibility lets the
faces descend to equivariant maps on a common open subgroup. Restriction
to that subgroup preserves injectivity. The equivariant model then
supplies a primitive for the ordinary cocycle.

The proof supplies the ordinary site's local smallness, sheafification,
enough injectives, and characterization of sheafification equivalences
by local bijectivity from the Library. The compatible-cover system has
exact augmented Čech complexes and local coefficient lifting. Its
dimension-shifting argument turns positive Hom exactness into vanishing
of higher derived sections at every compact object admitting a lift.
`restrictedInjectivesAcyclic_of_compactCompatibleCech` applies this to the
identity of the base, whose lift comes from the continuous action.

The proof composes the published geometry, Čech exactness, and
derived-sections results in the module categories of the target. The
compact-case argument motivating it is in Berkovich's unfinished
1995–1996 manuscript *Étale equivariant sheaves on p-adic analytic
spaces*, proof of Theorem 1.6.1(ii), printed and PDF page 13
(registered source `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`).

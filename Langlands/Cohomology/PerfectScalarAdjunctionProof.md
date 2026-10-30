# Perfect-source scalar extension Hom adjunction

This module proves the published proposition
`Langlands.Cohomology.ModuleComplex.PerfectScalarAdjunctionStatement.{u}`.
It imports the Library's `AdditiveAdjunction`, `PerfectModuleComplexHomotopy`,
and scalar-adjunction statement.

The proof computes derived Hom from a K-projective source using Mathlib's
`CochainComplex.IsKProjective.Qh_map_bijective` and the actual quotient-to-Q
comparison. The helper `kProjectiveDerivedHomEquiv` is the resulting equivalence,
and its two formulas identify the images of actual chain maps and their inverses.
The generic `derivedComplexAdjunctionUnit` applies Q to the ordinary complex unit
and then the inverse of the exact right-adjoint comparison. For an additive
adjunction F ⊣ G with G exact, when K and F(K) are both K-projective,
`kProjectiveDerivedAdjunctionHomEquiv` composes the inverse derived-Hom equivalence
at F(K), the ordinary homotopy adjunction, the derived-Hom equivalence at K,
and the exact-functor comparison for G. The `_Q_map` formula follows from the
ordinary adjunction-unit formula, functoriality of Q, and naturality of that
comparison. Every derived morphism from Q(F(K)) has a homotopy representative,
which has a chain-map representative; this proves the `_apply` formula for every
derived morphism, not only represented ones.

For a strictly perfect module complex, the existing
`ModuleComplex.isKProjective_of_isStrictlyPerfect` helper from
`PerfectModuleComplexHomotopy` uses boundedness above and termwise projectivity
to give K-projectivity by Mathlib's `isKProjective_of_projective`. Ordinary extension
of scalars preserves the upper bound and maps projectives to projectives because
its right adjoint, scalar restriction, preserves epimorphisms. Thus the extended
source is K-projective as well. The proof uses neither flatness of the ring map
nor preservation of arbitrary quasi-isomorphisms by extension. Finite generation
and the lower bound occur in the target's strict-perfection hypothesis; this
particular proof needs only projectivity and the upper bound.

`perfectScalarDerivedHomEquiv` specializes the generic equivalence to the existing
module extension/restriction adjunction. Its `_apply` formula identifies its
forward map with the specified map in the target. The target's chain unit and the
generic complex unit have the same components by definition. The final theorem
`perfectScalarAdjunction` uses bijectivity of this equivalence and the formula.
It uses the standard actual derived category instances, matching the target.

This is internal algebraic infrastructure derived from Mathlib's existing APIs;
no geometric base-change or section-lifting assertion is proved here. Generic
category and localization universes are independent. The final theorem retains
arbitrary ring universe u, including zero, and only the standard Mathlib axioms.

# Actual whole-cuspidal components under the remaining comparison

Worker 491. This internal construction supplies concrete smooth components and
their literal inclusion coproduct, then identifies their factors conditionally.
It does not prove the closed
`RationalWholeCuspidalCategoryDecompositionStatement`. Fixed-level compact-class
finiteness and the full objectwise equivalence between compact norm-kernel
restriction and proper-standard cuspidality remain intermediate obligations.
They are not new premises of the unchanged published target.

The field and representation carrier have independent universes `uF` and `uV`.
The setup is an affine group scheme locally of finite type over an arbitrary
nonarchimedean local field, with its canonical rational-point topology and
explicit local compactness and nonarchimedeanness on the point group.
`hstrata` asserts finiteness of the actual compact-class `fixedStratum` for every
compact open subgroup of `Plancherel.rationalCommonNormKernel G`. The kernel has
the induced topology and is open. No characteristic, rank, irreducibility,
admissibility, dimension or length restriction is imposed on a representation.

`rationalNormKernelCompactComponents G hstrata A` is the Bool family of the
actual range at `true` and actual kernel at `false` of
`rationalNormKernelCompactProjector G hstrata A`, each viewed as a smooth
ambient subrepresentation of `A`.
`rationalNormKernelCompactCofan` uses their literal inclusion morphisms.
`rationalNormKernelCompactCofanIsColimit` uses the proved idempotence of that
projector to obtain complementary submodules and invokes the actual
complementary-subrepresentation coproduct construction. Its descent extends
two supplied intertwiners over the unique decomposition of every ambient
vector. These constructions need no Hausdorff hypothesis.

The range has compact coefficients against every smooth functional of its
actual norm-kernel restriction: its restricted subrepresentation equals the
published total intrinsic compact-isotypic subrepresentation, and published
total compactness applies using a cofinal compact-open subgroup basis.
With Hausdorffness on the rational-point group, the projector fixes every object
with compact restriction. This uses the field's total disconnectedness,
the affine rational-point evaluation embedding, the subgroup's Borel structure
and a chosen left Haar measure. The published exhaustion theorem then says
that each compact object equals its total compact-isotypic part.

`rationalNormKernelCompactComponents_mem` places the concrete components in the
exact all/no arbitrary-subquotient compact-restriction factors. Compactness of
the range passes to every actual subquotient by smooth-functional extension
across injections and pullback across surjections. On the kernel the projector
is zero by naturality of its inclusion. Naturality transports that zero action
through an actual injective/surjective presentation of every subquotient.
If such a subquotient has compact restriction, the projector also fixes it, so
every vector is zero. This excludes exactly nontrivial compact subquotients.
The argument extracts no irreducible constituent.

The comparison section uses the actual torus morphism, cocharacter, finite
simple-root enumeration, actual standard semidirect decompositions and closed
unipotent subgroups from `RationalCuspidalCategory`.
`rationalWholeCuspidalDecompositionProperties_eq_compactRestriction` assumes,
for every actual smooth ambient representation, the equivalence of compact
norm-kernel restriction with the existing `IsCuspidal` predicate. It proves
equality of the entire Bool-indexed property families by function extensionality
and propositional extensionality. At `true`, both factors test every actual
subquotient. At `false`, both exclude the corresponding property for every
nontrivial actual subquotient. Both implication directions are used, including
under negation. This equality needs no locally-finite-type or Hausdorff premise.

The component-membership theorem rewrites by that equality. The final local
category theorem pairs these same components, their literal inclusions and
their actual colimit universal property with the already proved off-diagonal
Hom law for the unchanged rational cuspidal factors. It concludes precisely
`IsRationalWholeCuspidalCategoryDecomposition G i ν h hU` under `hstrata` and
the full objectwise comparison, not the closed universal target.

The provenance is internal assembly of the existing projector, total
compactness/exhaustion, actual subquotient and coproduct constructions.
Renard VI.3.5, printed pp.146–147 / PDF pp.152–153, motivates the route and uses
VI.2.1 in both directions to identify the factors. A.IX, printed p.268 /
PDF p.274, supplies the actual coproduct plus zero off-diagonal Hom convention.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`,
French edition dated 9 July 2026, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The separate refined inertia-product obligation, prerequisite owners and
explicit holds are unaffected.

Worker 1751's naming repair assigns explicit module-specific names to the local instances in this file. This prevents generated-name collisions when the rebuilt inertia and norm-kernel branches are imported or replayed together. Only the instance names change; their values, topology, mathematical statements and proof bodies are unchanged.

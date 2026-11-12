# Geometric specialization of the Bernstein fixed-vector reduction

Author: Worker 146. This internal unit constructs the actual standard family
needed by the fixed-vector splitting adapter and isolates its remaining
special-level comparison with the exact geometric telescope of Task 5293.
It is a conditional reduction and does not prove the unconditional target.

`standardBernsteinFamily` constructs `BernsteinStandardFamily i ν` from a
connected reductive group, its maximal split torus and a generic cocharacter
over a nonarchimedean local field. Connected reductivity, maximality and
genericity give the first three fields directly. The existing
`finite_simpleRoot` gives the finite simple-root type.
The published unconditional `GroupScheme.standardCocharacter` theorem
supplies the actual standard semidirect decompositions. The published
canonical-topology closedness theorems supply both closed subgroup fields.
Finally, `GroupScheme.standardLeviIntersection`, specialized through
`isSemidirectDecomposition_in_levi`, supplies the exact restricted
decompositions inside every standard Levi. No representation decomposition,
support comparison or fixed-vector property is included in this construction.

`StandardBernsteinFixedVectorVisibilityStatement` has the same local-field,
connected-reductive, torus, cocharacter, compact subgroup, Iwasawa, compact
open level, normality and Iwahori-decomposition hypotheses as
`FixedVectorCategoryStatements`. Its conclusion is
`bernsteinFixedVectorVisibility` for the constructed actual standard family.
The required local compactness and nonarchimedean group structure are
derived from the canonical rational-point topology. Field and carrier
universes remain independent. The statement is an explicit remaining
obligation, not an assumed global instance or an established theorem.

`standardFixedVectorSplitting_of_bernstein_inputs` applies the actual
Bernstein splitting adapter using the constructed family. Its two explicit
global premises are `BernsteinDecompositionStatement` and the visibility
statement above. Thus standard-family availability is discharged, while
the actual category decomposition and special-level irreducible comparison
remain mathematical proof obligations.

`fixedVectorCategoryStatements_of_bernstein_inputs` combines this splitting
reduction with the previously published exact global assembly. Its
conclusion is exactly `FixedVectorCategoryStatements`, under four explicit
premises: VI.9.4 subquotient generation, VI.7.5 smooth-category
Noetherianity, the actual Bernstein decomposition, and the new special-level
comparison. None of these four propositions is proved by this unit.

The provenance is internal: the family construction composes published
structural theorems on the actual standard subgroups, and the remaining
proofs specialize the fixed-vector adapters without changing their objects
or the published target and its imports.

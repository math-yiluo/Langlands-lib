# Actual Picard pullback and unit cohomology for arbitrary morphisms

This internal construction compares the existing actual Picard pullback with
pullback of Ext-defined cohomology of the actual structure-sheaf units.

For any morphism `i : Y ⟶ X` of universe-u schemes and every natural degree n,
`UnitH1MorphismPullback.cohomologyMap i n` is
`AbelianSheafCohomologyPullback.pushforwardMap i.base (unitsReduction i) n`.
Here `unitsReduction i` is induced by the actual structure-sheaf morphism.
There is no immersion, flatness or nilpotence assumption on this map.

On a finite full open cover U of X, `classOfCocycle_pullback` says that the
actual class of `UnitCechPullback.mapCocycles i U z` equals this map applied
to `classOfCocycle U hU z`. Its proof specializes the general
`AbelianSheafH1Pullback.comparisonHom_pullback` to the actual unit sheaves and
unfolds the existing cocycle-class and cohomology-map definitions.

If X and Y are compact, `Group.unitCohomologyClass_pullback_morphism` says
that the actual Picard class `Group.pullback i x` has unit-cohomology class
`cohomologyMap i 1 (Group.unitCohomologyClass x)`. The proof chooses the
existing line-bundle representative and its finite unit presentation,
identifies its glued bundle with the representative, applies the existing
cocycle gluing pullback isomorphism, and then applies the finite-cover result.
`Group.unitCohomologyAddEquiv_pullback_morphism` restates the same equality
using the published additive classifier. Compactness is used for those
finite presentations and classifiers.

The construction and proofs are internal consequences of the published unit
cocycle, line-bundle, Picard classifier and arbitrary sheaf-pullback APIs.
This extends the nilpotent-immersion interface of `UnitH1Pullback` to arbitrary
scheme morphisms using the general Ext-defined map. It does not identify
that map with the older homeomorphic cohomology equivalence in every degree,
and does not prove the square-zero obstruction naturality target.

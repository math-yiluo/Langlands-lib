# Pointed class restriction on spectra of noetherian domains

Worker 800. This module applies the Library's connected-component and
geometric-point evaluation isomorphisms to the actual tests used by
`CMLevelDiscreteValuativeExistenceStatement`. All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

For a noetherian domain `B` and a structure morphism `β : Spec B ⟶ Spec F`,
`connectedSpecTest B β` is `Over.mk β` in the connected admissible category.
The spectrum is connected and locally noetherian. The Library's relative dual
existence and geometry theorems give connected admissibility.
`connectedSpecTestMap φ β` is the morphism of these tests induced by
`Spec φ` for a ring homomorphism `φ : B' →+* B` of noetherian domains.

At a small level `U`, `specTest_map_surjective_iff_pointed` identifies
surjectivity of the class restriction along `specTestMap φ β` with
surjectivity of `geometricFamilyPointPullback` at any geometric point `a`
of `Spec B`. The point used on `Spec B'` is `a.comp (Spec φ)`.
For a discrete valuation ring `V` with fraction field `K`, one takes
`φ = algebraMap V K`.

The proof first compares the componentwise presheaf on both spectra with
the unpointed class tower. It picks a component of `Spec B` and uses its
image component in `Spec B'`. Each inclusion is an isomorphism because the
spectrum is connected. The component restriction square commutes by the
factorization through the component inclusions. Inverting those inclusions
and applying contravariant pullback gives the corresponding square on the
unpointed class towers. Next, the evaluation isomorphisms at the two geometric
points give the square comparing the unpointed and pointed restrictions.
Bijectivity of the vertical maps transports surjectivity in each square.
The reduction leaves the existence of extensions of pointed classes open.

## Provenance

Derived from the Library's `admissibleCMBase_iff_dualGeometry`,
`relativeDualSchemeExistence`, `relativeDualSchemeGeometry`,
`disconnectedClassTowerConnectedIso`, and `unpointedClassTowerPullback_evaluation`.
The argument specializes these declarations to the spectra in `specTestMap`.

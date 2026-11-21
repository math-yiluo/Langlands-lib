# Normal Laurent models of split tori

Author: Worker 946.

`Langlands.GroupScheme.IsSplitTorus.normalAffineModel` chooses a finite index type `I` and an actual isomorphism from the diagonalizable group of the lattice `I → ℤ` to a supplied split torus over `Spec R`. It records that the coordinate algebra `R[ℤ^I]` is an integrally closed domain. The base ring `R` is any integrally closed domain in the same universe as the torus, including a valuation domain of arbitrary rank. No Noetherian or discrete valuation hypothesis is imposed.

The group algebra calculation is independent of schemes and works in separate universes for `R` and `I`. In one variable, the published Mathlib instance for adjoining a polynomial variable preserves integral closedness, and localization at the powers of the nonzero variable gives the Laurent polynomial ring. Induction on finite index types uses the existing `IntLatticeAlgebra.optionEquiv` to add one Laurent variable. The empty lattice gives `R`, and transport along a bijection of index types uses `IntLatticeAlgebra.congrEquiv`.

The actual affine scheme of the model is `Spec R[ℤ^I]`, via `SplitTorusNormalAffineModel.specIso`. The spectrum is integral because its coordinate algebra is a domain. The isomorphism transports integrality and identifies each actual stalk with the corresponding stalk of that spectrum. Those stalks are integrally closed domains by `spec_hasNormalStalks`, which uses the localizations at prime ideals. Thus `isIntegral` and `hasNormalStalks` apply to the supplied torus itself. With its integrality in scope, `geometricallyUnibranch` yields the Library's stalkwise geometric-unibranch condition, using the fact that the normalization of a local integrally closed domain is the same local domain.

This is an internal composition of the published finite lattice, polynomial normality, localization and actual-stalk interfaces. The normal-affine model supplies integrality and geometric unibranchness for the generic-section argument in Task 7782; it does not by itself extend any section or prove the conjugacy quotient affine.

# Construction of algebraic SU3 rank-one coordinates at multipliable roots

Module `Langlands.Geometry.Building.AlgebraicSU3RootCoordinatesConstruction`, namespaces
`Langlands.GroupScheme.SimpleRootFiber` and `Langlands.Geometry.Building`.

Worker 163, for Task 6836 (8c04a3ed-3fa6-4680-a59f-856738cb578b), SU3 half.

## Purpose

`AlgebraicRankOneCoordinatesExistenceStatement`, the target of Task 6836, has two clauses
for an indivisible relative root `b`. The SL2 clause covers the case where `2 • b` is not a
relative root. The SU3 clause, the published `AlgebraicSU3RootCoordinatesExistenceStatement`,
covers the case where it is. The published module `AlgebraicSL2RootCoordinatesConstruction`
reduces the target to `SplitRelativeRootGroupProductStatement` and the SU3 clause. The
published proof `splitRelativeRootGroupProduct` (module
`SplitRelativeRootGroupProductProof`) settles the first of these.

This module proves the SU3 clause from two explicit hypotheses:
`SplitRelativeRootGroupProductStatement` and the published
`AdjacentSimpleRootSpecialLinearStatement` (an `SL₃` homomorphism for each pair of adjacent
simple roots of a split pinning). Its final theorem therefore reduces the whole target to
`AdjacentSimpleRootSpecialLinearStatement`. Neither proposition is assumed outside the
hypotheses of the theorems below.

The construction is the standard one for quasi-split `SU₃` root groups: Borel–Tits,
*Groupes réductifs*, §4, and Kaletha–Prasad, *Bruhat–Tits theory*, Prop. 7.1.1 (printed
p. 239) and its proof. The Lean development is internal.

## The record (namespace `SimpleRootFiber`)

The setting is that of `SimpleRootFiberPinning`. It has the fiber pinning `Dₚ` for a generic
`ν` making `a` simple, `K / k` finite Galois, `j` closed and `G` smooth. In addition,
`h2a : 2 • a ∈ relativeRoots`, `hR` a relative root system, `[Fintype Oₐ]`, and the
hypotheses `hProd` and `hAdj`. Write `L₀` for the fiber field, `E₀` for the pair field,
`c₀ = SU3Root.fieldInvolution E₀ L₀`, `Dπ` for `fiberPartnerData` and `τ` for
`fiberEmbedding`. The arguments of `SplitPinning.unitaryRho` (module
`PartnerOrbitSpecialUnitary`) are the fields of `Dₚ` and the partner and embedding lemmas.
These are `fiberPinning_pairing_action`, `fiberSet_galois`, `partner_action`,
`fiberEmbedding_galois`, and `fiberEmbedding_partner` (`c₀.bar` is the conjugation of `L₀`
over `E₀` by definition).

- `fiberUnitaryRho` (def): `SplitPinning.unitaryRho : SU₃(L₀/E₀) →* G(k)` for these data.
- `fiberPositiveUnitary` (def):
  `RootUnitaryCoordinatesOn (groupHom f ≫ j) j (groupHom f) a E₀ L₀`.
  - `equiv`: `SplitPinning.upperUnitaryEquiv` (module `PartnerOrbitUnitaryCoordinates`). Its
    hypotheses are `fiber_hmem_upper`, `fiber_hprod_upper`, `fiber_huniq_upper` (module
    `SimpleRootFiberUnitary`), `exists_eq_fiberEmbedding` and `basePoint_mem`.
  - `double`: `SplitPinning.mem_double_iff_upper` with `fiber_hmem2_upper`,
    `fiber_hprod2_upper`.
  - `character`: `rootOrbitCharacter k K j β₀`, the root of the base point over `L₀`.
    `restriction` is `characterRestrict_rootOrbitCharacter`.
  - `conjugation`: `SplitPinning.conj_unitaryRho_upper` with
    `fiberEmbedding_rootOrbitCharacter`.
- `fiberNegativeUnitary` (def): the same for `-a`, with `lowerUnitaryEquiv`,
  `mem_double_iff_lower` and the lower hypotheses. The character is `-partnerCharacter`.
  `restriction` comes from `AffineCharacterTowerDescent.characterRestrict_fixedDescend`,
  since the partner root also restricts to `a`. `conjugation` comes from
  `SplitPinning.conj_unitaryRho_lower` with `fiberEmbedding_neg_partnerCharacter`.
- `fiberSU3Coordinates` (def):
  `Geometry.Building.AlgebraicSU3RootCoordinates (groupHom f ≫ j) j (groupHom f) a`.
  - `base := E₀`, `extension := L₀`. The instance fields are found by instance search, from
    `SimpleRootFiberPartners` (`pairAlgebra`, the scalar tower, the quadratic and separable
    instances) and from the intermediate-field instances.
  - `positive`, `negative`: the two records above.
  - `rho`: `fiberUnitaryRho`. `rho_upper` and `rho_lower` hold by `rfl`, since the
    coordinate equivalences are `rho` on the upper and lower parameters
    (`upperUnitaryEquiv_apply`, `lowerUnitaryEquiv_apply`).
  - `coroot`: the coroot `fiberCoroot : R_{L₀/k} 𝔾_m ⟶ T` of module
    `SimpleRootFiberCoroot`, for the fiber field.
  - `coroot_points`: after scalar extension to `K`, both sides are the image of
    `∏ b ∈ Oₐ, b^∨(τ_b t)`. For `rho`, this is
    `SplitPinning.rationalExtend_unitaryRho_diagonal` (module `PartnerOrbitRootProducts`).
    For the coroot, it is `fiberCoroot_extendedUnitPoint`. Then
    `rationalExtend_injective_of_isAffineHom` applies.
- `fiberSU3Coordinates_weyl`: the image of the antidiagonal Weyl element
  `SU3Root.weylElement` lies in `normalizerPoints (groupHom f ≫ j)`. The proof combines
  `SplitPinning.unitaryRho_weylElement_mem` (module `PartnerOrbitRootProducts`) with the
  Library lemma `IsMaximalSplitTorus.mem_normalizerPoints_of_mem_normalizerPoints`.

## Final theorems (namespace `Geometry.Building`)

- `exists_algebraicSU3RootCoordinates_of_product_of_adjacent`: under the binders of
  `AlgebraicSU3RootCoordinatesExistenceStatement`, with `hProd` and `hAdj`, every
  indivisible relative root `b` with `2 • b` a relative root has a record
  `C : AlgebraicSU3RootCoordinates i j s b` whose Weyl element `C.rho J` normalizes `i`. The
  proof follows `exists_algebraicSL2RootCoordinates_of_product`. It chooses a finite Galois
  splitting field of `Z` (`torusFiniteGaloisSplitting`) and a root datum over it
  (`rootDatumExistence`). It uses the relative root system (`relativeRootSystem`) and a
  generic cocharacter making `b` simple
  (`RelativeRoot.exists_isGenericCocharacter_mem_simpleRelativeRoots`), then applies
  `fiberSU3Coordinates` and `fiberSU3Coordinates_weyl`.
- `algebraicSU3RootCoordinatesExistence_of_product_of_adjacent`:
  `SplitRelativeRootGroupProductStatement → AdjacentSimpleRootSpecialLinearStatement →
  AlgebraicSU3RootCoordinatesExistenceStatement`.
- `algebraicRankOneCoordinatesExistence_of_adjacent`:
  `AdjacentSimpleRootSpecialLinearStatement → AlgebraicRankOneCoordinatesExistenceStatement`.
  It combines `algebraicRankOneCoordinatesExistence_of_product_of_su3` (module
  `AlgebraicSL2RootCoordinatesConstruction`) with `splitRelativeRootGroupProduct`.
  `#print axioms` gives `propext`, `Classical.choice`, `Quot.sound`.

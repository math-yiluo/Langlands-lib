# Proof of `AdelicParabolicModulusStatement`

Author: Worker 759.

This module proves the unchanged published proposition
`Langlands.Global.AdelicGroupPoints.AdelicParabolicModulusStatement` (module
`Langlands.Global.AdelicParabolicModulusStatement`) at every universe `u`:

```
theorem Langlands.Global.AdelicGroupPoints.adelicParabolicModulus :
    AdelicParabolicModulusStatement.{u}
```

The theorem takes no hypotheses. It keeps every quantifier and premise of the statement: an
arbitrary number field `F : Type u`, an arbitrary connected reductive `G` over `F`, an
arbitrary cocharacter `χ`, arbitrary representing group schemes `iP : P ⟶ G` of `P(χ)` and
`iU : U ⟶ G` of `U(χ)`, and arbitrary finite coordinates `c` on `Lie U`. The two conjuncts
concern the published `parabolicModulus F hP hU`. Its value at `p` is the Haar modulus of
`u ↦ p u p⁻¹` on the closed image of `U(𝔸_F)` in `G(𝔸_F)`. The proof shows:

1. `parabolicModulus F hP hU p = characterNorm F P (Dynamic.adjointDeterminantCharacter hP hU c).toMul p`;
2. `Measure.modularCharacter p = parabolicModulus F hP hU p`, for Mathlib's modular character of
   the locally compact group `P(𝔸_F)`.

For `p` in the Levi factor, these are the formulas `δ_P(m) = m^{2ρ_P}` of Mœglin–Waldspurger,
I.1.13 (`moeglin-waldspurger-1995-spectral-decomposition`, printed p. 18), and of Getz–Hahn,
(8.1) (`getz-hahn-2024-automorphic-representations`, printed p. 213). The proof below does not
follow either text. It uses no archimedean or non-archimedean analysis beyond the published
all-place formula for modular characters of smooth affine groups.

## Notation and choices

The statement supplies no representative of the Levi factor. The proof takes the published
representative `Z = Dynamic.Affine.centralizerScheme χ`, with
`iZ = Dynamic.Affine.centralizerHom χ` and `Dynamic.Affine.isRepresentedBy_centralizerHom χ`.
The general lemmas below hold for any representative `iZ` of `Z(χ)`.

Write `Δ` for `Measure.modularCharacter` on `P(𝔸_F)` and `δ` for `parabolicModulus F hP hU`.
Write `N₁` for `characterNorm F P (Lie.adjointDeterminantCharacter P).toMul`, the idele norm of
`det(Ad | Lie P)`, and `N₂` for the idele norm of `det(Ad | Lie U)` in the coordinates `c`.

## Auxiliary results (section `Compact`)

- `characterNorm_eq_one_of_compactSpace`: if `RationalQuotient F H = H(F) \ H(𝔸_F)` is compact,
  the idele norm of every algebraic character `χ` of `H` is identically `1`. By the product
  formula (`characterNorm_rational`) the continuous character `characterNorm F H χ` is
  invariant under left multiplication by `H(F)`. It descends to a continuous map on the compact
  quotient (`LeftCosetSpace.lift`, `LeftCosetSpace.continuous_lift`). Its range is therefore a
  compact subgroup of `ℝ≥0ˣ`, and the published `continuousMonoidHom_eq_one_on_compactSubgroup`
  shows that such a subgroup is trivial.
- `modularCharacter_eq_one_of_compactSpace`: for smooth affine `H` of finite type with compact
  rational quotient, `Δ_{H(𝔸_F)} = 1`. The published `modularCharacter_eq_characterNorm_of_local`,
  applied to the published all-place formula `PlaceGroupPoints.localModularCharacterAdjointDeterminant`,
  gives `Δ_{H(𝔸_F)} = |det Ad_H|_𝔸`. This norm is `1` by the previous item.
- `modularCharacter_eq_one_of_isConnectedReductive`: for connected reductive `H`,
  `Δ_{H(𝔸_F)} = 1`. Combine the same adelic formula with
  `Lie.connectedReductiveAdjointDeterminant` (`det Ad_H = 0`), through the published
  `modularCharacter_eq_one_of_adjointDeterminant_eq_zero`.

## Conjunct 2: `modularCharacter_eq_parabolicModulus`

Let `PG`, `ZG` and `UG` be the images of `P(𝔸_F)`, `Z(𝔸_F)` and `U(𝔸_F)` in `G(𝔸_F)`. The three
inclusions are closed subgroups (`Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_*`). So
the images are closed (`isClosed_range_map_of_isClosedSubgroup`, `isClosed_range_map_unipotent`)
and locally compact. The adelic point maps are closed embeddings (`isClosedEmbedding_map`), and
`rangeEquiv` identifies each point group with its image as topological groups.

1. *Semidirect decomposition.* `ZG ≤ PG` and `UG ≤ PG` follow from
   `centralizerToParabolic_comp` and `unipotentToParabolic_comp`. The map
   `f : PG → G(𝔸_F)`, `f = map iZ ∘ map (limitGroupHom hP hZ) ∘ (rangeEquiv iP)⁻¹`, is a
   continuous homomorphism with values in `ZG`. It is the identity on `ZG`, by
   `centralizerToParabolic_comp_limitGroupHom`. Its kernel is `UG`: since `map iZ` is
   injective, `f q = 1` means the `𝔸_F`-point of `P` is killed by `limitGroupHom`, and
   `Dynamic.limitGroupHom_eq_one_iff` (module `ParabolicLieDecomposition`) identifies this
   with membership in `U(χ)`, that is in `UG`. The published
   `Aubert.General.IsSemidirectDecomposition.of_retraction` and
   `continuous_of_retraction_projection` (module `Langlands.Global.AdelicSiegelMeasureReduction`)
   give `IsSemidirectDecomposition PG ZG UG` with continuous Levi projection.
2. *Unimodular Levi factor.* `Z` is connected reductive by the published
   `dynamicCentralizerReductive`. Hence `Δ_{Z(𝔸_F)} = 1`, and `Δ_{ZG} = 1` by the published
   invariance of modular characters under topological group isomorphisms
   (`Aubert.General.modularCharacter_continuousMulEquiv`).
3. *Unimodular radical.* `U` is smooth (`dynamicSmooth`), connected (`dynamicConnected`) and
   unipotent (`dynamicUnipotentUnipotence`). So `U(F) \ U(𝔸_F)` is compact by the published
   `unipotentRationalQuotientCompact`, and `Δ_{U(𝔸_F)} = 1`. For `v ∈ UG`, the Haar modulus of
   conjugation by `v` on `UG` is `Δ_{UG}(v)` (`Aubert.General.modularCharacter_eq_innerConjugation`),
   hence `1`.
4. *Conclusion.* The published
   `IsSemidirectDecomposition.modularCharacter_eq_restrictCharacter_of_unimodular` (module
   `Langlands.Representation.Aubert.General.SemidirectModularCharacter`) gives
   `Δ_{PG}(q) = ` Haar modulus of `u ↦ q u q⁻¹` on `UG`, for every `q ∈ PG`. For `q` the image
   of `p`, the right side is by definition `parabolicModulus F hP hU p`
   (`HaarModulus.closedNormalizerCharacter`). Transporting `Δ` along `rangeEquiv iP` gives
   conjunct 2.

All modular characters and Haar moduli use the orientation `x ↦ g x g⁻¹`, as in the cited
published lemmas; no inverse is inserted.

## Conjunct 1: `parabolicModulus_eq_characterNorm`

1. By conjunct 2, `δ(p) = Δ(p)`. Since `P` is smooth (`dynamicSmooth`), the published adelic
   formula (`modularCharacter_eq_characterNorm_of_local` with
   `localModularCharacterAdjointDeterminant`) gives `Δ(p) = N₁(p)`. It remains to show
   `N₁(p) = N₂(p)`.
2. Write `p = (v ≫ U ⟶ P) * (m ≫ Z ⟶ P)` with `v ∈ U(𝔸_F)` and `m ∈ Z(𝔸_F)`
   (`Dynamic.exists_eq_unipotent_mul_centralizer`). Both norms are multiplicative.
3. On the unipotent factor both norms are `1`. By the published `characterNorm_comp`, each is
   the idele norm of a character of `U`, and this norm is trivial by
   `characterNorm_eq_one_of_compactSpace`, since `U(F) \ U(𝔸_F)` is compact.
4. On the Levi factor, `characterNorm_comp` reduces the claim to equality of the restrictions to
   `Z` of the two characters of `P`. The helper theorem
   `Dynamic.characterRestrict_adjointDeterminantCharacter_parabolic` gives
   `restrict_Z det(Ad | Lie P) = det(Z on Lie U)_c + det(Ad | Lie Z)`. The last term is `0` by
   `Lie.connectedReductiveAdjointDeterminant`. The published
   `Dynamic.adjointDeterminantCentralizerRestriction` identifies `det(Z on Lie U)_c` with
   `restrict_Z (Dynamic.adjointDeterminantCharacter hP hU c)`.

## Final assembly

`adelicParabolicModulus` introduces the statement's data and installs the same instances as the
statement (`hG.isAffineHom`, `hG.smooth`, `isAffine_parabolic`, `locallyOfFiniteType_parabolic`,
`isAffine_unipotent`). It then applies the two theorems above with the published centralizer
representative. The proof was checked with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`. It depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Published inputs

- `PlaceGroupPoints.localModularCharacterAdjointDeterminant` (`Langlands.Global.LocalModularCharacterAdjointDeterminantProof`)
- `modularCharacter_eq_characterNorm_of_local` (`Langlands.Global.AdelicLocalModularComparison`)
- `modularCharacter_eq_one_of_adjointDeterminant_eq_zero` (`Langlands.Global.AdelicModularCharacterAdjointDeterminantStatement`)
- `unipotentRationalQuotientCompact` (`Langlands.Global.UnipotentRationalQuotientCompactProof`)
- `characterNorm_rational`, `characterNorm_comp`, `continuousMonoidHom_eq_one_on_compactSubgroup` (`Langlands.Global.AdelicGroupNormOne`, `Langlands.Global.AdelicGroupNormOneFunctorial`)
- `parabolicModulus`, `rangeEquiv`, `isClosed_range_map_of_isClosedSubgroup`, `isClosed_range_map_unipotent`, `isAffine_*`, `locallyOfFiniteType_*` (`Langlands.Global.AdelicParabolicModulus`); `isClosedEmbedding_map` (`Langlands.Global.AdelicPositiveImageClosed`)
- `IsSemidirectDecomposition.of_retraction`, `continuous_of_retraction_projection` (`Langlands.Global.AdelicSiegelMeasureReduction`)
- `IsSemidirectDecomposition.modularCharacter_eq_restrictCharacter_of_unimodular`, `modularCharacter_eq_innerConjugation` (`Langlands.Representation.Aubert.General.SemidirectModularCharacter`)
- `modularCharacter_continuousMulEquiv` (`Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction`)
- `dynamicSmooth`, `dynamicConnected`, `dynamicUnipotentUnipotence`, `dynamicCentralizerReductive`, `Lie.connectedReductiveAdjointDeterminant`, `Dynamic.adjointDeterminantCentralizerRestriction`
- `Dynamic.Affine.centralizerScheme`, `centralizerHom`, `isRepresentedBy_centralizerHom`, `Dynamic.limitGroupHom`, `centralizerToParabolic`, `unipotentToParabolic`
- the helper module `Langlands.GroupScheme.Dynamic.ParabolicLieDecomposition`, submitted with this proof.

# Opposite adjoint determinants on a dynamic Levi, from structural inputs

Author: Worker 1415.

This module proves the published proposition
`Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityStatement`
under three published hypotheses that are still unproved. The main result is

```
theorem Langlands.GroupScheme.leviAdjointDeterminantReciprocity_of_structure
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u})
    (hRed : DynamicCentralizerReductiveStatement.{u}) :
    Dynamic.LeviAdjointDeterminantReciprocityStatement.{u}
```

The three hypotheses are explicit arguments of the theorem. Nothing in the module asserts
them, and the module adds no axiom. It also introduces the definition
`positiveWeightCharacter` and proves the supporting lemmas listed below.

## The definition `positiveWeightCharacter`

Let `k` be a field, `G` a group scheme over `Spec k` with `[IsAffineHom G.X.hom]`,
`i : T.toGrp ⟶ G` a homomorphism from a commutative group scheme `T`, and
`ζ : cocharacterLattice T`. Then

```
positiveWeightCharacter i ζ =
  ∑ᶠ α : characterLattice T,
    (if 0 < latticePairing T α ζ then finrank k (weightSpace i α) else 0) •
      (rationalCharacters.equivCharacterLattice T).symm α
```

is an element of the additive group `rationalCharacters T.toGrp`. Here
`weightSpace i α` is the Library's weight space of `α` for the adjoint action of `T`
through `i` on the actual Lie algebra `Lie(G) = ker(G(k[ε]) → G(k))`. The pairing
`latticePairing T α ζ` is the integer `⟨α, ζ⟩`, and
`rationalCharacters.equivCharacterLattice T` identifies the character lattice with
the rational characters of `T`. So the definition is the character

`∑_{⟨α, ζ⟩ > 0} (dim 𝔤_α) · α`,

the weights of `T` on `Lie(G)` that are positive on `ζ`, each counted with the
dimension of its weight space. The sum is a `finsum`. In the situations used below
the support is finite: a nonzero summand needs `weightSpace i α ≠ ⊥`, and for a
split torus acting on a finite-dimensional Lie algebra only finitely many weight
spaces are nonzero. In general the definition follows the `finsum` convention, which
gives `0` when the support is infinite.

When `T` is a split torus in the centralizer of `ζ`, the lemma
`characterRestrict_centralizerAdjointDeterminant` below shows that this character is
the restriction to `T` of the determinant character of the adjoint action of the
Levi `Z(ζ)` on `Lie U(ζ)`.

## Supporting lemmas

### Symmetry of root multiplicities

- `finrank_weightSpace_weylAction`: for a monomorphism `i` and a rational point
  `n : normalizerPoints i`,
  `finrank k (weightSpace i (weylAction i n χ)) = finrank k (weightSpace i χ)`.
  *Proof.* The Library's `map_weightSpace_weylAction` states that
  `basePointAdjoint n` maps `weightSpace i χ` onto
  `weightSpace i (weylAction i n χ)`. The linear map `basePointAdjoint n` is
  injective, because `basePointAdjoint_inv_mul` says that composing it with
  `basePointAdjoint n⁻¹` gives the identity. An injective linear map preserves the
  dimension of a submodule (`Submodule.equivMapOfInjective`).
- `RelativeRootReflectionData.finrank_weightSpace_neg`: given reflection data
  `D : RelativeRootReflectionData i`,
  `finrank k (weightSpace i (-χ)) = finrank k (weightSpace i χ)` for every `χ`.
  *Proof.* If `χ` is a relative root, `D.action` and `D.pair_self` give
  `weylAction i (D.representative χ) χ = χ - 2 • χ = -χ`, and the previous lemma
  applies. If `-χ` is a relative root, the same argument applies to `-χ`. If `χ = 0`
  the claim is trivial. Otherwise neither `χ` nor `-χ` is a relative root. Since
  `relativeRoots i` consists of the nonzero `α` with `weightSpace i α ≠ ⊥`
  (`mem_relativeRoots`), both weight spaces are `⊥` and both dimensions are `0`.
- `RelativeRootReflectionData.positiveWeightCharacter_neg`: with reflection data,
  `positiveWeightCharacter i (-ζ) = -positiveWeightCharacter i ζ`.
  *Proof.* Reindex the `finsum` for `-ζ` by `α ↦ -α`
  (`finsum_comp_equiv (Equiv.neg _)`). The summand at `-α` has pairing
  `⟨-α, -ζ⟩ = ⟨α, ζ⟩`, character `-α`, and multiplicity `dim 𝔤_{-α} = dim 𝔤_α` by the
  previous lemma. So it is the negative of the summand at `α` for `ζ`, and
  `finsum_neg_distrib` concludes.

### Torus weights on the Lie algebra of a dynamic unipotent subgroup

In this section `G` also satisfies `[LocallyOfFiniteType G.X.hom]` and
`hT : IsSplitTorus T.toGrp`. `iZ : Z ⟶ G` represents `Dynamic.centralizer χ` and
`iU : U ⟶ G` represents `Dynamic.unipotent χ`, where
`χ = CommGroupScheme.groupHom ζ ≫ i`. Also `j : T.toGrp ⟶ Z` satisfies
`hj : j ≫ iZ = i`.

- `centralizerAdjointAction_restrict_isEquivariant`: restricted along `j`, the action
  of `Z` on `U` (`Dynamic.centralizerAdjointAction hZ hU`) is compatible, via `iU`,
  with conjugation by `T` on `G` along `i`. This follows from
  `Dynamic.centralizerAdjointAction_act_comp` and `hj`.
- `range_targetMapLinear_unipotent`: the image of `Lie U` in `Lie G` is
  `⨆_{⟨α, ζ⟩ > 0} weightSpace i α`. *Proof.* The image is the tangent submodule of the
  subgroup functor represented by `iU` (`RelativeRoot.tangentSubmodule_range`), which
  is `Dynamic.unipotent χ` by `hU`. The Library theorem `dynamicLie` (CGP Proposition
  2.1.8(1)) identifies its tangent vectors with `⨆_{n ≥ 1}` of the weight spaces of
  `𝔾_m` acting through `χ`. `iSup_nat_succ_weightSpace_cocharacter` rewrites this sum
  as the sum of the weight spaces of the characters of `T` that are positive on `ζ`.
- `map_lieWeightSpace_centralizerAdjointAction`: the weight space of `α` for the
  action of `T` (through `j`) on `Lie U` maps under `Lie U → Lie G` to
  `weightSpace i α` if `⟨α, ζ⟩ > 0` and to `⊥` otherwise. *Proof.* By the
  equivariance lemma and `IsEquivariant.map_actionWeightSpace_eq_inf_range`, the image
  is `weightSpace i α ⊓ range`, and the range is computed by the previous lemma. If
  `⟨α, ζ⟩ > 0`, the intersection is `weightSpace i α`. Otherwise the weight space is
  disjoint from the sum of the other weight spaces (`weightSpace_disjoint_iSup`, from
  the direct-sum decomposition of `Lie G` under the split torus `T`). This lemma
  carries `set_option maxHeartbeats 400000`. Matching the two lattice structures on
  the submodules (over `k` and over `CommRingCat.of k`) exceeds the default limit.
- `finrank_lieWeightSpace_centralizerAdjointAction`: the dimension of that weight
  space is `dim 𝔤_α` if `⟨α, ζ⟩ > 0` and `0` otherwise, because `Lie U → Lie G` is
  injective (`Lie.targetMapLinear_injective`).
- `characterRestrict_centralizerAdjointDeterminant`: for finite Lie coordinates `c`
  of `U` (and `[IsAffine Z.X.left]`),
  `characterRestrict j ((centralizerAdjointAction hZ hU).determinantCharacter c) =
  positiveWeightCharacter i ζ`. *Proof.* The proved Library theorem
  `AutomorphicAction.determinantCharacter_restrict_eq_rootSum` writes the restricted
  determinant as the sum, over the weights of `T` on `Lie U`, of each weight times the
  dimension of its weight space. The previous lemma identifies the dimensions. Zero
  weights and weights with trivial weight space contribute `0` on both sides.

## Proof of `leviAdjointDeterminantReciprocity_of_structure`

Fix the data of `LeviAdjointDeterminantReciprocityStatement`: a field `k`, a
connected reductive `G`, a maximal split torus `i : T ⟶ G`, a cocharacter `ζ`, the
common centralizer model `iZ` (premises `hZ`, `hZ'`), the unipotent models `iU`,
`iV`, and finite coordinates `c`, `c'`.

1. `iZ` is a closed subgroup
   (`Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_centralizer`). By `hRed`
   (`DynamicCentralizerReductiveStatement`), `Z` is connected reductive.
2. `T` centralizes `χ` (`range_le_centralizer_groupHom_comp`), so
   `IsMaximalSplitTorus.exists_lift` gives `j : T ⟶ Z` with `j ≫ iZ = i`.
3. `hRefl` (`RelativeRootReflectionExistenceStatement`) gives reflection data `D`
   for the relative roots of `i`. Its kernel-centralizing property is not used.
4. Apply `characterRestrict_centralizerAdjointDeterminant` to `ζ` with `(hZ, hU, c)`
   and to `-ζ` with `(hZ', hV, c')`. The same `j` works for both because `Z` is a
   common model. With `D.positiveWeightCharacter_neg`, the restriction along `j` of
   the sum of the two determinant characters is
   `positiveWeightCharacter i ζ - positiveWeightCharacter i ζ = 0`.
5. Suppose the sum `ψ` were nonzero. `hCST` (`CentralSplitTorusCharacterStatement`)
   applied to the connected reductive `Z` gives a central split torus `a : A ⟶ Z`
   with `characterRestrict a ψ ≠ 0`. `j ≫ iZ = i` is a maximal split torus of `G`, so
   `IsCentralSplitTorus.exists_factor_of_isMaximalSplitTorus` factors
   `a = g ≫ j`. Then `characterRestrict a ψ = characterRestrict g (characterRestrict
   j ψ) = 0` by `characterRestrict_comp` and step 4, a contradiction.

## Provenance and relation to the literature

Provenance: derived. The argument is the classical one sketched in the Markdown of
`LeviAdjointDeterminantReciprocityStatement`, carried out over `k` with the maximal
split torus `T` instead of a maximal torus over an algebraic closure. It uses relative
root multiplicities, made symmetric by integral reflections, in place of
one-dimensional absolute root spaces.

- Conrad, Gabber and Prasad, *Pseudo-reductive groups*, second edition, source
  `conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
  `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`, Proposition
  2.1.8(1), printed p. 53 (PDF p. 79): "We have Lie(Z_G(λ)) = g_0, Lie(U_G(±λ)) =
  g_±, and Lie(P_G(λ)) = g_0 ⊕ g_+ inside g." The Library theorem `dynamicLie`
  formalizes this. It is the source of `range_targetMapLinear_unipotent`.
- Renard, *Représentations des groupes réductifs p-adiques*, source
  `renard-2026-representations-groupes-reductifs-padiques`, SHA256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, Section V.5.4,
  printed pp. 126–127 (PDF pp. 132–133). Renard computes the modular characters of
  `N` and `N̄` on the split component from the roots of `A` in `Lie N` and their
  multiplicities, and obtains `δ_N(m)⁻¹ = δ_N̄(m)`. The character
  `positiveWeightCharacter i ζ` is the algebraic counterpart: the weights of `T` in
  `Lie U(ζ)` counted with multiplicity. `positiveWeightCharacter_neg` is the
  algebraic form of the fact that the opposite radical has the opposite roots with
  the same multiplicities.

The three hypotheses are published proposition definitions with open proof tasks:
`RelativeRootReflectionExistenceStatement` (task 5c031416),
`CentralSplitTorusCharacterStatement` (task 4f432abe) and
`DynamicCentralizerReductiveStatement` (task ccd6e0f7). Once they are proved, applying
this theorem to their proofs proves `LeviAdjointDeterminantReciprocityStatement`
unconditionally.

# The Tits obstruction of a base change in terms of the original representation

This module computes the Tits obstruction of the base change `G_E`, for an
intermediate field `k ⊆ E ⊆ K`, from a representation of `G_K`. The base
change is published as `GaloisPinningData.baseChange`
(`Reductive/GaloisPinningBaseChange`). It carries the weight transport
`weightTransport E : X^*(T_K) ≃ X^*((T_E)_K)` and the tower isomorphism
`groupTowerIso k E K G : G_K ≅ (G_E)_K`. This is the field-extension half of
this development's proof of the integral-weight transfer law of
`Reductive/TitsTransfer`. The term computed here is `α_E(λ_E)`, the Tits
obstruction of the base change `G_E` at the transported weight. That law is
derived from, but is not, Tits's Proposition 5.1 (*Représentations linéaires
irréductibles d'un groupe réductif sur un corps quelconque*, J. reine angew.
Math. 247 (1971), printed p. 207 / PDF p. 12). Tits's source term there is
`β_{G,k₁}(c₁)`, for a central character `c₁` and the fixed field `k₁` of its
stabilizer. The comparison is internal to this development.

## Galois twists and the tower

- `StarActionFiniteStage.descentPoint_groupTowerIsoOf_inv`: the inverse group
  tower isomorphism intertwines the changes of test-scheme structure along an
  endomorphism `a` of the top base over the middle one. This is the group
  version of the published `descentPoint_towerIsoOf_inv` for commutative
  group schemes, with the same proof (`descentPoint_comp_of_fst`).
- `StarActionFiniteStage.groupTowerIso_eq`: `groupTowerIso` is
  `groupTowerIsoOf` for the composite base map, by definition.
- `MatrixRepresentation.transport_restrict_groupTowerIsoOf_inv`: restriction
  along the inverse tower isomorphism commutes with transport along such an
  `a`. Compare point matrices (`pointMatrix_transport`,
  `pointMatrix_restrict`) and apply the previous lemma.
- `MatrixRepresentation.galoisBaseMap_restrictScalars` and
  `transport_congr_base`: `Spec h` is the same morphism whether
  `h ∈ Gal(K/E)` is viewed over `E` or over `k`, and transport depends only on
  that morphism.
- `MatrixRepresentation.galoisTwist_restrict_groupTowerIso_inv`: for
  `h ∈ Gal(K/E)`, the twist by `h` of `ρ` restricted to `(G_E)_K` is the
  restriction of the twist of `ρ` by `h` viewed in `Gal(K/k)`.
- `MatrixRepresentation.Intertwines.restrict`: intertwiners restrict along
  group homomorphisms.

## Highest weights and the tower (`GaloisPinningData`)

- `isHighestWeight_restrict_groupTowerIso_inv_iff`: `ρ` has highest weight `λ`
  for `d` exactly when its restriction to `(G_E)_K` has highest weight
  `weightTransport E λ` for `d.baseChange E`. This is the published
  `SplitPinning.isHighestWeight_restrict_iso_iff` (`Reductive/GaloisPinningIso`)
  for the tower isomorphism. Its inputs are the square
  `torusTowerIso_square`, the root-datum equivalence `baseChangeRootDatumEquiv`
  with weight map `weightTransport E`, and `mem_baseChange_base_support_iff`.
- `exists_intertwiner_galoisTwist_of_smul`: if the star action of a single
  `σ` fixes the highest weight `λ` of `ρ`, then `ρ` is isomorphic to `ρ^σ`.
  This is the published classification (`splitHighestWeightClassification`)
  applied to `ρ` and `ρ^σ` (`isHighestWeight_galoisTwist`). It is the
  one-element version of `exists_intertwiner_galoisTwist`.

## The base-changed obstruction

`titsObstructionValue_baseChange_eq_classOf`. Hypotheses:

- `K/E` is Galois, and the coroots of `d.baseChange E` span its cocharacter
  lattice (`hspanE`);
- `ρ` is a representation of `G_K` on `Fin r` (`r ≥ 1`) of highest weight `λ`;
- `Q h` is invertible for `h ∈ Gal(K/E)` and intertwines `ρ` with its twist
  by `h` viewed in `Gal(K/k)`;
- `weightTransport E λ` is star-fixed for `d.baseChange E` (`hfixE`).

Conclusion: the `E`-algebra `twistedFixed Q` spans `M_r(K)`, and
`titsObstructionValue (d.baseChange E) (weightTransport E λ)` is the class of
`toCSA Q (twistedFixed Q)`.

Proof. Let `ρ_E` be the restriction of `ρ` to `(G_E)_K`. It has highest
weight `weightTransport E λ`, and `Q h` intertwines `ρ_E` with its twist by
`h` (`galoisTwist_restrict_groupTowerIso_inv`, `Intertwines.restrict`). So
`titsAlgebra ρ_E ≤ twistedFixed Q` over `E`. The Tits algebra spans
(`span_titsAlgebra_eq_top`, with scalar self-intertwiners from
`IsHighestWeight.intertwiner_eq_scalar`), hence so does `twistedFixed Q`.
Then `titsObstructionValue_of_maximal` for `d.baseChange E`, `ρ_E`, `Q` and
`B = twistedFixed Q` gives the class. Multiplicity one and maximality come
from the highest weight.

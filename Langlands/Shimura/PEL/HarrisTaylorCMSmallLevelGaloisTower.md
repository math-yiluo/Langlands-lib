# Towers over sufficiently small CM levels with a commuting action, as representations of the finite-adelic similitude group

This internal construction specializes the published
`Langlands.Shimura.RestrictedLevelGaloisColimit` to the sufficiently small
levels of the CM unitary similitude group, which are levels of the opposite
group. Let `F` be a presheaf of modules on these levels, with an action of a
monoid `Γ` at every level that commutes with the transition maps. The module
makes the colimit of `F` over the levels a smooth representation of the
finite-adelic similitude group `G(A_f)` itself, not of its opposite, with a
commuting action of `Γ`. It also provides the `Γ`-equivariant maps from the
levels to fixed vectors, the proposition that these maps are bijective for
every level, and the level Hecke algebra acting on the fixed vectors.

## Motivation and scope

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), III.2, form the cohomology of the Shimura tower as a colimit over
sufficiently small open compact levels `U` of `G(A^∞)`. On printed p.96
(PDF p.104), read on a rendered image of the page because the text layer
omits the displays, they set
"`H^i(X, L_ξ) = lim_{→U} H^i_et(X_U ×_F F^ac, L_ξ)`". They let `g ∈ G(A^∞)`
act through the maps between levels related by conjugation by `g`, and
state: "If `V ⊂ U` then we see that
`H^i_et(X_U ×_F F^ac, L_ξ) ≅ H^i_et(X_V ×_F F^ac, L_ξ)^{U/V}`." On printed
p.97 (PDF p.105, text layer) they continue: "Thus `H^i(X, L_ξ)` becomes an
admissible `G(A^∞)`-module, in fact an admissible/continuous
`G(A^∞) × Gal(F^ac/F)`-module."

In the Library, the CM tower is indexed by `σ.SmallLevelCategory` for
`σ : AlgebraInvolution ℚ B`. Its objects are compact open subgroups of the
opposite group `σ.FiniteAdelicPointsᵐᵒᵖ`, because the cohomology is
contravariant in the transporters. The intended input `F` is the
`λ`-adic cohomology of the CM tower with Harris's coefficient systems,
`U ↦ H^d(S_U ×_F F̄, W)_λ`, with `Γ = Gal(F̄/F)`. This module does not use
that input: `F` is arbitrary and level-trivial, and `Γ` is an arbitrary
monoid. The module constructs no Shimura variety, cohomology or Galois group.
It proves no admissibility, finiteness, continuity or smoothness of the
action of `Γ`. It does not prove the fixed-vector comparison; it states it as
the proposition `TowerFixedVectorComparison`. The passages above are
motivation; no statement of Harris–Taylor is formalized here.

## Inputs

- `Langlands.Shimura.Unitary.Adelic` and
  `Langlands.Shimura.Unitary.SufficientlySmallLevels`: for an involution
  `σ : AlgebraInvolution ℚ B` of a finite-dimensional `ℚ`-algebra `B`,
  `σ.FiniteAdelicPoints` is the group of similitudes of `σ` over the finite
  adeles of `ℚ`, with its topology. `σ.LevelSufficientlySmall` is Harris–Taylor's
  sufficiently-small condition on compact open levels of
  `σ.FiniteAdelicPointsᵐᵒᵖ`, and `σ.SmallLevelCategory` is the full
  subcategory of the transporter category of levels satisfying it.
- `Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelCohomology`: the instances
  stating that sufficient smallness passes to smaller and to conjugate levels
  (`IsDownwardClosed`, `IsConjStable`), which the colimit action needs.
- `Langlands.Shimura.PEL.HarrisTaylorCMCoefficientReduction`:
  `CompactOpenLevel.inverseOppositeContinuousEquiv : G ≃ₜ* Gᵐᵒᵖ`, the map
  `g ↦ op g⁻¹`, and `CompactOpenLevel.inverseOpposite U`, the ordinary
  compact open level `{g | op g⁻¹ ∈ U}` of `G` attached to a level `U` of
  `Gᵐᵒᵖ` (`mem_inverseOpposite`).
- `Langlands.Shimura.LevelColimit`: `conjLevel g U`, the level `g U g⁻¹`
  (`mem_conjLevel`: `x ∈ g U g⁻¹ ↔ g⁻¹ x g ∈ U`).
- `Langlands.Shimura.RestrictedLevelColimit`: `restrictedConj P g U` and
  `restrictedConjArrow P g U`, the conjugate level and its arrow; the
  property `IsLevelTrivial F`; the colimit inclusions `ι F₀ U`.
- `Langlands.Shimura.RestrictedLevelGaloisColimit`: `smoothRepAction`,
  `smoothRepAction_ρ_ι_apply`, `smoothRepAction_representation_ι_apply`,
  `FixedVectorComparison`, and the restriction along a continuous
  homomorphism `φ`: `smoothRepActionPullback`, `fixedLegPullback`,
  `fixedLegPullbackIso`.
- `Langlands.Shimura.LevelHeckeAction` and `Langlands.Shimura.LevelHeckeModule`:
  `fixedVectorsActionFunctor R Γ K`, `heckeModuleActionFunctor R Γ K`,
  `heckeModuleActionFunctor_ρ_smul`, `doubleCoset_smul`, the published
  `LevelHeckeAlgebra R K` and double-coset operator `heckeOperator`.

## The convention `g ↦ op g⁻¹`

The levels are subgroups of `σ.FiniteAdelicPointsᵐᵒᵖ`, so the published
colimit is a representation of the opposite group. Here an element `g` of
`σ.FiniteAdelicPoints` acts as the element `op g⁻¹` of the opposite group.
The map `g ↦ op g⁻¹` is a continuous group isomorphism, so this gives a
smooth representation of `σ.FiniteAdelicPoints` itself. A level `U` of the
opposite group corresponds to the ordinary level `inverseOpposite U`. The
published constant-coefficient CM modules (for example
`HarrisTaylorCMSmallLevelCohomology`) keep the opposite group instead. The
same identification `inverseOppositeEquiv` relates the two descriptions of
a level.

## Declarations

### Generic lemmas on levels of the opposite group

In namespace `Langlands.Shimura.CompactOpenLevel`, for a topological group `G`:

- `map_inverseOpposite_subgroup U`: the image of the ordinary level
  `inverseOpposite U` under `g ↦ op g⁻¹` is `U`.
- `mem_inverseOpposite_conjLevel g x U`:
  `x ∈ inverseOpposite (conjLevel (op g⁻¹) U)` if and only if
  `g⁻¹ x g ∈ inverseOpposite U`. So conjugating a level of the opposite group
  by `op g⁻¹` conjugates its ordinary level by `g`.

### The tower as a representation of `G(A_f)`

In namespace `Langlands.Shimura.SmallLevelGaloisTower`. Let
`B` be a finite-dimensional `ℚ`-algebra with an involution `σ`, `R` a
commutative ring and `Γ` a monoid. Let
`F : σ.SmallLevelCategoryᵒᵖ ⥤ Action (ModuleCat R) Γ` be level-trivial
(`hF : IsLevelTrivial F`). Write `F₀ = F ⋙ Action.forget (ModuleCat R) Γ`
and `small = σ.LevelSufficientlySmall`.

- `inverseOppositeHom σ : σ.FiniteAdelicPoints →* σ.FiniteAdelicPointsᵐᵒᵖ`
  is `g ↦ op g⁻¹`; `continuous_inverseOppositeHom σ` states its continuity.
- `towerAction F hF : Action (SmoothRep R σ.FiniteAdelicPoints) Γ` is
  `smoothRepActionPullback F hF (inverseOppositeHom σ) _`. Its carrier is the
  colimit of `F₀` over the sufficiently small levels, `g` acts as `op g⁻¹`,
  and `Γ` acts by morphisms of smooth representations.
- `towerAction_ρ_ι_apply`: `γ ∈ Γ` sends the class `(ι F₀ U).hom x` to
  `(ι F₀ U).hom (γ x)`, where `γ x` is the action at level `U`.
- `towerAction_representation_ι_apply`: `g ∈ σ.FiniteAdelicPoints` sends
  `(ι F₀ U).hom x` to the class at the conjugate level
  `restrictedConj small (op g⁻¹) U` of the image of `x` under the transition
  map of `restrictedConjArrow small (op g⁻¹) U`.
- `mem_inverseOpposite_restrictedConj`: the ordinary level of that conjugate
  level is `g K g⁻¹`, where `K = inverseOpposite U`. So `g` moves classes from
  ordinary level `K` to ordinary level `g K g⁻¹`, as in Harris–Taylor.
- `towerAction_comm`: the actions of `γ ∈ Γ` and `g ∈ σ.FiniteAdelicPoints`
  commute.

### Fixed vectors and the comparison proposition

- `towerFixedLeg F hF U` is the `Γ`-equivariant map from `F.obj (op U)` to
  the vectors of `towerAction F hF` fixed by the ordinary level
  `inverseOpposite U`. The map is `fixedLegPullback` for
  `φ = inverseOppositeHom σ`, and the hypothesis on the image of the level is
  `map_inverseOpposite_subgroup`. On vectors it is `x ↦ (ι F₀ U).hom x`
  (`towerFixedLeg_hom_apply_coe`).
- `TowerFixedVectorComparison F` is the proposition that
  `FixedVectorComparison F₀ U` holds for every sufficiently small level `U`:
  `(ι F₀ U).hom` is injective and its image is the set of vectors of the
  colimit fixed by `U`. It is the fixed-vector form of the identification of
  Harris–Taylor quoted above, for every level at once, and it is stated, not
  proved.
- `towerFixedLegIso F hF h U`, for `h : TowerFixedVectorComparison F`, is the
  isomorphism in `Action (ModuleCat R) Γ` between `F.obj (op U)` and the
  `inverseOpposite U`-fixed vectors of `towerAction F hF`, with hom
  `towerFixedLeg F hF U` (`towerFixedLegIso_hom`).

### The Hecke algebra on fixed vectors

- `towerHeckeModule F hF U` is the vectors of `towerAction F hF` fixed by the
  ordinary level `K = inverseOpposite U`, as a module over the published
  `LevelHeckeAlgebra R K`, with the action of `Γ` by module maps
  (`heckeModuleActionFunctor`).
- `towerHeckeModule_ρ_smul`: each `γ ∈ Γ` commutes with every element of the
  Hecke algebra.
- `doubleCoset_smul_towerHeckeModule`: for `g ∈ σ.FiniteAdelicPoints`, the
  double coset `[K g K]` acts on the `K`-fixed vectors as the published
  `heckeOperator` with levels `K`, `K` and element `g`.

## Provenance

The constructions are internal. They specialize the published restricted
level colimit with a commuting action, its restriction along a continuous
homomorphism, fixed vectors and the level Hecke algebra to the sufficiently
small CM levels and the continuous isomorphism `g ↦ op g⁻¹`.
`TowerFixedVectorComparison` is the fixed-vector form of the finite-level
identification of Harris–Taylor (2001), III.2, printed p.96 (PDF p.104,
rendered image), used for admissibility on printed p.97 (PDF p.105). Source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, PDF SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`; printed
page = PDF page − 8. Harris–Taylor do not state it as a separate result.
This module states it for an arbitrary level-trivial presheaf of modules on
the sufficiently small CM levels, without proof.

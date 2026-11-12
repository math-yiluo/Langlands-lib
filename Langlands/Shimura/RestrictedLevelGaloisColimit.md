# Colimits over levels of presheaves of modules carrying a further action

This internal construction extends the published colimit over levels
satisfying a property `P` (`Langlands.Shimura.RestrictedLevelColimit`) to
presheaves of modules on which a monoid `Γ` acts at every level, compatibly
with the transition maps. The colimit is then a smooth representation of `G`
on which `Γ` acts by morphisms of smooth representations, so the two actions
commute. The module also gives the `Γ`-equivariant map from each level `U`
into the `U`-fixed vectors of the colimit, an exact proposition stating that
this map is bijective, the module structure of the fixed vectors over the
level Hecke algebra, and the restriction of all of this along a continuous
group homomorphism.

## Motivation and scope

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), III.2, form the cohomology of a Shimura tower as a colimit over
sufficiently small open compact levels. On printed p.96 (PDF p.104), read on
a rendered image of the page because the text layer omits the displays, they
set "`H^i(X, L_ξ) = lim_{→U} H^i_et(X_U ×_F F^ac, L_ξ)`", let `g ∈ G(A^∞)`
act through maps between levels related by conjugation by `g`, and state: "If
`V ⊂ U` then we see that `H^i_et(X_U ×_F F^ac, L_ξ) ≅ H^i_et(X_V ×_F F^ac, L_ξ)^{U/V}`."
On printed p.97 (PDF p.105, text layer) they continue: "Thus `H^i(X, L_ξ)`
becomes an admissible `G(A^∞)`-module, in fact an admissible/continuous
`G(A^∞) × Gal(F^ac/F)`-module." The Galois group acts at every level and
commutes with the level-changing maps, which is the situation of this module
with `Γ = Gal(F^ac/F)`.

This module constructs no Shimura variety, cohomology, sheaf or Galois group:
`Γ` is an arbitrary monoid and the presheaf is arbitrary. It proves no
admissibility, finiteness, continuity or smoothness of the action of `Γ`, and
it does not prove the fixed-vector comparison; it only states it as the
proposition `FixedVectorComparison`. The passages above are motivation; no
statement of Harris–Taylor is formalized here.

## Inputs

The published module `Langlands.Shimura.RestrictedLevelColimit` provides, for
a property `P : ObjectProperty (CompactOpenLevel G)` of compact open levels of
a group `G` with a topology, the full subcategory `P.FullSubcategory` of
levels satisfying `P`; the restricted self-arrows `restrictedSelfArrow P K k hk`
(element `k ∈ K`); the conjugate level `restrictedConj P g U` (the level
`g U g⁻¹`) with the arrow `restrictedConjArrow P g U : restrictedConj P g U ⟶ U`
(element `g`); the property `IsLevelTrivial F` (every restricted self-arrow
acts as the identity) and the full subcategory
`levelTrivialProperty P C` of level-trivial presheaves; the colimit inclusion
`ι F U`; the translation `translate F g`; the elementwise formulas
`translate_ι_apply` and `translate_ι_apply_of_mem`; the natural map of
colimits `ι_map`; and the functor `smoothFunctor P R` from level-trivial
presheaves of `R`-modules to `SmoothRep R G`, whose value on `F` is the smooth
representation `smoothRep F hF`.

The published `Langlands.Shimura.LevelHeckeAction` and
`Langlands.Shimura.LevelHeckeModule` provide
`fixedVectorsActionFunctor R Γ K : Action (SmoothRep R G) Γ ⥤ Action (ModuleCat R) Γ`
(the `K`-fixed vectors `fixedVectors A.V.obj.ρ K` with the induced action of
`Γ`), `heckeModuleActionFunctor R Γ K` (the same fixed vectors as modules over
`LevelHeckeAlgebra R K`), `heckeModuleActionFunctor_ρ_smul`, and
`doubleCoset_smul`, by which the double coset `[K g K]` acts as the published
double-coset operator `heckeOperator ρ K K g`, `v ↦ ∑_{k ∈ K/(K ∩ g K g⁻¹)} ρ(k g) v`.

Mathlib provides `Action V Γ` (objects of `V` with a monoid morphism
`ρ : Γ →* End`), `Functor.mapAction`, `Action.forget`, `Action.mkIso` and
`Rep.resFunctor`. The published `isSmooth_comp`
(`Langlands.Representation.Smooth.Transfer.PullbackProof`) states that a
smooth representation stays smooth after composing with a continuous group
homomorphism.

## The action of `Γ` on the underlying presheaf

All declarations are in namespace `Langlands.Shimura.RestrictedLevelColimit`.
Let `R` be a commutative ring, `Γ` a monoid and
`F : P.FullSubcategoryᵒᵖ ⥤ Action (ModuleCat R) Γ`. Thus `F` is a presheaf of
`R`-modules on levels satisfying `P`, with an action of `Γ` on every
`F.obj (op U)` commuting with all transition maps `F.map a`.

- `isLevelTrivial_forget F hF`: if `F` is level-trivial, so is the underlying
  presheaf of modules `F ⋙ Action.forget (ModuleCat R) Γ`.
- `actionNatTrans F γ` is the endomorphism of the underlying presheaf of
  modules given by the action of `γ` at every level (`actionNatTrans_app`).
- `levelTrivialAction F hF` is the underlying level-trivial presheaf of
  modules, as an object of `levelTrivialProperty P (ModuleCat R)`, with `γ`
  acting by `actionNatTrans F γ`.

## The colimit as a smooth representation with a commuting action of `Γ`

Assume moreover that `G` is a topological group, `IsConjStable P`, and that
`ModuleCat R` has colimits of shape `(RestrictedOrdered P)ᵒᵖ`. Let `hF` state
that `F` is level-trivial, and write `F₀ = F ⋙ Action.forget (ModuleCat R) Γ`.

- `smoothRepAction F hF : Action (SmoothRep R G) Γ` is the image of
  `levelTrivialAction F hF` under `(smoothFunctor P R).mapAction Γ`. Its
  underlying smooth representation is, by definition, the published
  `smoothRep F₀ (isLevelTrivial_forget F hF)` (`smoothRepAction_V`), and each
  `γ ∈ Γ` acts by the morphism of smooth representations induced on colimits
  by `actionNatTrans F γ`.
- `smoothRepAction_ρ_ι_apply`: `γ` sends `(ι F₀ U).hom x` to
  `(ι F₀ U).hom (γ x)`, where `γ x` is the action at level `U`.
- `smoothRepAction_representation_ι_apply`: `g ∈ G` sends `(ι F₀ U).hom x` to
  `(ι F₀ (restrictedConj P g U)).hom ((F.map (restrictedConjArrow P g U).op).hom.hom x)`,
  the class of the image of `x` at the conjugate level `g U g⁻¹`.
- `smoothRepAction_comm`: the action of `γ ∈ Γ` commutes with the action of
  every `g ∈ G`. It holds because `γ` acts by a morphism of smooth
  representations.

### Fixed vectors

Let `U` be a level satisfying `P`.

- `ι_apply_mem_fixedVectors`: every `(ι F₀ U).hom x` is fixed by every
  element of `U`, by `translate_ι_apply_of_mem`.
- `fixedLegLinear F hF U` is the `R`-linear map from `F.obj (op U)` to the
  `U`-fixed vectors of the colimit with values `(ι F₀ U).hom x`
  (`fixedLegLinear_apply_coe`).
- `fixedLeg F hF U : F.obj (op U) ⟶ (fixedVectorsActionFunctor R Γ U.obj.subgroup).obj (smoothRepAction F hF)`
  is that map as a morphism commuting with the actions of `Γ`
  (`fixedLeg_hom`).
- `FixedVectorComparison F₀ U`, for any presheaf of `R`-modules
  `F₀ : P.FullSubcategoryᵒᵖ ⥤ ModuleCat R`, is the proposition that
  `(ι F₀ U).hom` is injective and its image is
  `{z | ∀ u ∈ U, (translate F₀ u).hom z = z}`, the vectors of the colimit
  fixed by `U`. It is stated, not proved.
- `fixedVectorComparison_iff_bijective`:
  `FixedVectorComparison F₀ U` holds exactly when `fixedLegLinear F hF U` is
  bijective.
- `fixedLegIso F hF U h` is, under `h : FixedVectorComparison F₀ U`, the
  isomorphism in `Action (ModuleCat R) Γ` between `F.obj (op U)` and the
  `U`-fixed vectors of `smoothRepAction F hF`, with hom `fixedLeg F hF U`
  (`fixedLegIso_hom`).

`FixedVectorComparison F₀ U` has the form of the conclusion of the published
proposition `HarrisCMColimitInvariantsStatement`
(`Langlands.Cohomology.HarrisCMColimitInvariants.Statement`) for one level.

### The Hecke algebra on fixed vectors

- `heckeModule F hF K`, for a subgroup `K` of `G`, is
  `(heckeModuleActionFunctor R Γ K).obj (smoothRepAction F hF)`: the `K`-fixed
  vectors of the colimit as a module over the published `LevelHeckeAlgebra R K`,
  with the action of `Γ` by module maps.
- `heckeModule_ρ_smul`: each `γ ∈ Γ` commutes with every element of the
  Hecke algebra.
- `doubleCoset_smul_heckeModule`: for a compact open level `K` and `g ∈ G`,
  the double coset `doubleCoset K g` acts on the `K`-fixed vectors as the
  published `heckeOperator` with levels `K`, `K` and element `g`.

## Restriction along a continuous homomorphism

Let `H` be a group with a topology and `φ : H →* G` a group homomorphism with
`hφ : Continuous φ`. This section allows the level group to differ from the
group whose action is wanted, for example when the levels are compact open
subgroups of the opposite group.

- `smoothRepPullback R φ hφ : SmoothRep R G ⥤ SmoothRep R H` restricts a
  smooth representation along `φ`, keeping the carrier: `h ∈ H` acts as
  `φ h` (`smoothRepPullback_obj_ρ`). It lifts Mathlib's `Rep.resFunctor φ`,
  with smoothness from `isSmooth_comp`.
- `fixedVectors_smoothRepPullback`: the `K'`-fixed vectors of the restriction,
  for `K' : Subgroup H`, are the vectors fixed by the image `K'.map φ`.
- `fixedVectorsPullbackIso R Γ φ hφ A hK` is, for
  `A : Action (SmoothRep R G) Γ` and `hK : K'.map φ = K`, the isomorphism in
  `Action (ModuleCat R) Γ` between the `K'`-fixed vectors of the restriction
  of `A` and the `K`-fixed vectors of `A`. It is the identity on vectors
  (`fixedVectorsPullbackIso_hom_apply_coe`).

With `F` and `hF` as above:

- `smoothRepActionPullback F hF φ hφ` is `smoothRepAction F hF` restricted
  along `φ`, an object of `Action (SmoothRep R H) Γ`.
- `fixedLegPullback F hF φ hφ U hK`, for `hK : K'.map φ = U.obj.subgroup`, is
  `fixedLeg F hF U` followed by the inverse of `fixedVectorsPullbackIso`: the
  `Γ`-equivariant map from level `U` into the `K'`-fixed vectors of the
  restricted colimit.
- `fixedLegPullbackIso F hF φ hφ U hK h` is, under
  `h : FixedVectorComparison F₀ U`, the corresponding isomorphism, with hom
  `fixedLegPullback F hF φ hφ U hK` (`fixedLegPullbackIso_hom`).

## Provenance

The constructions are internal assemblies of Mathlib's `Action`,
`Functor.mapAction`, full-subcategory lifts, `Rep.resFunctor` and linear
equivalences with the published restricted level colimit, its smooth
representation functor, fixed vectors, the level Hecke algebra and its module
structure on fixed vectors. `FixedVectorComparison` is the fixed-vector form
of the finite-level identification of Harris–Taylor (2001), III.2, printed
p.96 (PDF p.104, rendered image), used for admissibility on printed p.97
(PDF p.105): source `harris-taylor-2001-geometry-cohomology-simple-shimura`,
PDF SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`, printed
page = PDF page − 8. Harris–Taylor do not state it as a separate result, and
this module states it for an arbitrary presheaf of modules, without proof.

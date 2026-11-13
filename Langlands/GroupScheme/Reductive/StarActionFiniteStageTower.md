# Galois actions on characters along a tower of base changes

Author: Worker 61. This is a helper module for the proof of
`Langlands.GroupScheme.StarActionFiniteStageStatement` (module
`Langlands.GroupScheme.Reductive.StarActionFiniteStageProof`, Task 5982, written under the
plan of Task 5703). It contains only definitions and lemmas used by that proof. The module
proves no published statement. Every declaration lives in the namespace
`Langlands.GroupScheme.StarActionFiniteStage`. `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound` for every theorem checked (for example
`towerCharacterOf_transport` and `baseChange_map_eq_groupTowerIsoOf`).

All content is internal infrastructure. It is not taken from the literature (provenance:
derived). It formalizes a standard compatibility: in a tower `K ⊇ L ⊇ k`, base change of
characters from `T_L` to `T_K` commutes with the action of compatible automorphisms of
`L` and `K`.

## Setting

Schemes `B`, `SL`, `SK` with maps `bL : SL ⟶ B` and `j : SK ⟶ SL`, and a commutative group
scheme `T` over `B`. In the application `B = Spec k`, `SL = Spec L`, `SK = Spec K`, and
`j = Spec(L → K)`.

## Contents

### Points (section `Points`)

- `characterLattice_baseChange_points`: for `ψ ∈ X^*(T)` and a point `z` of `T_{S'}` over a
  test scheme `U` over `S'`, the base-changed character `characterLattice.baseChange b T ψ`
  evaluated at `z` equals `ψ` evaluated at the point `baseChangePointsEquiv b T U z` of `T`
  over `U` viewed over `S` (both values are read as units through `Gm.pointsEquiv`). It is
  the Library lemma `rationalCharacters.characterEval_baseChange`, restated for
  `characterLattice`.

### The tower isomorphism (section `Tower`)

- `towerIso bL j T : T_{j ≫ bL} ≅ (T_{bL})_j`: the Library isomorphism
  `Langlands.GroupScheme.baseChangeCompIso` (module `AbelianScheme/Tate/BaseChangeCoherence`),
  packaged with `CommGroupScheme.isoOfGroupIso` as an isomorphism of
  commutative group schemes. `groupHom_towerIso_hom` records that its underlying group map
  is `(baseChangeCompIso bL j T.toGrp).hom`, by `rfl`.
- `towerTestHom j aL aK hcomm U`: for endomorphisms `aL` of `SL` and `aK` of `SK` with
  `j ≫ aL = aK ≫ j`, and a test scheme `U` over `SK`, the identity of `U.left` read as an
  arrow `(Over.map j).obj ((Over.map aK).obj U) ⟶ (Over.map aL).obj ((Over.map j).obj U)` of
  schemes over `SL`. `towerTestHom_left` records that its underlying map is the identity.
- `towerTestHom_comp_descentPoint`: for a group `G` over `B`, with `aL ≫ bL = bL` and
  `aK ≫ j ≫ bL = j ≫ bL`, two ways of moving a point `y` of `G_{j ≫ bL}` agree. One first
  goes down to `G_{bL}` through `baseChangeCompIso` and `baseChangePointsEquiv j`, and then
  transports along `aL` with the Library `descentPoint`. The other first transports along
  `aK` and then goes down. The two points are compared through `towerTestHom`. The proof
  applies the injective map `baseChangePointsEquiv bL G _`, rewrites with
  `baseChangePointsEquiv_naturality`, `baseChangePointsEquiv_descentPoint` and
  `baseChangePointsEquiv_base_comp`, cancels `baseChangeCompIso` with its inverse, and
  closes the goal by `Over.OverMorphism.ext` and `simp` with `descentTestIso` and
  `Over.mapComp`.
- `towerCharacter bL j T : X^*(T_{bL}) → X^*(T_{j ≫ bL})`, `χ ↦ (towerIso bL j T).hom ≫
  characterLattice.baseChange j _ χ`: base change of characters along `j`, read on
  `T_{j ≫ bL}`.
- `towerCharacter_transport` (**tower compatibility**): under the same hypotheses on `aL`
  and `aK`,
  `towerCharacter (characterLattice.transport bL aL haL T χ) =
  characterLattice.transport (j ≫ bL) aK haK T (towerCharacter χ)`.
  The proof works on points (`characterLattice.ext_points`). Both sides are evaluated at a
  point `y` over a test scheme `U`. A chain of equalities built from
  `comp_groupHom_comp`, `characterLattice_baseChange_points`,
  `characterLattice.transport_points` and `towerTestHom_comp_descentPoint` reduces each
  side to `χ` evaluated at the same point of `T_{bL}`. On the right the point is first
  precomposed with `towerTestHom`. `Gm.pointsEquiv_naturality` along `towerTestHom`
  removes that precomposition, because the underlying map of `towerTestHom` is the
  identity. The chain is written with term-mode `Eq.trans` and `congrArg`, because
  `rw` cannot rewrite between the two presentations of the base-changed group's object.

### Along an equality of base maps (still section `Tower`)

In the application the base map `Spec(k → K)` equals `j ≫ bL` only propositionally. These
declarations take `bK : SK ⟶ B` and `hc : j ≫ bL = bK`, and insert an `eqToIso`.

- `towerIsoOf bL j T bK hc : T_{bK} ≅ (T_{bL})_j` and, for a group scheme `G` over `B`,
  `groupTowerIsoOf bL j bK hc G : G_{bK} ≅ (G_{bL})_j` (again from
  `Langlands.GroupScheme.baseChangeCompIso`).
- `towerIsoOf_square`: for `i : T.toGrp ⟶ G`, the square
  `i_{bK} ≫ (groupTowerIsoOf G).hom = (towerIsoOf T).hom ≫ (i_{bL})_j` commutes. After
  `subst hc` it is the Library lemma `baseChangeCompIso_hom_naturality` (module
  `Torus/StrictHenselianMaximalReduction`).
- `baseChange_map_eq_groupTowerIsoOf`: for a homomorphism `i : H ⟶ G` of group schemes
  over `B`, `(i_{bL})_j = (groupTowerIsoOf H).inv ≫ i_{bK} ≫ (groupTowerIsoOf G).hom`.
  It follows from the same naturality lemma and `Iso.inv_hom_id_assoc`.
- `towerCharacterOf bL j T bK hc : X^*(T_{bL}) → X^*(T_{bK})`, `χ ↦ (towerIsoOf T).hom ≫
  characterLattice.baseChange j _ χ`.
- `towerCharacterOf_transport`: tower compatibility in this form, for `aK ≫ bK = bK`. After
  `subst hc` the `eqToIso` is the identity and the statement is `towerCharacter_transport`.

### Based projections for pinnings over two fields (section `Pinnings`)

These are copies of `StarActionIndependence.conjAut_mem_basedRootDatumAut` and
`StarActionIndependence.comp_basedRootDatumProjection` (module
`Reductive/StarActionIndependenceProof`). The proofs are the same, but here the two split
pinnings `p : SplitPinning G` and `q : SplitPinning H` may be over different fields `k` and
`k'`. The Library versions require one field.

- `conjAut_mem_basedRootDatumAut`: if `e : p.rootDatum ≃ q.rootDatum` carries the support
  of `p.base` onto the support of `q.base`, then `StarActionIndependence.conjAut e` maps
  based automorphisms of `p` to based automorphisms of `q`.
- `comp_basedRootDatumProjection`: if moreover `x' * (conjAut e x)⁻¹` lies in the Weyl group
  of `q.rootDatum`, then
  `e.comp (p.basedRootDatumProjection x).val = (q.basedRootDatumProjection x').val.comp e`.
  The proof uses `basedRootDatumProjection_correction`,
  `basedRootDatum_representative_unique`, `conjAut_mem_weylGroup` and
  `comp_eq_conjAut_comp`.

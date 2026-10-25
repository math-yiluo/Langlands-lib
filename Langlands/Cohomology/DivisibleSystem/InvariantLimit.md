# Harris's direct limit `C_m^•` over shrinking subgroups and the comparison (2.6)

Author: Worker 61. Built on
`Langlands.Cohomology.DivisibleSystem.Colimit` (`colimitSystem`,
`colimitSystemDesc`, `levelCocone`),
`Langlands.Cohomology.DivisibleSystem.InvariantTransitivity`
(`quotientInvariantsTransition_comp`, `quotientInvariantsTransition_refl`),
`Langlands.Cohomology.ExactColimitQuasiIso`
(`ExactColimit.quasiIso_isColimit_desc`), and through them on
`…InvariantTransition` (`quotientProjection`, `quotientInvariantsTransition`,
`quotientInvariantsTransition_comp_toRepExtend`), `…InvariantComparison`
(`inflatedQuotientInvariantsTotalSystem`,
`quotientInvariantsTotalSystemToRepExtend`,
`quasiIso_quotientInvariantsTotalSystemToRepExtend`), `…Invariants`
(`smoothQuotientInvariants`, `toRepComplexes`), `…ProPInvariants`
(`IsProPSubgroup`), the base module `DivisibleSystem` (`extendSystem`) and
Worker 3's `Langlands.Cohomology.ProPInvariants.Statement`
(`ProPInvariantSubcomplexStatement`, used only as a hypothesis). From
Mathlib it uses `HasExactColimitsOfShape`, `AB5OfSize_of_univLE`,
`HasExactColimitsOfShape.domain_of_functor`,
`hasColimitsOfSizeOfUnivLE`, `preservesColimitsOfSize_of_univLE`, the
forgetful functors `forget₂`, `IsFiltered.isConnected` and quasi-isomorphisms.

Everything is in the namespace `Langlands.Cohomology`; the declarations of
the section "The direct limit" are in `Langlands.Cohomology.DivisibleSystem`.

Notation: composition `f ≫ g` is `f` followed by `g`. As in the earlier
modules, `K` is an `ℓ`-divisible system of `ℕ`-graded complexes of smooth
representations of a group `G` (`SmoothRep.{uR, uG, max w uR uG} R G`),
`N : ℕ` is the number of rows of the total complexes, and for a normal
subgroup `H` of finite index `C^{•,H}` is `quotientInvariantsTotalSystem N K
H hK` (Harris's `C_m^{•,H}` at level `m`). `Inf_H C^{•,H}` is its inflation
to `G`, `inflatedQuotientInvariantsTotalSystem N K H hK`, a system of
`ℤ`-graded complexes of `Rep.{max w uR uG} R G`.

## Exact filtered colimits

`J : Type t` is a small filtered category and `w'` a universe with
`UnivLE.{t, w'}` (`t ≤ w'`).

- `hasExactColimitsOfShape_addCommGrpCat J`: colimits of shape `J` in
  `AddCommGrpCat.{w'}` are exact. Mathlib's AB5 for `AddCommGrpCat.{w'}`
  covers shapes in `Type w'`. It is transported to `J` by
  `AB5OfSize_of_univLE`.
- `hasExactColimitsOfShape_moduleCat J R`: the same in `ModuleCat.{w'} R`
  for any ring `R : Type u`. Exactness is pulled back along the forgetful
  functor to `AddCommGrpCat.{w'}`, which preserves finite limits and
  colimits of shape `J` and reflects finite limits
  (`HasExactColimitsOfShape.domain_of_functor`). Mathlib's own instance
  needs `R : Type w'`.
- `hasColimitsOfShape_rep J k G`: `Rep.{w'} k G` (commutative ring `k`,
  monoid `G`) has colimits of shape `J`. Mathlib's colimits of
  `Rep.{w'} k G` are of size `w'`. The instance restricts them with
  `hasColimitsOfSizeOfUnivLE`.
- `hasExactColimitsOfShape_rep J k G`: colimits of shape `J` in
  `Rep.{w'} k G` are exact. This is pulled back along the forgetful functor
  to `ModuleCat.{w'} k`, which preserves colimits of shape `J` by
  `preservesColimitsOfSize_of_univLE`.

Complexes in these categories then have exact colimits of shape `J` by
Mathlib's `HomologicalComplex.hasExactColimitsOfShape`. In particular this
holds for `CochainComplex (Rep.{max w uR uG} R G) ℤ` with
`J : Type uG`, the case used below.

## The direct limit

`ι : Type uG` is a preorder and `H : ι → Subgroup G` is antitone (`hH`), so
`i ≤ j` gives `H j ≤ H i`. Every `H i` is normal and of finite index. Every
`G ⧸ H i` is a `Fintype` with decidable equality. `hK i` says that the
projections of `K` stay epimorphisms on `H i`-invariants. `hk hij` says
that the order of the kernel of `G ⧸ H j → G ⧸ H i` is a unit in `R`.

- `quotientInvariantsDiagram N K H hH hK hk : ι ⥤ DivisibleSystem
  (CochainComplex (Rep R G) ℤ) ℓ`: `i ↦ Inf_{H i} C^{•,H i}` and, for
  `i ≤ j`, the InvariantTransition module's transition morphism
  `quotientInvariantsTransition K (hH hij) N (hK i) (hK j) (hk hij)` from
  `Inf_{H i} C^{•,H i}` to `Inf_{H j} C^{•,H j}`. The identity and
  composition laws are `quotientInvariantsTransition_refl` and
  `quotientInvariantsTransition_comp` of the InvariantTransitivity module.
  Their order and unit hypotheses agree with those of the diagram by proof
  irrelevance.

Assume further that `ι` is filtered (for example directed and nonempty).

- `quotientInvariantsLimit N K H hH hK hk`: our `C_m^•`, the colimit
  `colimitSystem` of the diagram, an `ℓ`-divisible system of `ℤ`-graded
  complexes of representations of `G`. At level `m` it is the colimit over
  `ι` of the inflated `C_m^{•,H i}`.
- `quotientInvariantsDiagramCocone N K H hH hK hk hN` (for `K` vanishing in
  degrees `q ≥ N`, `hN`): the cocone with vertex
  `K.toRepComplexes.extendSystem` (the underlying complexes of
  representations of `K`, extended to `ℤ`), whose leg at `i` is the
  comparison `quotientInvariantsTotalSystemToRepExtend N K (H i) (hK i) hN`.
  It is a cocone by the InvariantTransition module's
  `quotientInvariantsTransition_comp_toRepExtend`.
- `quotientInvariantsLimitToRepExtend N K H hH hK hk hN`: our (2.6), the
  morphism `colimitSystemDesc` from `quotientInvariantsLimit` to
  `K.toRepComplexes.extendSystem` induced by this cocone. At each level it is
  the morphism from the colimit induced by the level-`m` comparisons.
- `quasiIso_quotientInvariantsLimitToRepExtend N K H hH hK hk hS hP hR hN m
  htriv`: for `G` a topological group,
  `hS : ProPInvariantSubcomplexStatement.{uG, uR, max w uR uG}`,
  `hP i : IsProPSubgroup p (H i)` for all `i`, `hR : IsUnit (p : R)`, and
  `htriv i` saying that `H i` acts trivially on the cohomology of
  `K.toRepComplexes.obj m`: the level-`m` component of (2.6) is a
  quasi-isomorphism. Proof: each leg at level `m` is a quasi-isomorphism by
  `quasiIso_quotientInvariantsTotalSystemToRepExtend`. A filtered category is
  connected, and colimits of shape `ι` of complexes of representations are
  exact (first section). So `ExactColimit.quasiIso_isColimit_desc` applies to
  the level-`m` colimit and its cocone `levelCocone`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed p.306. After forming
`C_m^{•,H}` and noting the change of `H`, Harris writes: "Taking the direct
limit as H shrinks to the identity, we obtain an ℓ-divisible system of
complexes C_m^• of projective Z/ℓ^mZ[S(ẽ)]-modules and a natural
S(ẽ)-equivariant quasi-isomorphism (2.6)". Worker 61 read this passage in
the scanned original. On p.305 the subgroup `H` is an open normal pro-`p`
subgroup of `S(ẽ)` acting trivially on `H_c^q(U(ẽ)_F̄, ℤ/ℓ^mℤ)` for all `q`
and `m`.

Our rendering:

1. The index is a general filtered preorder `ι` with an antitone family of
   normal subgroups of finite index. Harris's family is the open subgroups
   of such an `H` that are normal in `S(ẽ)`, ordered by reverse inclusion.
   That specialization is not formalized. In particular we do not prove that
   these subgroups are pro-`p`, of finite index, or act trivially. Those are
   the hypotheses `hP` and `htriv` and the instances.
2. The transition morphisms are those of the InvariantTransition module.
   That module does not formalize Harris's isomorphism
   `C_m^{•,H} = [C_m^{•,H'}]^H` and explains why it is not the evident
   identification.
3. The direct limit is taken in `Rep R G` (inflated to `G`), not in smooth
   representations, and projectivity of the terms over `Z/ℓ^mZ[S(ẽ)]` is not
   addressed.
4. As in the InvariantComparison module, `htriv` is the trivial action on
   the cohomology of the abstract complex `K.toRepComplexes.obj m`. It is not
   stated for Harris's compactly supported cohomology
   `H_c^q(U(ẽ)_F̄, ℤ/ℓ^mℤ)`; his (2.3) identifies the two, and that is not
   formalized. The quasi-isomorphism also depends on Worker 3's unproved
   `ProPInvariantSubcomplexStatement` (hypothesis `hS`), and the surjectivity
   (`hK`) and unit (`hk`) hypotheses stay explicit.
5. The exact-colimit instances, the diagram, the cocone and the theorem are
   ours. Harris uses without comment that the direct limit is an
   `ℓ`-divisible system and that a direct limit of quasi-isomorphisms is a
   quasi-isomorphism; the Colimit and ExactColimitQuasiIso modules prove
   these in general.

## Scope

The module constructs the direct limit over a filtered family of subgroups
and the comparison (2.6), and proves that (2.6) is a quasi-isomorphism at
each level under the hypotheses above. All objects and maps are in
`Rep R G`, so they are `G`-equivariant (Harris's `S(ẽ)` plays the role of
`G`). It does not construct Harris's specific family of subgroups, (2.7),
Lemma 2.8 or the Mittag-Leffler argument, and it does not compare the
colimit with smooth representations.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

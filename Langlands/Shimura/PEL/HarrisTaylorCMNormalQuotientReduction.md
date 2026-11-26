# Normal-quotient descent of quasi-projective representability from its premises

The module `Langlands.Shimura.PEL.HarrisTaylorCMNormalQuotientReduction`
proves

```
cmQuasiProjectiveNormalQuotientStatement_of_premises
  (hG : FiniteFreeQuasiProjectiveQuotientStatement)
  (hD : CMSmallLevelEtaleSheafStatement D C …)
  (hL : CMSublevelEtaleLiftStatement D C …)
  (hO : CMNormalSublevelConnectedFibreStatement D C …) :
  CMQuasiProjectiveNormalQuotientStatement D C …
```

for the parameters of `CMQuasiProjectiveNormalQuotientStatement` (module
`Langlands.Shimura.PEL.HarrisTaylorCMDivisionQuasiProjectiveDecomposition`).
The four premises are stated in
`Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` and
`Langlands.Shimura.PEL.HarrisTaylorCMNormalQuotientPremiseStatements`; this
module proves none of them. Freeness of the residual action is not a premise:
it comes from the Library theorem `cmSmallLevelRigidity` (module
`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelRigidityProof`). No division
hypothesis is used.

The description of the coarse moduli space as the quotient of the fine one by
the residual group `U/U'` comes from the normal-level covering assertions of
Harris–Taylor (2001), III.1, printed p.91, source
`harris-taylor-2001-geometry-cohomology-simple-shimura` (the finite étale
cover `X_V ⟶ X_U` is Galois with group `U/V` for `V` normal in `U`), and of
Kottwitz, *Points on some Shimura varieties over finite fields* (1992), §6,
printed p.392, source `kottwitz-1992-points-shimura-finite-fields` (the étale
covering `S_{K'^p} ⟶ S_{K^p}` is Galois with group `K^p/K'^p`). Those
assertions concern the moduli problems of the sources, under their running
hypotheses. The construction below is internal to the Library: it builds the
quotient and its representing isomorphism directly for the Library presheaves,
from the four premises.

## Notation

Fix small levels `U' ≤ U` with `U'` normal in `U`, and a quasi-projective
representation `R : CMLevelQuasiProjectiveRepresentation … U'`. Write
`X = R.scheme`, an object of `Over (Spec F)` with an immersion into a
projective space over `F`, `M_U` and `M_U'` for the coarse and fine class
presheaves on the admissible tests `DisBases`, and `forget : M_U' ⟶ M_U` for
the forgetting transition at `smallCMInclusion D hle`.

`noetherianCMTest` turns a scheme over `Spec F` with locally noetherian
underlying scheme into an admissible test, by
`componentwiseAdmissibleCMBase_of_relativeDual` and the Library theorems
`relativeDualSchemeExistence` and `relativeDualSchemeGeometry`. `R.test` is
`X` as a test (it is locally of finite type over `F`). `R.cls T a` is the fine
class of a point `a : T.obj ⟶ X`, given by the representing isomorphism, and
`R.pt T c` is the point of a fine class. `cls_pt`, `pt_cls`, `cls_injective`
and `cls_comp` (naturality) record that these are inverse and natural.

## The residual action

`R.act U hle g` is the Yoneda image of inverse right translation by
`g : U.obj.subgroup`: the point of the class obtained by translating the
universal class `R.cls R.test (𝟙 _)`. It acts on points by postcomposition,
sending a point `a : T.obj ⟶ X` to `a ≫ R.act U hle g`; `cls_comp_act` says
that the class `R.cls T (a ≫ R.act U hle g)` of this composite is the inverse
right translate by `g` of the class `R.cls T a`. Hence
`act_one`, `act_mul` (`act (g * k) = act k ≫ act g`), and `act_of_mem`: for
`g` in `U'` the action is trivial, by
`smallLevelClassPresheafTower_map_eq_of_target_coset`. The same lemma gives
`forget_cls_comp_act`: translation does not change the coarse class.

`actIso`, `actHom` and `residualHom` assemble a group homomorphism from
`SmallCMResidualGroup D U U' = U/U'` to the automorphisms of the underlying
scheme of `X`. `residualAction` is the `FiniteFreeSchemeAction` with
`act q = residualHom q⁻¹`, which has the composition convention of that
structure. Its freeness, `eq_one_of_comp_residualHom`, is proved as follows.
If `a : T ⟶ X` from a nonempty scheme is fixed by the class of `g`, compose
with the geometric point `HarrisGeometricPoint.ofResidue` of `T`. The
resulting point `b : Spec Ω ⟶ X`, viewed as a point of `X` over the test
`cmGeometricTestBase … p`, has a fine class fixed by translation by `g`. The
Library theorem `cmGeometricTestBase_normalTranslate_eq_iff`, with the
rigidity `cmSmallLevelRigidity … U.obj U.property`, then gives `g = 1` in
`U/U'`. `residualAction_over` says that the action is over `Spec F`.

Applying `hG` with the field `F`, the immersion of `R` and this action gives
an effective quotient `Q`, a structure map `t : Q.scheme ⟶ Spec F` with
`Q.map ≫ t = X.hom`, and an immersion of `Q.scheme` into a projective space
over `F` compatible with `t`.

## Coarse classes and the quotient map

`forget_cls_targetO` is the key use of `hD`. The relation scheme
`∐_{q} X` of the action is a test (`relationTest`); its two projections
`sourceO` and `targetO` are points of `X`. Their coarse classes agree: the
summand inclusions `summandO q` are open immersions, hence étale, and they
cover the relation scheme (Mathlib's `sigmaMk`); on the summand `q` the
second projection is an action map and the first is the identity, so the
classes agree after restriction by `forget_cls_comp_act`; `hD` gives
separatedness for this family.

`forget_cls_eq_of_comp_eq`: if two points `b₁ b₂ : T.obj ⟶ X` have the same
composite with `Q.map`, they factor through the relation scheme by the
pullback square `Q.isPullback`, so their coarse classes agree.

`comp_eq_of_forget_cls_eq` is the converse and the use of `hO`. It suffices
to compare the two composites on each open connected component of the
underlying scheme of `T` (`component_hom_ext`, using the Library's
`componentι`, `componentSchemeConnected` and `componentTest`). On a component
the two fine classes have equal coarse classes, so `hO` gives `g` with
`cls (b₁ ≫ act g) = cls b₂` there; injectivity of `cls` and
`act_left_comp_map` (`act g ≫ Q.map = Q.map`, from `Q.condition` on a
summand) finish the proof.

## From points of the quotient to coarse classes

For a test `S` and a morphism `f : S.obj ⟶ Over.mk t`, `pullbackTest` is the
pullback of `Q.map` along `f`, with its étale surjective projection
`pullbackTestπ` to `S` and its projection `pullbackTestPt` to `X`.
`compatible_pullbackTest` checks, with `forget_cls_eq_of_comp_eq`, that the
coarse class of `pullbackTestPt` is a compatible family for the single
morphism `pullbackTestπ`. `hD` (through `isSheafFor_singleton_of_etale`)
gives a unique descended class, `classOfMap`.

`map_classOfMap` characterizes it: for any test morphism `q : S₂ ⟶ S` and any
point `a₂ : S₂.obj ⟶ X` with `a₂ ≫ Q.map = q ≫ f` on underlying schemes, the
pullback of `classOfMap f` along `q` is the coarse class of `a₂`. The proof
pulls back once more along the étale surjective base change of
`pullbackTestπ`, where separatedness (`map_injective_of_etale`) and
`forget_cls_eq_of_comp_eq` apply. `classOfMap_comp` is naturality in `S`.

## From coarse classes to points of the quotient

`CoarseLift` packages the data supplied by `hL`: an étale surjective test
morphism `π : test ⟶ S` and a fine class on `test` lifting the pullback of the
coarse class; `coarseLift` chooses it. The composite of the point of the fine
class with `Q.map` is equal on the two projections of the kernel pair of
`π` (`coarseLift_desc_condition`): the kernel pair is a test, the two fine
classes there have the same coarse class, and `comp_eq_of_forget_cls_eq`
applies. Since an étale surjective morphism is an effective epimorphism in
Mathlib (`Mathlib.AlgebraicGeometry.Sites.Fpqc`), the composite descends
along `π`; this is `mapOfClass`, a morphism over `Spec F` since `π` is an
epimorphism. `mapOfClass_spec` characterizes it by any fine lift of any
pullback of the class, again by comparison on a pullback and
`comp_eq_of_forget_cls_eq`.

## The representation at the coarse level

`mapOfClass_classOfMap` and `classOfMap_mapOfClass` show that the two
constructions are inverse: the first by `mapOfClass_spec` on `pullbackTest`
and cancellation of the epimorphism `pullbackTestπ`, the second by
`map_classOfMap` on the chosen lift and separatedness along its étale
surjection. `quotientRepresents` assembles the natural isomorphism

```
admissibleTestPoints … (Over.mk t) ≅ (smallLevelClassPresheafTower …).obj U
```

from these bijections and `classOfMap_comp`.

The final theorem takes `U' U`, the inclusion, normality and a representation
at `U'`, uses `smallCMResidualGroup_finite` for the finiteness of `U/U'`,
applies `hG` to `residualAction`, and returns the representation at `U` with
scheme `Over.mk t`, the immersion `j'` provided by `hG` and
`quotientRepresents`. The representing scheme at `U` is the quotient, not a
supplied scheme; the presheaf it represents is the Library's
`(smallLevelClassPresheafTower …).obj U`.

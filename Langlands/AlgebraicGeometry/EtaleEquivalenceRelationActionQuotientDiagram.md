# Diagrams of quotient relations of actions

Module `Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionQuotientDiagram`. It imports
`EtaleEquivalenceRelationActionQuotientRelation` (the quotient relation `A.quotientRelation Q Q₂`
of an action) and the Library modules `EtaleEquivalenceRelationFiniteTypeSystem` (the structure
`FiniteTypeCartesianSystem`) and `EtaleEquivalenceRelationActionSystem` (the pulled back objects
`Action.CartesianSystem.objectDiagram` and their cone `objectCone`; through its imports also the
pulled back action `Action.pullbackAction` of `EtaleEquivalenceRelationActionDescent`).

This module is the third generic bridge module for the first-level step of absolute Noetherian
approximation (FL task 8d02331e, Workers 706 and 416). Through that step it serves this task
(Tag 07VS). In that step one has, at every level `i` of a cofiltered system, an étale
equivalence relation `D i`, an action of `D i` on a scheme `P i` étale over `(D i).U`, and the
quotient `O i = P i / D i`. The étale equivalence relation `O i ×_{X i} O i` on `O i` is
`(A i).quotientRelation (Q i) (Q₂ i)` from the imported module. This module makes these
relations into a diagram with cartesian transition maps. It proves that the object schemes of
the diagram have the expected limit, and packages the result as a `FiniteTypeCartesianSystem`,
which is the input format of the FL induction.

The last part of the module constructs such diagrams of actions by base change. A single action
`B` of a relation `F` on `q : Q ⟶ F.U` pulls back along a cartesian comparison
`t : D ⟶ const F` to a diagram of actions on the schemes `(D i).U ×_{F.U} Q`
(`ActionDiagram.ofComparison`). An action on the base change of `Q` to the point of a cone of
`D`, equivariant with `B`, gives an action cone over this diagram
(`ActionDiagram.ActionCone.ofComparison`). For an index `j`, the restriction of `D` to the
category `Over j` of indices over `j` has such a comparison to the constant diagram on `D j`
(`ActionDiagram.overComparison`). This is how an action given at one level `j` is spread to all
levels over `j`.

## Conventions

All schemes live in one universe `u`. Morphisms of `EtaleEquivalenceRelation.{u}` are the
Library `CartesianMorphism`s, with fields `objMap`, `relMap` and `isCartesian`. Their
extensionality lemma is `CartesianMorphism.ext`. `objectFunctor` sends a relation to its object
scheme `U` and a morphism to its `objMap`. For `π : P ⟶ H.U`, the Library structure
`Action H π` is an action of `H` on `P`. Its action relation is `A.relation`, and `A.pairAction`
is the diagonal action on `pullback π π` over `pullback.fst π π ≫ π`, from the imported module.
For an equivariant map of actions (`IsEquivariant h π' π k w A' A`, over a cartesian morphism
`h : IsCartesianHom H' H f g`, with `w : π' ≫ f = k ≫ π`), `arrowMap` and
`isCartesianHom_of_isEquivariant` are the Library constructions of the induced cartesian
morphism of action relations. `SchemeQuotient.map h Q' Q` is the map of quotients induced by a
cartesian morphism `h`, with `q_map`, `isPullback_map` and `isAffineHom_map`.
`SchemeQuotient.quotientFunctor`, `quotientCone` and `isLimitQuotientCone` are the Library
diagram of quotients, its cone and its limit theorem.

## Statements

### Maps of quotient relations (namespace `EtaleEquivalenceRelation.Action`)

Variables: `h : IsCartesianHom H' H f g`, `π' : P' ⟶ H'.U`, `π : P ⟶ H.U`, `k : P' ⟶ P`,
`w : π' ≫ f = k ≫ π`, actions `A' : Action H' π'` and `A : Action H π`, and
`hA : IsEquivariant h π' π k w A' A`.

- `pairObjMap w : pullback π' π' ⟶ pullback π π` is `pullback.map π' π' π π k k f w w`. It has
  `pairObjMap_fst`, `pairObjMap_snd` (with `reassoc` forms) and
  `pairObjMap_w : (pullback.fst π' π' ≫ π') ≫ f = pairObjMap w ≫ pullback.fst π π ≫ π`.
- `isPullback_pairObjMap w hk`: if `hk : IsPullback k π' π f`, then
  `IsPullback (pairObjMap w) (pullback.fst π' π') (pullback.fst π π) k`.
- `isEquivariant_pairObjMap hA`: `pairObjMap w` is equivariant from `A'.pairAction` to
  `A.pairAction` over `h`. `isCartesianHom_pairObjMap hA` is the induced cartesian morphism of
  the pair action relations.
- For quotients `Q' : A'.relation.SchemeQuotient`, `Q : A.relation.SchemeQuotient`,
  `Q₂' : A'.pairAction.relation.SchemeQuotient` and `Q₂ : A.pairAction.relation.SchemeQuotient`:
  - `quotientObjMap hA Q' Q : Q'.M ⟶ Q.M` and `quotientRelMap hA Q₂' Q₂ : Q₂'.M ⟶ Q₂.M` are the
    maps of quotients induced by `k` and by `pairObjMap w`. They are characterized by
    `q_quotientObjMap : Q'.q ≫ quotientObjMap hA Q' Q = k ≫ Q.q` and
    `q_quotientRelMap : Q₂'.q ≫ quotientRelMap hA Q₂' Q₂ = pairObjMap w ≫ Q₂.q`.
  - `isPullback_quotientObjMap`: `IsPullback k Q'.q Q.q (quotientObjMap hA Q' Q)`.
    `isAffineHom_quotientObjMap`: with `[IsAffineHom k] [IsAffineHom Q.q]`, the map
    `quotientObjMap hA Q' Q` is affine.
  - `quotientRelMap_quotientS`, `quotientRelMap_quotientT`: the maps commute with the source maps
    `quotientS` and with the target maps `quotientT` of the two quotient relations.
  - `isPullback_quotientRelMap hA Q' Q Q₂' Q₂ hk`: if `hk : IsPullback k π' π f`, then
    `IsPullback (quotientRelMap hA Q₂' Q₂) (A'.quotientS Q' Q₂') (A.quotientS Q Q₂)
    (quotientObjMap hA Q' Q)`.
  - With `[Etale π'] [Etale π]` and `hk`: `isCartesianHom_quotientRelation` says that the pair
    `(quotientObjMap hA Q' Q, quotientRelMap hA Q₂' Q₂)` is a cartesian morphism
    `A'.quotientRelation Q' Q₂' ⟶ A.quotientRelation Q Q₂`. `quotientRelationHom hA Q' Q Q₂' Q₂ hk`
    is this morphism. Its `objMap` and `relMap` are given by the simp lemmas
    `quotientRelationHom_objMap` and `quotientRelationHom_relMap`.

### Pulled back actions and pulled back objects (namespace `EtaleEquivalenceRelation.Action`)

- `isEquivariant_pullbackAction_of_comp h₁ h₂ h hg hp w hk w' A B hA`. Let
  `h₁ : IsCartesianHom E' E f₁ g₁`, `h₂ : IsCartesianHom E F f₂ g₂` and
  `h : IsCartesianHom E' F f g` be cartesian morphisms with `hg : g₁ ≫ g₂ = g`. Let
  `hp : IsPullback k p q f₂` for `k : P ⟶ Q`, `p : P ⟶ E.U` and `q : Q ⟶ F.U`, so `P` is the base
  change of `Q` along `f₂`. Let `p' : P' ⟶ E'.U`, `l : P' ⟶ P` with `w : p' ≫ f₁ = l ≫ p`, and
  `k' : P' ⟶ Q` with `hk : l ≫ k = k'` and `w' : p' ≫ f = k' ≫ q`. If an action
  `A : Action E' p'` is equivariant via `k'` over `h` with `B : Action F q` (`hA`), then `A` is
  equivariant via `l` over `h₁` with the Library pulled back action `pullbackAction h₂ hp B`.
  Only the relation maps are required to compose (`hg`); the object maps are related through
  `w`, `hk` and `w'`.
- In namespace `Action.CartesianSystem`, for `D : I ⥤ EtaleEquivalenceRelation.{u}`, a
  comparison `t : D ⟶ (Functor.const I).obj F` and `q : Q ⟶ F.U`, write `objectDiagram D t`
  for the Library diagram of the schemes `pullback (t.app i).objMap q`, `objectMap D t i` for
  its first projection to `(D.obj i).U` and `pointComparison D t` for its second projection to
  `Q`. For `a : i ⟶ j`:
  - `comparison_naturality_objMap t a : (D.map a).objMap ≫ (t.app j).objMap = (t.app i).objMap`
    and `comparison_naturality_relMap t a`, the same for `relMap`.
  - `pointComparison_naturality t a : (objectDiagram D t).map a ≫ (pointComparison D t).app j =
    (pointComparison D t).app i`.
  - `objectMap_naturality t a : objectMap D t i ≫ (D.map a).objMap =
    (objectDiagram D t).map a ≫ objectMap D t j`.
  - `isPullback_objectDiagram_map t a : IsPullback ((objectDiagram D t).map a)
    (objectMap D t i) (objectMap D t j) (D.map a).objMap`.

### Diagrams of actions (namespace `EtaleEquivalenceRelation`)

Let `I : Type u` be a category with morphisms in `Type u`, and `D : I ⥤ EtaleEquivalenceRelation.{u}`.

- `structure ActionDiagram D` has fields `points : I ⥤ Scheme.{u}`,
  `proj i : points.obj i ⟶ (D.obj i).U`, `proj_w a : proj i ≫ (D.map a).objMap =
  points.map a ≫ proj j`, `action i : Action (D.obj i) (proj i)`, `etale i : Etale (proj i)`
  (an instance), `isEquivariant a`: `points.map a` is equivariant from `action i` to
  `action j` over `(D.map a).isCartesian`, and `isPullback a : IsPullback (points.map a)
  (proj i) (proj j) (D.map a).objMap`.
- For `A : ActionDiagram D` and a cone `c : Cone D`, `structure A.ActionCone c` has fields
  `P`, `proj : P ⟶ c.pt.U`, `action : Action c.pt proj`, `etale : Etale proj` (an instance),
  `leg i : P ⟶ A.points.obj i`, `leg_w i : proj ≫ (c.π.app i).objMap = leg i ≫ A.proj i`,
  `leg_comp a : leg i ≫ A.points.map a = leg j`, `isEquivariant i`: `leg i` is equivariant
  from `action` to `A.action i` over `(c.π.app i).isCartesian`, and
  `isPullback i : IsPullback (leg i) proj (A.proj i) (c.π.app i).objMap`.

In namespace `ActionDiagram`, for `A : ActionDiagram D`, `T : A.ActionCone c`, quotients
`Q i : (A.action i).relation.SchemeQuotient`, `Q₂ i : (A.action i).pairAction.relation.SchemeQuotient`,
`Qc : T.action.relation.SchemeQuotient` and `Q₂c : T.action.pairAction.relation.SchemeQuotient`:

- `relationDiagram : I ⥤ EtaleEquivalenceRelation` sends `i` to `(A.action i).relation` and
  `a` to the cartesian morphism of action relations with object map `A.points.map a`.
  `relationCone T` is the cone over it with point `T.action.relation` and legs with object maps
  `T.leg i`.
- `isLimitRelationConeObject T hc`: if `I` is cofiltered and
  `hc : IsLimit (objectFunctor.mapCone c)`, then the points `T.P → A.points.obj i` form a limit
  cone, `IsLimit (objectFunctor.mapCone (A.relationCone T))`.
- `quotientRelationDiagram Q Q₂ : I ⥤ EtaleEquivalenceRelation` sends `i` to
  `(A.action i).quotientRelation (Q i) (Q₂ i)` and `a` to `quotientRelationHom` for
  `A.isEquivariant a` and `A.isPullback a`.
- `isAffineHom_quotientRelationDiagram_map Q Q₂ hD a`: if every `(Q i).q` is affine and
  `hD : ∀ a, IsAffineHom (D.map a).objMap`, then every object map of
  `quotientRelationDiagram Q Q₂` is affine.
- `quotientRelationCone T Q Q₂ Qc Q₂c : Cone (A.quotientRelationDiagram Q Q₂)` has point
  `T.action.quotientRelation Qc Q₂c` and legs `quotientRelationHom` for `T.isEquivariant i` and
  `T.isPullback i`.
- `quotientFunctorIso Q Q₂`: the Library diagram of quotients
  `SchemeQuotient.quotientFunctor A.relationDiagram Q` is isomorphic to
  `A.quotientRelationDiagram Q Q₂ ⋙ objectFunctor`. All its components are identities.
- `isLimitQuotientRelationConeOfIsLimit T Q Q₂ Qc Q₂c hP`: for `I` cofiltered, if the points form
  a limit (`hP`), then `IsLimit (objectFunctor.mapCone (A.quotientRelationCone T Q Q₂ Qc Q₂c))`.
  `isLimitQuotientRelationCone T Q Q₂ Qc Q₂c hc` is the same conclusion from the limit
  hypothesis `hc` on the object schemes of `c`.
- `isLimitQuotientRelationConeExtend T Q Q₂ Qc Q₂c hc φ`: for a relation `E` and a morphism
  `φ : E ⟶ T.action.quotientRelation Qc Q₂c` with `[IsIso φ.objMap]`, the cone
  `(A.quotientRelationCone T Q Q₂ Qc Q₂c).extend φ` (point `E`) is still a limit on object
  schemes.
- `finiteTypeCartesianSystem T Q Q₂ Qc Q₂c hc φ hD : FiniteTypeCartesianSystem E` assumes `I`
  cofiltered, `hc`, `φ` as above, and, for every `i`, the instances `CompactSpace (A.points.obj i)`,
  `LocallyOfFiniteType (terminal.from (A.points.obj i))`, `IsAffineHom (A.proj i)`,
  `QuasiSeparatedSpace (pullback (A.proj i) (A.proj i))` and `IsAffineHom (Q i).q`, together
  with `hD`. Its index category is `I`, its diagram is `A.quotientRelationDiagram Q Q₂`
  (simp lemma `finiteTypeCartesianSystem_diagram`), its comparison is the cone
  `(A.quotientRelationCone T Q Q₂ Qc Q₂c).extend φ`, and its limit field is
  `isLimitQuotientRelationConeExtend`. The finiteness fields are listed in the proofs below.

Base change of a single action (still in namespace `ActionDiagram`). Let
`t : D ⟶ (Functor.const I).obj F`, `q : Q ⟶ F.U` with `[Etale q]`, and `B : Action F q`.

- `ofComparison t B : ActionDiagram D` (with `@[simps]` lemmas) has points
  `objectDiagram D t`, so `(ofComparison t B).points.obj i = pullback (t.app i).objMap q`, i.e.
  `(D i).U ×_{F.U} Q`. Its structure maps are `objectMap D t i`, and its action at `i` is
  `pullbackAction (t.app i).isCartesian (object_isPullback D t i) B`, the pullback of `B` along
  `t.app i`. The pullback squares are `isPullback_objectDiagram_map`.
- `ActionCone.ofComparison t B m hm hp A hA : (ofComparison t B).ActionCone c` (with `@[simps]`
  lemmas). Here `c : Cone D`, `m : c.pt ⟶ F` with `hm : ∀ i, c.π.app i ≫ t.app i = m`,
  `hp : IsPullback k p q m.objMap` for `k : P ⟶ Q` and `p : P ⟶ c.pt.U` with `[Etale p]`, and
  `A : Action c.pt p` with `hA : IsEquivariant m.isCartesian p q k hp.w.symm A B`. Its point is
  `P` with structure map `p` and action `A`. Its legs are the legs
  `(objectCone D t c m hm hp).π.app i` of the Library object cone.
- `overComparison D j : Over.forget j ⋙ D ⟶ (Functor.const (Over j)).obj (D.obj j)` (with
  `@[simps]` lemmas) has component `D.map X.hom` at `X : Over j`.
  `whisker_overComparison D c j X : (c.whisker (Over.forget j)).π.app X ≫
  (overComparison D j).app X = c.π.app j`. Thus a cone `c` of `D` restricts to a cone of
  `Over.forget j ⋙ D` that satisfies the hypothesis `hm` with `m = c.π.app j`. Mathlib provides
  the instance that `Over j` is cofiltered when `I` is.

## Proofs

- `isPullback_pairObjMap`. Uniqueness: two points of `pullback π' π'` with the same image under
  `pairObjMap w` and the same first component have the same second component, because the second
  components have the same image under `k` and under `π'` (the latter through the first
  component and `pullback.condition`), and `hk` is a pullback. Existence: from a point `z` of
  `pullback π π` and a point `b` of `P'` with `b ≫ k = z ≫ pullback.fst π π`, the second
  component of the lift is `hk.lift (z ≫ pullback.snd π π) (b ≫ π')`.
- `isEquivariant_pairObjMap`. Both components of the equivariance equation reduce, through
  `pairMap_fst`, `pairMap_snd` and `pairObjMap_fst`, `pairObjMap_snd`, to the equivariance of
  `k` (`act_naturality`), followed by `act_precomp` and `act_congr`.
- `quotientObjMap`, `quotientRelMap` are `SchemeQuotient.map` for the cartesian morphisms of
  action relations given by `hA` and by `isEquivariant_pairObjMap hA`. `q_…`, `isPullback_…` and
  `isAffineHom_quotientObjMap` are `SchemeQuotient.q_map`, `isPullback_map` and
  `isAffineHom_map`. The compatibilities with `quotientS` and `quotientT` are checked after
  precomposition with the epimorphism `Q₂'.q` (`SchemeQuotient.hom_ext`), using `q_quotientS`,
  `q_quotientT`, `pairObjMap_fst` and `pairObjMap_snd`.
- `isPullback_quotientRelMap`. The square commutes by `quotientRelMap_quotientS`. We use the
  Library criterion `isPullback_of_exists_local`. It needs uniqueness of lifts and their existence
  after an effective epimorphism.
  Uniqueness: let `φ, φ' : T ⟶ Q₂'.M` have equal images under `quotientRelMap` and under
  `A'.quotientS`. Let `e` be the base change of `Q₂'.q` along `φ`. It is an epimorphism, and
  `φ` lifts after `e` to a point `x` of `pullback π' π'`. The pullback square
  `A'.isPullback_quotientS` gives a lift `y` of `e ≫ φ'` with the same first component as `x`.
  Then `x = y`: by `isPullback_pairObjMap` it suffices that their images under `pairObjMap w`
  agree. This holds by `A.isPullback_quotientS`, since these images have equal first components
  and equal images in `Q₂.M` (by `q_quotientRelMap` and the hypothesis on `φ, φ'`). Cancelling
  `e` gives `φ = φ'`.
  Existence: given `a : T ⟶ Q₂.M` and `b : T ⟶ Q'.M` with `a ≫ A.quotientS = b ≫
  quotientObjMap`, let `e` be the base change of the étale surjection `Q'.q` along `b`. It is an
  effective epimorphism, and `b` lifts after `e` to `b' : _ ⟶ P'`. The square
  `A.isPullback_quotientS` gives `z` in `pullback π π` with first component `b' ≫ k` and
  `z ≫ Q₂.q = e ≫ a`. `isPullback_pairObjMap` then gives `z'` in `pullback π' π'` with
  `z' ≫ pairObjMap w = z` and first component `b'`. The point `z' ≫ Q₂'.q` is the required
  local lift.
- `isCartesianHom_quotientRelation` combines `quotientRelMap_quotientT` (target compatibility) and
  `isPullback_quotientRelMap` (the source square), which is the Library definition of a cartesian
  morphism.
- `relationDiagram`, `relationCone`, `quotientRelationDiagram`, `quotientRelationCone`. The
  functor and naturality laws are checked with `CartesianMorphism.ext`. For action relations the
  arrow maps are maps into `pullback`, compared componentwise (`pullback.hom_ext`). For quotient
  relations both maps are compared after precomposition with the quotient maps
  (`SchemeQuotient.hom_ext`), using `q_quotientObjMap`, `q_quotientRelMap` and the identities
  `pairObjMap (proj_w (𝟙 i)) = 𝟙`, `pairObjMap (proj_w (a ≫ b)) = pairObjMap (proj_w a) ≫
  pairObjMap (proj_w b)`, and `pairObjMap (T.leg_w i) ≫ pairObjMap (A.proj_w a) =
  pairObjMap (T.leg_w j)`, each proved componentwise.
- `isLimitRelationConeObject`. We use `IsLimit.ofExistsUnique`. Fix `j₀ : I`. A cone `S` over
  the points gives, through the maps `A.proj i`, a cone over the object schemes of `D`, and
  hence, by `hc`, a map `u : S.pt ⟶ c.pt.U`. The pullback square `T.isPullback j₀` gives
  `m : S.pt ⟶ T.P` with `m ≫ T.leg j₀ = S.π.app j₀` and `m ≫ T.proj = u`. For any `i`, take
  `k = min i j₀`. Then `m ≫ T.leg k = S.π.app k` by the pullback square
  `A.isPullback (k ⟶ j₀)`, so `m ≫ T.leg i = S.π.app i` by `T.leg_comp`. Uniqueness follows
  from `T.isPullback j₀` and `hc.hom_ext`.
- `isLimitQuotientRelationConeOfIsLimit`. Transport the Library limit
  `SchemeQuotient.isLimitQuotientCone Q (A.relationCone T) Qc hP` along `quotientFunctorIso` and
  the identity isomorphism of cone points (`IsLimit.equivOfNatIsoOfIso`).
  `isLimitQuotientRelationCone` composes this with `isLimitRelationConeObject`.
- `isLimitQuotientRelationConeExtend`. `IsLimit.ofIsoLimit` with the cone isomorphism whose
  point component is `(asIso φ.objMap).symm`. The legs agree because the object map of a
  composite is the composite of the object maps (`comp_objMap`).
- `finiteTypeCartesianSystem`. The finiteness fields are the lemmas of the imported module at each
  level: `object_compact` is `compactSpace_quotientRelation_U`, `object_finiteType` is
  `locallyOfFiniteType_quotientRelation_U`, `relation_compact` is
  `compactSpace_quotientRelation_R` (the affine `A.proj i` is quasi-compact),
  `relation_quasiSeparated` is `quasiSeparatedSpace_quotientRelation_R`, and
  `source_isSeparated` is `isSeparated_quotientRelation_s`. `objectMap_isAffine` is
  `isAffineHom_quotientRelationDiagram_map`. It uses `hD` and the pullback square
  `A.isPullback a` to make `A.points.map a` affine (`MorphismProperty.of_isPullback`), and then
  `isAffineHom_quotientObjMap`.
- `isEquivariant_pullbackAction_of_comp`. The pulled back action map is the Library
  `pullbackMap h₂ hp B.map B.over`, so the claim is an equation of maps into `P`. It is checked on
  the two projections of the pullback square `hp`. On the projection `k`: the arrow map of `h₁`
  for `l` followed by the arrow map of `h₂` for `k` is the arrow map of `h` for `k'`
  (componentwise, by `hg` and `hk`). Then `pullbackMap_comparison` and the equivariance `hA`
  give the equation. On the projection `p`: both sides equal `pullback.fst E'.s p' ≫ E'.t ≫ f₁`,
  by `w` and `A.over` on one side, and by `pullbackMap_over`, `arrowMap_fst` and the first
  condition `h₁.1` of the cartesian morphism on the other.
- The naturality lemmas of `Action.CartesianSystem` are the naturality of `t` (whose target is
  constant, so the right-hand composite is an identity), of `pointComparison` and of the Library
  projection `TargetLimit.projection`. `isPullback_objectDiagram_map` is pullback pasting
  (`IsPullback.of_right`). The square for level `i` (`object_isPullback D t i`) is rewritten,
  using the two naturality lemmas, as the composite of the square in question with the square
  for level `j`, and the latter is a pullback.
- `ofComparison`. Étaleness of `objectMap D t i` is the base change of the étale `q`. The
  equivariance of the transition map `(objectDiagram D t).map a` is
  `isEquivariant_pullbackAction_of_comp` with `h₁ = (D.map a).isCartesian`,
  `h₂ = (t.app j).isCartesian` and `h = (t.app i).isCartesian`, applied to the Library
  equivariance `pullbackAction_isEquivariant` of the pulled back action at `i`.
- `ActionCone.ofComparison`. The legs and their equations are the Library lemmas
  `objectCone_π_object`, the cone condition of `objectCone`, and `objectCone_isPullback`.
  Equivariance of each leg is `isEquivariant_pullbackAction_of_comp` with
  `h₁ = (c.π.app i).isCartesian`, `h₂ = (t.app i).isCartesian` and `h = m.isCartesian`, applied
  to `hA`, with `hg` from `hm i` and `hk` from `objectCone_π_point`.
- `overComparison`. Naturality is functoriality of `D` together with the commuting triangle
  `Over.w` of a morphism over `j`. `whisker_overComparison` is the cone condition `c.w X.hom`.

## Provenance and relation to the literature

Provenance: derived. The proof of Stacks, Limits of Algebraic Spaces, Proposition 70.8.1
(Tag 07SU) sets `W_i = W_0 ×_{U_0} U_i` and notes `W = lim W_i`. It then uses the étale
equivalence relations `W_i ×_{U_i} W_i`. It proves that the squares formed by the source maps
`s_i` for `i ≥ i'` (its diagram 70.8.1.1) are cartesian, because
`(W_{i'} ×_{U_{i'}} W_{i'}) ×_{U_{i'}} U_i = W_i ×_{U_i} W_i`. In the FL task the algebraic space
`U_i` is presented by an étale equivalence relation `D i`. `W_i` is the quotient
`O i = P i / D i` of an action of `D i` on `P i = W_i ×_{U_i} (D i).U`, and
`W_i ×_{U_i} W_i` is the quotient relation of the imported module. The base change formula of
the source corresponds here to the pullback squares `A.isPullback a` of the actions. With them,
`isCartesianHom_quotientRelation` proves that the transition maps of the quotient relations are
cartesian, which is diagram 70.8.1.1 for this part of `R_i`. The induced square of quotients is
an instance of Stacks, Groupoid Schemes, Lemma 39.20.7 (Tag 07S3). `isLimitQuotientRelationCone`
is the statement `W = lim W_i` for the quotient schemes, deduced from the limit of the object
schemes of the presentations. The finiteness fields are the hypotheses that the proof of 07SU
records for `W_i` and `W_i ×_{U_i} W_i`: finite type over `ℤ`, quasi-compactness, and affine
transition morphisms. The packaging (`ActionDiagram`, `ActionCone`, explicit quotients `Q`,
`Q₂`, `Qc`, `Q₂c`, and the comparison `φ`) is internal. It follows the input format
`FiniteTypeCartesianSystem` of the FL task's induction (Library module
`EtaleEquivalenceRelationFiniteTypeSystem`).

The base change part corresponds to the definition `W_i = W_0 ×_{U_0} U_i` in the same proof of
07SU. With `D` restricted to `Over j` and `t = overComparison D j`, the points of
`ofComparison t B` are `(D i).U ×_{(D j).U} Q`, the base change of the level-`j` data to the
levels over `j`. `ActionCone.ofComparison` records that `W = W_0 ×_{U_0} U` is the base change
at the cone point. The lemma `isEquivariant_pullbackAction_of_comp` and the naturality lemmas
are internal.

`ActionDiagram.overComparison` reuses the existing
`CartesianDiagram.comparison`; both have component `D.map X.hom`.

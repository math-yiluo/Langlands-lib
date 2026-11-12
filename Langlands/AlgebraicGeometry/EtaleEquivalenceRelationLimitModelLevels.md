# Equivalence-relation laws at the stages of an affine limit

Supporting module for the proof of
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.LimitModelExistence`
(`EtaleEquivalenceRelationLimitModelProof.lean`). All declarations live in the namespace
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.LimitModel`.

Provenance: internal infrastructure written for this proof. It carries out the step of the
existence argument in the proof of Stacks Project Lemma 70.7.1 (Tag 07SK), cited by the
target statement's Markdown, in which the laws of the étale equivalence relation descend
to a stage. The formulation as factorizations of base changed models (`Fact`, `LevelLaws`)
is specific to this development and is not taken from a source.

## Setting

Throughout, `a : X ⟶ S` and `b : Y ⟶ S` are two models over a base `S`, and
`ft fs : Y ⟶ X` are maps over `S` (`wt : ft ≫ a = b`, `ws : fs ≫ a = b`). For a base
change `q : T ⟶ S`, the Library map `AffineLimit.baseChangeMap b a ft wt q` is the induced
map `pullback q b ⟶ pullback q a`, and similarly for `fs`. A stage of a diagram
`D : I ⥤ Scheme` over `S` is described by a natural transformation
`t : D ⟶ (Functor.const I).obj S`, and the limit cone `c` maps to `S` by `p` with
`c.π.app i ≫ t.app i = p`.

## Contents

- The module reuses the public `Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp`
  from `Langlands.AbelianScheme.TorsionFiniteEtale`: if `f ≫ g` is locally of finite
  presentation and `g` is locally of finite type, then `f` is locally of finite presentation.
  Its proof reduces on affine opens to `RingHom.FinitePresentation.of_comp_finiteType`.

### Pointwise laws

- `Laws t s` for `t s : R ⟶ U`: for every scheme `T`, the pair `(t, s)` is injective on
  `T`-points, every point of `U` gives a reflexive point of `R`, every point of `R` has a
  symmetric partner, two composable points have a composite, and `t`, `s` are étale.
- `laws_of E`: every `EtaleEquivalenceRelation` satisfies `Laws E.t E.s` (injectivity from
  `E.mono_lift`).
- `Laws.relation`: conversely, `Laws t s` builds an `EtaleEquivalenceRelation` with
  object `U`, relation `R` and projections `t`, `s`.
- `Laws.of_iso`: the laws transfer along isomorphisms `R ≅ R'`, `U ≅ U'` compatible with
  both projections.

### Base change along composites

- `baseChangeMap_comp`, `pullMap q r α : pullback (r ≫ q) α ⟶ pullback q α` with its
  projection lemmas, `pullMap_isPullback` (it is a base change of `r`) and
  `pullMap_baseChangeMap_isPullback`.
- `baseChangeMap_comp_left`: a property stable under base change passes from
  `baseChangeMap … q` to `baseChangeMap … (r ≫ q)`.

### Factorizations

- `Fact α β g h q`: after base change along `q`, the map `h : Z ⟶ V` factors through
  `g : W ⟶ V` by a map `pullback q α ⟶ pullback q β` over `T`.
- `Fact.comp`, `Fact.level`: a factorization persists after further base change, hence at
  every later stage (`level_comp : D.map r ≫ t.app j = t.app i`).
- `Fact.descend`: if `α` is quasi-compact and quasi-separated, `β` is locally of finite
  presentation and `g`, `h` lie over a locally finite type `γ`, a factorization over the
  limit already exists at a stage. The proof descends the factorizing map with the Library
  lemma `SchemeLimitModel.exists_level_morphism` and the equation it must satisfy with
  `SchemeLimitModel.eventually_equal`.
- `exists_and_of_mono`: two stage properties that persist at later stages hold together at
  one stage of a cofiltered category.
- `baseChangeMap_level`: a property stable under base change of `baseChangeMap … (t.app j)`
  passes to every later stage.

### Étaleness

- `isOpenImmersion_baseChangeMap_diagonal_iff`: the base change of the diagonal of `f` is
  an open immersion exactly when the diagonal of the base change of `f` is (via
  `AffineLimit.baseChangeMap_square_isPullback`).
- `etale_baseChangeMap_iff`: for `f` locally of finite presentation, the base change of `f`
  is étale iff it is flat and its diagonal is an open immersion
  (`Etale.iff_flat_and_formallyUnramified`).
- `etale_descend`: over an affine base, étaleness over the limit of the base change of a
  finitely presented, quasi-compact, quasi-separated `f` between finitely presented models
  holds at a stage, combining the Library descents `AffineLimit.relativeFlatDescent` and
  `AffineLimit.relativeOpenImmersionDescent`.

### Laws as factorizations of models

- `graph a b ft fs wt ws : Y ⟶ pullback a a` is the pair `(ft, fs)`; `kernel_cond`,
  `kernel_ft`, `kernel_fs`, `pair_cond` record compatibilities of its kernel pair and of
  `pullback fs ft`.
- `LevelLaws a b ft fs wt ws q`: four factorizations (`Fact`) through the graph or the
  diagonal of `b` expressing reflexivity (the diagonal of `a` factors through the graph),
  symmetry (the swapped pair factors through the graph), transitivity (the composite pair
  on `pullback fs ft` factors through the graph) and injectivity (the kernel pair of the
  graph factors through the diagonal of `b`), together with étaleness of both base changed
  maps.
- `levelLaws_iff`: `LevelLaws … q` holds iff the base changed pair
  `(baseChangeMap b a ft wt q, baseChangeMap b a fs ws q)` satisfies `Laws`.
- `LevelLaws.comp`, `LevelLaws.level`: the laws persist after further base change and at
  later stages.
- `levelLaws_descend`: over an affine base `S` with `a`, `b` locally of finite
  presentation, quasi-compact and quasi-separated, and `D` a small cofiltered diagram of
  affine schemes with limit cone `c`, `LevelLaws` along `p` implies `LevelLaws` along
  `t.app i` for some stage `i`. Each of the four factorizations descends by
  `Fact.descend`, each étaleness condition by `etale_descend`, and a common stage is
  obtained from cofilteredness.

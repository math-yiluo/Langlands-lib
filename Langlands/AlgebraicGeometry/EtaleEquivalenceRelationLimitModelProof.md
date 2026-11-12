# Proof of finite-stage descent of étale scheme equivalence relations

The theorem `Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.limitModelExistence`
proves the Library statement
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.LimitModelExistence`
(`EtaleEquivalenceRelationLimitModelStatement.lean`) in every universe `u`, with the
statement unchanged and no additional hypotheses. It uses no algebraic-space model
existence for the relation, no previously supplied stage relation and no assumed descent
of the equivalence-relation laws: the laws are descended in the supporting module
`EtaleEquivalenceRelationLimitModelLevels.lean` (namespace
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.LimitModel`).

The overall route is the scheme part of the existence argument in the proof of Stacks
Project Lemma 70.7.1 (Tag 07SK), cited by the statement: find finitely presented models
of the object and relation schemes at a stage, descend the two projections, and then
descend the laws. The Lean proof below is the implemented route.

## Helper lemmas (namespace `…EtaleEquivalenceRelation.LimitModel`)

- `isPullback_iso_comp`, `isPullback_iso_comp₂`: a pullback square stays a pullback
  square after precomposing its top-left corner (and, in the second form, also its
  bottom-left corner) with isomorphisms compatible with the left edge.
- `overNat D j`, `overIsLimit j hc`, `over_hp`: restricting a cofiltered diagram to the
  stages over `j` (`Over.forget j ⋙ D`) keeps the limit cone a limit
  (`Functor.Initial.isLimitWhiskerEquiv`, since `Over.forget j` is initial), and these
  stages map compatibly to the stage `j` by `D.map k.hom`. The restricted diagram is still
  affine.
- `exists_model_rebase`: a finitely presented, quasi-compact, quasi-separated model
  `a : X ⟶ D.obj j` of `Z` over the limit (a pullback square along `c.π.app j`) gives such
  a model at every stage `k ⟶ j`, by base change along `D.map r`.
- `isAffine_level`: if `pullback (t.app j) a` is affine, so is `pullback (t.app i) a` for
  `i ⟶ j`, since the comparison map is an affine base change of `D.map r` between affine
  schemes.

## Core lemma `exists_stage`

Setting: a small cofiltered diagram `D` of affine schemes over an affine base `S`
(`t : D ⟶ const S`), a limit cone `c` with `p : c.pt ⟶ S`, finitely presented
quasi-compact quasi-separated models `a : X ⟶ S`, `b : Y ⟶ S`, maps `ft fs : Y ⟶ X`
over `S`, and an étale equivalence relation `E` with affine `E.U` whose object and
relation schemes are the base changes of `a` and `b` along `p` (squares `hU`, `hR`),
with `E.t`, `E.s` induced by `ft`, `fs` (`ht`, `hs`).

1. The pullback squares give isomorphisms `eU : E.U ≅ pullback p a` and
   `eR : E.R ≅ pullback p b` under which `E.t`, `E.s` become
   `baseChangeMap b a ft wt p` and `baseChangeMap b a fs ws p`.
2. By `laws_of E`, `Laws.of_iso` and `levelLaws_iff`, `LevelLaws a b ft fs wt ws p`
   holds. `levelLaws_descend` gives a stage where `LevelLaws` holds along `t.app i₁`.
3. `pullback p a ≅ E.U` is affine, so the Library lemma `AffineLimit.exists_isAffine_level`
   gives a stage `i₂` where `pullback (t.app i₂) a` is affine.
4. At a common stage `k` (cofilteredness, `LevelLaws.level`, `isAffine_level`),
   `levelLaws_iff` and `Laws.relation` give the étale equivalence relation `Ei` with
   object `pullback (t.app k) a` and projections the base changes of `ft`, `fs`.
5. The witnesses are `bi = pullback.fst (t.app k) a` (a base change of `a`, hence locally
   of finite presentation), `fU = eU.hom ≫ (cone …).π.app k` and
   `fR = eR.hom ≫ (cone …).π.app k`. Then `Ei.t ≫ bi = Ei.s ≫ bi = pullback.fst (t.app k) b`
   is a base change of `b`, hence quasi-compact. The object square is the Library square
   `cone_π_isPullback` transported by `isPullback_iso_comp`; the relation square commutes
   by `cone_baseChangeMap_isPullback` with the first projections, and is a pullback with
   the second projections by the same Library lemma transported by
   `isPullback_iso_comp₂`. This is `E.IsCartesianHom Ei fU fR`.

## Main theorem `limitModelExistence`

Given the data of the statement:

1. `c.pt` is affine (`Scheme.isAffine_of_isLimit`). The map `pullback.lift E.t E.s` into
   `pullback b b` is a monomorphism by the injectivity law, so `E.t ≫ b` is
   quasi-separated; it is locally of finite presentation (étale `E.t` composed with `b`)
   and quasi-compact by hypothesis. The map `b` between affine schemes is quasi-compact
   and quasi-separated.
2. The Library lemma `AlgebraicSpace.exists_schemeModel_of_affineLimit`, applied to
   `b` and to `E.t ≫ b`, gives finitely presented quasi-compact quasi-separated models of
   `E.U` and `E.R` at stages `j₁`, `j₂`. `exists_model_rebase` moves both to a common
   stage `j₀`, with models `a : X ⟶ D.obj j₀` and `bR : Y ⟶ D.obj j₀`.
3. On the stages over `j₀` (`overIsLimit`), the maps `E.t`, `E.s`, transported through
   the pullback isomorphisms, are morphisms of the base changed models over the limit
   (`SchemeLimitModel.LimitHom`). `SchemeLimitModel.exists_level_morphism` descends both
   to level morphisms, which are restricted to a common stage `k` over `j₀`; their values
   over the limit are the original maps (`toLimit`, `restrict`).
4. At the stage `k.left`, the base changes of `a` and `bR` along `D.map k.hom` are
   finitely presented quasi-compact quasi-separated models over the affine scheme
   `D.obj k.left`, and `E.U`, `E.R` are their base changes along `c.π.app k.left`
   (`cone_π_isPullback`). The descended maps `τ`, `σ` between these models induce `E.t`,
   `E.s` (`toLimit_square`).
5. `exists_stage`, applied to the diagram of stages over `k.left` with base
   `S = D.obj k.left`, gives a stage `i` over `k.left` and all required data; the stage
   `i.left` of `I` is the answer, since the cone leg of the restricted cone at `i` is
   `c.π.app i.left`.

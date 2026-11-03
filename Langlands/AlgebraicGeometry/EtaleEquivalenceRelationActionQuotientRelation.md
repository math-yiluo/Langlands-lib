# Quotient relations of actions of étale equivalence relations

Module `Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionQuotientRelation`. It imports
the Library modules `EtaleEquivalenceRelationSchemeQuotientMap` and
`EtaleEquivalenceRelationActionMorphism`.

This module is the second generic bridge module ("Module B") for the first-level step of
absolute Noetherian approximation (FL task 8d02331e, Workers 706 and 416). Through that step it
serves this task (Tag 07VS). The FL task has an étale equivalence relation `H` presenting an
algebraic space `X = H.U / H`. It also has a scheme `P` with an étale map `π : P ⟶ H.U` and an
action of `H` on `P`, so that the quotient `O = P / H` is a scheme étale over `X`. This module
constructs the étale equivalence relation `O ×_X O` on `O` as the quotient
`(P ×_{H.U} P) / H` of the diagonal action. It also records finiteness properties of this
relation.

## Conventions

All schemes live in one universe `u`. `EtaleEquivalenceRelation.{u}` is the Library structure
with `t s : R ⟶ U`, `unit`, `hom_ext`, and fields `mono_lift`, `refl`, `symm`, `trans`,
`etale_t` and `etale_s`. For `π : P ⟶ H.U`, the Library structure `Action H π` has
`map : pullback H.s π ⟶ P` (the action of an arrow `r` on a point `v` with `H.s r = π v`),
with `act r v h` the action of a `T`-point. Its action relation `A.relation` has objects `P`,
arrows `pullback H.s π`, `t := A.map` and `s := pullback.snd H.s π`.
`IsEquivariant`, `arrowMap` and `isCartesianHom_of_isEquivariant` are the Library notions for
equivariant maps between actions. `F.SchemeQuotient` is the Library structure with fields `M`,
`q : F.U ⟶ M`, `isPullback : IsPullback F.t F.s q q`, and instances `Etale q` and
`Surjective q`. `SchemeQuotient.map h Q' Q` is the map of quotients induced by a cartesian
morphism `h` (Library module `EtaleEquivalenceRelationSchemeQuotientMap`).

## Statements

General lemmas in namespace `Langlands.AlgebraicGeometry.EtaleEquivalenceRelation`:

- `exists_of_exists_local hom_ext e x y ρ ht hs`: let `t s : R ⟶ U` be such that morphisms into
  `R` are determined by their composites with `t` and `s`. If `e : T₁ ⟶ T` is an effective
  epimorphism, `x y : T ⟶ U`, and `ρ : T₁ ⟶ R` has `ρ ≫ t = e ≫ x` and `ρ ≫ s = e ≫ y`, then
  some `r : T ⟶ R` has `r ≫ t = x` and `r ≫ s = y`.
- `isCartesianHom_of_isIso α β ht hs`: isomorphisms `α : E.U ⟶ F.U` and `β : E.R ⟶ F.R`
  commuting with `t` and with `s` form a cartesian morphism `IsCartesianHom E F α β`.

In namespace `EtaleEquivalenceRelation.Action`, for `A : Action H π`:

- `pairMap : pullback H.s (pullback.fst π π ≫ π) ⟶ pullback π π` acts by `r` on both
  components of a pair `(v₁, v₂)` with `π v₁ = π v₂ = H.s r`. The lemmas `pairMap_fst`,
  `pairMap_snd` (with `reassoc` forms), `lift_pairMap_fst` and `lift_pairMap_snd` compute its
  components through `A.act`.
- `pairAction : Action H (pullback.fst π π ≫ π)` is the diagonal action, with
  `pairAction_map : A.pairAction.map = A.pairMap`.
- `isEquivariant_pairFst`, `isEquivariant_pairSnd`: the two projections
  `pullback.fst π π`, `pullback.snd π π` are equivariant from `A.pairAction` to `A` (over the
  identity of `H`). `isEquivariant_diagonal`: `pullback.diagonal π` is equivariant from `A` to
  `A.pairAction`. `pairSwap : pullback π π ⟶ pullback π π` exchanges the factors
  (`pairSwap_fst`, `pairSwap_snd`), and `isEquivariant_pairSwap` says it is equivariant for
  `A.pairAction`.
- `isCartesianHom_pairFst`, `isCartesianHom_pairSnd`, `isCartesianHom_diagonal`,
  `isCartesianHom_pairSwap`: the corresponding cartesian morphisms of action relations, with
  arrow maps `arrowMap …`.
- `eq_of_comp_q_eq Q hq hπ`: for `Q : A.relation.SchemeQuotient`, two points `b₁ b₂ : T ⟶ P`
  with `b₁ ≫ Q.q = b₂ ≫ Q.q` and `b₁ ≫ π = b₂ ≫ π` are equal.

For `Q : A.relation.SchemeQuotient` and `Q₂ : A.pairAction.relation.SchemeQuotient`:

- `quotientS A Q Q₂, quotientT A Q Q₂ : Q₂.M ⟶ Q.M` are the maps induced by the first and
  second projection (`SchemeQuotient.map`). They satisfy
  `q_quotientS : Q₂.q ≫ A.quotientS Q Q₂ = pullback.fst π π ≫ Q.q` and
  `q_quotientT : Q₂.q ≫ A.quotientT Q Q₂ = pullback.snd π π ≫ Q.q`, and the squares are
  pullbacks: `isPullback_quotientS : IsPullback (pullback.fst π π) Q₂.q Q.q (A.quotientS Q Q₂)`,
  and `isPullback_quotientT` likewise.
- `quotient_hom_ext ht hs`: two morphisms `x y : T ⟶ Q₂.M` with equal composites with
  `quotientT` and with `quotientS` are equal.
- `quotientDiagonal A Q Q₂ : Q.M ⟶ Q₂.M`, with `quotientDiagonal_s` and `quotientDiagonal_t`
  (both composites are `𝟙 Q.M`).
- `quotientSwap A Q₂ : Q₂.M ⟶ Q₂.M`, with `quotientSwap_s : quotientSwap ≫ quotientS =
  quotientT` and `quotientSwap_t : quotientSwap ≫ quotientT = quotientS`.
- `quotient_trans r r' h`: for `r r' : T ⟶ Q₂.M` with `r ≫ quotientS = r' ≫ quotientT`, some
  `r'' : T ⟶ Q₂.M` has `r'' ≫ quotientT = r ≫ quotientT` and
  `r'' ≫ quotientS = r' ≫ quotientS`.
- `quotientRelation A Q Q₂ [Etale π] : EtaleEquivalenceRelation.{u}` (the selected
  declaration) has `U := Q.M`, `R := Q₂.M`, `t := A.quotientT Q Q₂`, `s := A.quotientS Q Q₂`.
  The `simp` lemmas `quotientRelation_s` and `quotientRelation_t` unfold `s` and `t`.
- `quotientS_eq h` and `quotientT_eq h`: a morphism `s' : Q₂.M ⟶ Q.M` with
  `Q₂.q ≫ s' = pullback.fst π π ≫ Q.q` equals `quotientS`. Likewise for `t'` and `quotientT`
  with `pullback.snd π π`.

Finiteness properties, under the hypotheses named:

- `isAffineHom_q₂`: `[IsAffineHom Q.q] → IsAffineHom Q₂.q`.
- `isAffineHom_quotientS`, `isAffineHom_quotientT`: `[IsAffineHom π] → [IsAffineHom Q.q] →`
  the map is affine.
- With `[Etale π]`:
  - `isSeparated_quotientRelation_s`: `[IsAffineHom π] → [IsAffineHom Q.q] →
    IsSeparated (A.quotientRelation Q Q₂).s`.
  - `compactSpace_quotientRelation_U`: `[CompactSpace P] → CompactSpace (…).U`.
  - `locallyOfFiniteType_quotientRelation_U`: `[LocallyOfFiniteType (terminal.from P)] →
    LocallyOfFiniteType (terminal.from (…).U)`.
  - `compactSpace_quotientRelation_R`: `[CompactSpace P] → [QuasiCompact π] →
    CompactSpace (…).R`.
  - `quasiSeparatedSpace_quotientRelation_R`: `[IsAffineHom Q.q] →
    [QuasiSeparatedSpace (pullback π π)] → QuasiSeparatedSpace (…).R`.

## Proofs

- `exists_of_exists_local`. Two morphisms `g₁ g₂ : W ⟶ T₁` with `g₁ ≫ e = g₂ ≫ e` give
  `g₁ ≫ ρ = g₂ ≫ ρ` by `hom_ext`, because `ρ ≫ t` and `ρ ≫ s` factor through `e`. So `ρ`
  descends along `e` (`EffectiveEpi.desc`). The two equations hold after cancelling the
  epimorphism `e`.
- `isCartesianHom_of_isIso`. The `s`-square is a pullback because its horizontal maps are
  isomorphisms (`IsPullback.of_horiz_isIso`).
- `pairMap` is `pullback.lift` of the two actions on the components; they lie over the same
  point because both equal `H.t r` after `π` (`act_over`). The axioms of `pairAction` are
  checked componentwise with `pullback.hom_ext`, using `act_congr`, `act_unit`, `act_assoc`
  and `act_precomp` of `A`.
- The equivariance lemmas unfold `IsEquivariant` to an equation of morphisms out of
  `pullback H.s _`. They follow from `pairMap_fst`, `pairMap_snd`, the components of the
  diagonal and of `pairSwap`, and `act_congr`. The cartesian morphisms are the Library lemma
  `isCartesianHom_of_isEquivariant`.
- `eq_of_comp_q_eq`. By `Q.isPullback` the pair `(b₁, b₂)` lifts to an arrow `ρ` of the action
  relation, so `b₁ = A.act (ρ ≫ pullback.fst H.s π) b₂`. The arrow `ρ ≫ pullback.fst H.s π`
  of `H` has both endpoints `b₂ ≫ π` (the target by `A.over` and `hπ`), so it is
  `b₂ ≫ π ≫ H.unit` (`H.hom_ext`). Then `act_unit` gives `b₁ = b₂`.
- `quotientS`, `quotientT`, `q_quotientS`, `q_quotientT`, `isPullback_quotientS`,
  `isPullback_quotientT` are `SchemeQuotient.map`, `q_map` and `isPullback_map` applied to the
  cartesian projections.
- `quotient_hom_ext`. Let `e : pullback x Q₂.q ⟶ T` be the base change of the surjective étale
  `Q₂.q`, an epimorphism, with lift `x'` of `e ≫ x` to `pullback π π`. Using `hs` and the
  pullback square `isPullback_quotientS`, the pair `(x' ≫ pullback.fst π π, e ≫ y)` lifts to
  `y' : _ ⟶ pullback π π` with `y' ≫ Q₂.q = e ≫ y`. The points `x'` and `y'` have the same first
  component. Their second components have the same image in `Q.M` (by `ht`) and the same image
  in `H.U`, so they are equal by `eq_of_comp_q_eq`. Hence `x' = y'`, so `e ≫ x = e ≫ y`, and
  `x = y` after cancelling `e`.
- `quotientDiagonal_s`, `quotientDiagonal_t`, `quotientSwap_s`, `quotientSwap_t`,
  `quotientS_eq`, `quotientT_eq` are checked after precomposition with the quotient map
  (`SchemeQuotient.hom_ext`), using `q_map` and the components of `pullback.diagonal` and
  `pairSwap`.
- `quotient_trans`. As in `quotient_hom_ext`, with `e` the base change of `Q₂.q` along `r` and
  a lift `x'` of `e ≫ r`. The equation `h` and `isPullback_quotientT` give
  `y' : _ ⟶ pullback π π` with `y' ≫ Q₂.q = e ≫ r'` and second component equal to the first
  component of `x'`. The pair `z := (y' ≫ pullback.fst π π, x' ≫ pullback.snd π π)` lies in
  `pullback π π`. Its class `z ≫ Q₂.q` has the required endpoints after `e`, so
  `exists_of_exists_local` (with `quotient_hom_ext`) descends it along the effective
  epimorphism `e`.
- `quotientRelation`. `mono_lift` is `quotient_hom_ext`, applied to the two components of
  `prod.lift`. Reflexivity uses `quotientDiagonal`, symmetry uses `quotientSwap` and
  transitivity is `quotient_trans`. `quotientT` and `quotientS` are étale by Mathlib's
  descent of étaleness along the fppf cover `Q.q : P ⟶ Q.M`
  (`MorphismProperty.of_isPullback_of_descendsAlong` with the squares `isPullback_quotientT`
  and `isPullback_quotientS`). In these squares `Q.q` is the arrow along which `quotientT`
  and `quotientS` are base changed, so their base changes along `Q.q` are
  `pullback.snd π π` and `pullback.fst π π`, which are étale because `π` is; `Q₂.q` is the
  other projection of each square.
- Finiteness. `isAffineHom_q₂` is `SchemeQuotient.isAffineHom_q` for the cartesian first
  projection. `isAffineHom_quotientS` and `isAffineHom_quotientT` are
  `SchemeQuotient.isAffineHom_map`, since the projections of `pullback π π` are base changes of
  the affine `π`. An affine morphism is separated. The compactness, finite-type and
  quasi-separation statements are the Library instances `SchemeQuotient.compactSpace`,
  `SchemeQuotient.locallyOfFiniteType_terminal` and `SchemeQuotient.quasiSeparatedSpace` for
  `Q` and `Q₂`; compactness of `pullback π π` uses that `pullback.fst π π` is quasi-compact.

## Provenance and relation to the literature

Provenance: derived. In the proof of Stacks, Limits of Algebraic Spaces, Proposition 70.8.1
(Tag 07SU), `W_i` is a scheme étale over an algebraic space `U_i`, and the proof uses the
étale equivalence relation `W_i ×_{U_i} W_i` on `W_i` with its two étale projections. In the
FL task `U_i` is presented by an étale equivalence relation `H` and `W_i` is the quotient
`O = P / H` of an action of `H` on `P = W_i ×_{U_i} H.U`. Then
`O ×_X O ×_X H.U = P ×_{H.U} P`, so `O ×_X O` is the quotient `(P ×_{H.U} P) / H` of the
diagonal action. `quotientRelation` constructs this relation directly from scheme quotients,
without algebraic spaces. The pullback squares `isPullback_quotientS` and
`isPullback_quotientT` are instances of Stacks, Groupoid Schemes, Lemma 39.20.7 (Tag 07S3):
a cartesian morphism of equivalence relations gives a fibre square of quotients. The equivalence
relation axioms follow the description of `T`-points of quotients in Lemma 39.20.4
(Tag 045Y): points are related locally on `T`. This is the role of
`exists_of_exists_local`. The finiteness lemmas give the hypotheses on `R_i` used in the proof
of 07SU (quasi-compactness of `W_i ×_{U_i} W_i`, finite type over `ℤ`). The packaging
(`pairAction`, the selected `quotientRelation` with explicit quotients `Q` and `Q₂`) is internal
and follows the interface agreed with the FL task.

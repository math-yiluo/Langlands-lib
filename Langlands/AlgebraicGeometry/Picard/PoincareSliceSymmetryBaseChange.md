# Slice symmetry of the Poincaré bundle descends along a change of base

Module `Langlands.AlgebraicGeometry.Picard.PoincareSliceSymmetryBaseChange`.

## Setting

Throughout, `universality : PicardZeroUniversalBaseChangeStatement.{u}` is a hypothesis
(it is not assumed anywhere else), `b : S' ⟶ S` is a morphism of schemes, `A` is an abelian
scheme over `S` with a dual scheme (`hA : HasDualScheme A`), and
`A' = (baseChange b).obj A` is the changed abelian scheme. Its dual is the one given by
`hasDualScheme_baseChange universality b A hA`. `D = dualScheme A hA`, `D'` is the dual of `A'`,
and `e = dualSchemeBaseChangeIso universality b A hA _ : D ×_S S' ≅ D'` is the Library's
canonical comparison. `P`, `P'` are the line bundles underlying `poincareFamily A hA` and
`poincareFamily A' _` (parameter first).

## Main result

`Langlands.AbelianScheme.poincareSliceSymmetric_of_baseChange`: for
`f : A.X ⟶ D`, `T' : Over S'` and a point `t' : T' ⟶ A'.X`, if
`PoincareSliceSymmetric A' _ (dualBaseChangeMap A hA universality b f) t'` holds, then
`PoincareSliceSymmetric A hA f ((Over.map b).map t' ≫ baseChangeParameterMap b A.X)`.

Here `dualBaseChangeMap A hA universality b f = (Over.pullback b).map f ≫ e.hom` is the changed
map `f' : A' ⟶ D'`, and `(Over.map b).map t' ≫ baseChangeParameterMap b A.X : T ⟶ A`, with
`T = (Over.map b).obj T'` (that is, `T'` viewed over `S` through `b`), is the image of `t'` in
`A`: on underlying schemes it is `t'` followed by the projection `A ×_S S' ⟶ A`. In words:
if `P'(f' t', a') ≅ P'(f' a', t')` on `T' ×_{S'} A'`, then `P(f t, a) ≅ P(f a, t)` on `T ×_S A`.

## Auxiliary declarations

- `poincareBaseChangeForgetPullbackIso`: `P'` is isomorphic to the pullback of `P` along
  `(relativeSpace A'.X.hom).map e.inv ≫ baseChangeFamilySpaceMap b A D`, the map
  `D' ×_{S'} A' ⟶ (D ×_S S') ×_{S'} A' ⟶ D ×_S A`. It inserts `e.inv ≫ e.hom = 𝟙`, then
  applies the Library's `dualSchemeBaseChangePullbackIso` (the rigidified isomorphism that
  characterizes `e`) and `poincareFamilyBaseChangeForgetIso`.
- `baseChangePoincareSpace_comp_eq`: a map `ψ'` into `D' ×_{S'} A'`, followed by that map, is a
  given `ψ` into `D ×_S A` as soon as the two projections agree (`pullback.hom_ext`).
- `baseChangePoincarePullbackIso`: from those two projection equations, an isomorphism
  `ψ'^* P' ≅ ψ^* P` (`poincareBaseChangeForgetPullbackIso` composed with
  `LineBundle.pullbackCompEqIso`).
- `dualBaseChangeMap_left_inv_fst` (with `@[reassoc]`): `f'` followed by `e.inv` and the
  projection `D ×_S S' ⟶ D` equals the projection `A ×_S S' ⟶ A` followed by `f`, on
  underlying schemes.
- `map_comp_baseChangeParameterMap_left` (with `@[reassoc]`, proved by `rfl`): the underlying
  morphism of the image point is `t'.left` followed by the projection `A ×_S S' ⟶ A`.

## Proof of the main result

Let `φ = familyBaseChangeSpaceMap b A T' : T' ×_{S'} A' ⟶ T ×_S A`. It is an isomorphism
(`familyBaseChangeSpaceIso`), so by `LineBundle.nonempty_iso_of_pullback_iso` it suffices to
give an isomorphism between the pullbacks along `φ` of the two slices on `T ×_S A`. Each of these
is identified (with `LineBundle.pullbackCompEqIso`) with the pullback of `P` along
`φ ≫ pair map`, and `baseChangePoincarePullbackIso` identifies that with the corresponding slice
of `P'` on `T' ×_{S'} A'`. The hypothesis supplies the isomorphism between the two slices of
`P'`, which closes the chain.

There are four projection equations, one for each of the two coordinates of the two pair maps.
They follow from `pairOver_left`, `pullback.lift_fst`/`pullback.lift_snd`,
`familyBaseChangeSpaceMap_fst`/`familyBaseChangeSpaceMap_snd`, and the two helper lemmas above.
The objects `A'.X.left` and `pullback A.X.hom b` are equal only after unfolding `baseChange`,
which `simp` and `rw` do not do. The proof therefore uses `erw` for the pullback-lift
projections and closes the remaining associativity steps with explicit `exact` terms.

## Provenance and purpose

This is an internal auxiliary result for the proof of
`Langlands.AbelianScheme.PolarizationDiagonalMumfordStatement`
(Mumford, Fogarty, Kirwan, *Geometric Invariant Theory*, 3rd ed., Prop. 6.10). The Lean
proof of that statement in this contribution (not GIT's proof) checks the slice symmetry of `PoincareSliceSymmetric` at field-valued points after a base change,
and this module brings the property back down to the original base. It is a formal consequence
of the compatibility of the Poincaré bundle with base change (the Library's
`DualSchemeBaseChange` and `PoincareBaseChange`) and claims nothing beyond the stated transport.

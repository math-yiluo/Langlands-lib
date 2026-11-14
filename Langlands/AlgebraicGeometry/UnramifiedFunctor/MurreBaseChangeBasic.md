# Base change of Murre's conditions other than (F2)

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreBaseChangeBasic`
shows that nine of the ten conditions of `MurreConditions` pass from a presheaf
`F : (Over S)ᵒᵖ ⥤ Type v` to its base change
`baseChange g F = (Over.map g).op ⋙ F` along any `g : S' ⟶ S`. All results are
in the namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.BaseChange`.
In each one, the condition on the base change follows from the same condition
on `F`.

## Transport for algebras

Fix `f : Spec A ⟶ S'` and an `A`-algebra `B`.

- `mapAlgebraOverIso g f B : (Over.map g).obj (algebraOver f B) ≅ algebraOver (f ≫ g) B`
  is the identity of `Spec B` on underlying schemes.
- `equiv g F f B : (baseChange g F).obj (op (algebraOver f B)) ≃ F.obj (op (algebraOver (f ≫ g) B))`
  is `F` applied to that isomorphism.
- `equiv_map` and `equiv_base` show that `equiv` commutes with the maps
  `algHomOver` (from `A`-algebra maps) and `algebraOverBase` (the structure
  map to `Spec A`). In both proofs, the needed equation between morphisms of
  `Over S` is checked on the `left` components with `simp`. It is then moved
  through `F` with `Functor.map_comp_apply` in a term-mode `calc`.
- From these, `equiv` intertwines `restrictQuotient`
  (`equiv_restrictQuotient`). It therefore identifies `LiftsTo` and
  `NoLargerLift` for the base change with the same predicates for `F` over
  `f ≫ g` (`liftsTo_iff`, `noLargerLift_iff`).

## The conditions

- `smallValues`: `(baseChange g F).obj (op T) = F.obj (op ((Over.map g).obj T))`.
- `nilpotentInjective`, `valuativeSeparation`: injectivity of
  `(baseChange g F).map (algebraOverBase f _).op` follows from injectivity of
  `F.map (algebraOverBase (f ≫ g) _).op`. Apply `equiv` and `equiv_base`.
- `adicLimits`: apply the condition for `F` at `f ≫ g`. Injectivity follows
  as above. A compatible family `s` for the base change is sent by `equiv` to a
  compatible family for `F` (`equiv_map`). The limit element for `F` is also
  one for the base change, by `equiv_base` and the injectivity of `equiv`.
- `artinianLifting`, `oneDimensionalLifting`, `genericNonLifting`: apply the
  condition for `F` at `f ≫ g` to the transported elements. Transport the
  hypotheses with `equiv_map`, `liftsTo_iff` and `noLargerLift_iff`, and
  transport the conclusions back with `equiv_base` and `noLargerLift_iff`.

## Sheaf conditions

`isSheafFor_ofArrows` is the general step. Let `π i : U i ⟶ T` be a family of
arrows in `Over S'`, and let `π' i : V i ⟶ (Over.map g).obj T` be a family in
`Over S` with isomorphisms `e i : V i ≅ (Over.map g).obj (U i)` such that
`(e i).hom ≫ (Over.map g).map (π i) = π' i`. If `F` satisfies the sheaf
condition for the family `π'`, then `baseChange g F` satisfies it for the
family `π`.

The proof goes through `Presieve.isSheafFor_arrows_iff`. A compatible family
`x` for the base change gives the family `y i = F.map (e i).hom.op (x i)`. To
show `y` is compatible, let `gi : Z ⟶ V i` and `gj : Z ⟶ V j` in `Over S`
agree after `π'`. Form the object `Z'` of `Over S'` on `Z.left`, with the
lifts `gi'` and `gj'` to `Over S'`, and the identity `ε : Z ⟶ (Over.map g).obj Z'`.
Then `gi ≫ (e i).hom = ε ≫ (Over.map g).map gi'`, which reduces compatibility
of `y` to compatibility of `x`. The amalgamation of `y` is the amalgamation of
`x`, since `F.map (e i).hom.op` is injective. Uniqueness carries over in the
same way.

- `zariskiSheaf`: for `T : Over S'` and an open cover `𝒰` of `T.left`, the
  same cover is an open cover of `((Over.map g).obj T).left`. The objects are
  identified by `Over.isoMk (Iso.refl _)`.
- `faithfullyFlatSheaf`: a singleton presieve is written as `ofArrows` over
  `PUnit` (`Presieve.ofArrows_pUnit`). The morphism
  `(Over.map g).map φ` has the same underlying morphism of schemes as `φ`,
  so it is flat, surjective and quasi-compact.

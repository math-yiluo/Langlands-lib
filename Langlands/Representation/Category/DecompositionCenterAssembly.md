# Central elements over a decomposition of a smooth category

Worker 117. Internal helper module for Task 5545 (Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026
(`renard-2026-representations-groupes-reductifs-padiques`), VI.10.4, Theorem,
printed p.212 / PDF p.218). It is used by the conditional reduction
`BernsteinCenterFunctionsReduction`. Renard uses these facts implicitly when he
identifies the centre of `M(G) = ∏_Ω M(G)_Ω` with the product of the centres of
the blocks. The module states them for an arbitrary decomposition in the sense of
the published A.IX predicate `Renard.IsCategoryDecomposition`. None of them is a
separate assertion of Renard, and the module adds no hypothesis to any Library
statement. It builds on the published module
`Langlands.Representation.Category.DecompositionCentralProjectors` (`cofanProjection`,
`comp_cofanComponent`).

## Restriction (any category `C`)

- `catCenterRestrict P z`: for an element `z` of the centre `CatCenter C` (a
  natural endotransformation of the identity functor) and a full subcategory
  given by an object property `P`, the element of `CatCenter P.FullSubcategory`
  with components `ObjectProperty.homMk (z.app X)`. Naturality is that of `z`.
- `catCenterRestrict_app_hom` (simp, `rfl`): the underlying morphism of the
  component at `X` is `z.app X.obj`.
- `catCenterRestrict_app_eq`: if `catCenterRestrict P z = catCenterRestrict P z'`,
  then `z.app X = z'.app X` for every `X` with `P X`.
  *Proof.* Apply `congrArg` to the components at `⟨X, hX⟩` and take underlying
  morphisms.
- `catCenter_ext_of_everyObjectIsCoproduct`: if every object is the vertex of a
  coproduct cofan of objects of the `P i`
  (`Renard.EveryObjectIsCoproductOfComponents P`), two central elements that
  agree on every object of every `P i` are equal.
  *Proof.* Fix `X` with a cofan `(ι j : A j ⟶ X)`, `A j` in `P j`. By
  `Cofan.IsColimit.hom_ext` it suffices that `ι j ≫ z.app X = ι j ≫ z'.app X`.
  Naturality rewrites both sides to `z.app (A j) ≫ ι j` and `z'.app (A j) ≫ ι j`,
  and these agree by hypothesis.

## Assembly (namespace `Langlands.SmoothRep`, categories `SmoothRep ℂ G`)

Let `P : I → ObjectProperty (SmoothRep ℂ G)` and let
`w i X hX : X ⟶ X` be given for every object `X` of every `P i`, natural inside
each block (`hw`: `f ≫ w i Y hY = w i X hX ≫ f` for `f : X ⟶ Y` with `X`, `Y`
in `P i`).

- `coproductDesc w hA hc`: for a coproduct presentation `(ι j : A j ⟶ Y)` of `Y`
  with `A j` in `P j`, the endomorphism of `Y` that is `w j (A j)` on the `j`-th
  summand (`Cofan.IsColimit.desc` of `w j (A j) ≫ ι j`).
- `comp_coproductDesc`: if off-diagonal Homs vanish
  (`Renard.OffDiagonalHomsZero P`), then for every `W` in `P j` and every
  `g : W ⟶ Y`, `g ≫ coproductDesc w hA hc = w j W hW ≫ g`.
  *Proof.* By `comp_cofanComponent`, `g = g ≫ cofanProjection hc j ≫ ι j` (`g`
  lands in the `j`-th summand). The defining property of the cofan description
  gives `ι j ≫ coproductDesc = w j (A j) ≫ ι j`. Naturality of `w j` applied to
  `g ≫ cofanProjection hc j : W ⟶ A j` moves `w j` to the front. A short
  `calc` chain assembles these.
- With `hP : Renard.IsCategoryDecomposition P`:
  `assembledCenterApp hP w X` is `coproductDesc` on the coproduct presentation
  of `X` chosen from `hP.1 X`. `comp_assembledCenterApp` is
  `comp_coproductDesc` for it.
- `assembledCenter hP w hw : CatCenter (SmoothRep ℂ G)` has components
  `assembledCenterApp hP w X`.
  *Naturality.* For `f : X ⟶ Y`, test on the chosen cofan of `X` (`hom_ext`).
  For the summand `ι j : A j ⟶ X`, both `ι j ≫ f ≫ assembled_Y` and
  `ι j ≫ assembled_X ≫ f` equal `w j (A j) ≫ ι j ≫ f`, by
  `comp_assembledCenterApp` applied to `ι j ≫ f` and to `ι j`.
- `assembledCenter_app_of_mem`: on every object `X` of `P i`, the component of
  `assembledCenter hP w hw` at `X` is `w i X hX`.
  *Proof.* `comp_assembledCenterApp` with `g = 𝟙 X`.

The module uses `backward.isDefEq.respectTransparency.types false` and
`backward.isDefEq.respectTransparency false`, and no heartbeat options.

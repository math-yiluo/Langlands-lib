/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-!
# Compatibility of base-changed edge maps with the pushforward of a unit

Source: Stacks Project, Etale Cohomology, Lemma 09ZE
(`lemma-efface-cohomology-on-closed-by-finite-cover`), proof, second paragraph
(blueprint: lem-weil-pbc-finite-pushforward-unit-edge-compatibility).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private lemma counit_pushforward_unit
    {X Y Y' : Scheme.{u}} (f : Y ⟶ X) (π : Y' ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let F := (lowerStar AddCommGrpCat.{u + 1} f).obj G
    let U := (lowerStar AddCommGrpCat.{u + 1} f).map ((upperStarLowerStarAdjunction AddCommGrpCat.{u
      + 1} π).unit.app G) ≫
      (lowerStarComp AddCommGrpCat.{u + 1} π f).hom.app ((upperStar AddCommGrpCat.{u + 1} π).obj G)
    (upperStar AddCommGrpCat.{u + 1} (π ≫ f)).map U ≫
        (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (π ≫ f)).counit.app ((upperStar
          AddCommGrpCat.{u + 1} π).obj G) =
      (upperStarComp AddCommGrpCat.{u + 1} π f).hom.app F ≫
        (upperStar AddCommGrpCat.{u + 1} π).map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          f).counit.app G) := by
  dsimp only
  let η := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} π).unit.app G
  let ε := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app G
  let U := (lowerStar AddCommGrpCat.{u + 1} f).map η ≫ (lowerStarComp AddCommGrpCat.{u + 1} π
    f).hom.app
    ((upperStar AddCommGrpCat.{u + 1} π).obj G)
  change (upperStar AddCommGrpCat.{u + 1} (π ≫ f)).map U ≫
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (π ≫ f)).counit.app ((upperStar
      AddCommGrpCat.{u + 1} π).obj G) =
      (upperStarComp AddCommGrpCat.{u + 1} π f (π ≫ f) rfl).hom.app ((lowerStar AddCommGrpCat.{u +
        1} f).obj G) ≫
        (upperStar AddCommGrpCat.{u + 1} π).map ε
  apply (cancel_epi ((upperStarComp AddCommGrpCat.{u + 1} π f (π ≫ f) rfl).inv.app
    ((lowerStar AddCommGrpCat.{u + 1} f).obj G))).1
  have hn := (upperStarComp AddCommGrpCat.{u + 1} π f (π ≫ f) rfl).inv.naturality U
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.comp_map] at hn
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc]
  rw [upperStarComp_inv_app_counit_app AddCommGrpCat.{u + 1} π f ((upperStar AddCommGrpCat.{u + 1}
    π).obj G)]
  dsimp only [U]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app_assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [Category.comp_id]
  have hc := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.naturality η
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hc
  rw [hc, Functor.map_comp, Category.assoc,
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} π).left_triangle_components G,
      Category.comp_id]

private lemma exchange_edge_apply
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} g).obj ((lowerStar AddCommGrpCat.{u + 1} f).obj
      F)) q) :
    Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f').counit.app
        ((upperStar AddCommGrpCat.{u + 1} g').obj F)) q
      (cohomologyMap f' _ q (Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1} sq).app F) q x)) =
    Sheaf.H.map ((squareUpperStarIso AddCommGrpCat.{u + 1} sq).hom.app ((lowerStar AddCommGrpCat.{u
      + 1} f).obj F) ≫
      (upperStar AddCommGrpCat.{u + 1} g').map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        f).counit.app F)) q
      (cohomologyMap f' _ q x) := by
  let ε := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f').counit.app ((upperStar
    AddCommGrpCat.{u + 1} g').obj F)
  let β := (upperStar AddCommGrpCat.{u + 1} f').map ((baseChangeMap AddCommGrpCat.{u + 1} sq).app F)
  let y := cohomologyMap f' ((upperStar AddCommGrpCat.{u + 1} g).obj ((lowerStar AddCommGrpCat.{u +
    1} f).obj F)) q x
  calc
    _ = Sheaf.H.map ε q (Sheaf.H.map β q y) :=
      congrArg (Sheaf.H.map ε q) (cohomologyMap_map f' q
        ((baseChangeMap AddCommGrpCat.{u + 1} sq).app F) x)
    _ = Sheaf.H.map (β ≫ ε) q y := (Sheaf.H.map_comp_apply β ε y).symm
    _ = _ := congrArg (fun φ ↦ Sheaf.H.map φ q y)
      (upperStar_map_baseChangeMap_app_counit AddCommGrpCat.{u + 1} sq F)

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Base-changed exchange followed by the edge map carries the pushforward of the unit
for `π` to pullback along `πZ`, followed by the canonical composition comparison.
Source: Stacks Project, Lemma 09ZE (`lemma-efface-cohomology-on-closed-by-finite-cover`),
proof, second paragraph; the compatibility used there is formulated by the node's agent
(blueprint: lem-weil-pbc-finite-pushforward-unit-edge-compatibility).

Proof (the eight steps of the node):
1. Set `A = f_* G`, `B = i^* A`, and `A' = (π ≫ f)_* π^* G`. The two cartesian
squares and the equations for `πZ` identify every composite to `X`. Use the units,
counits and composition isomorphisms of def-weil-pbc-inverse-image,
def-weil-pbc-direct-image and lem-weil-pbc-inverse-image-composition. Exchange is the
adjoint of the square comparison followed by inverse image of the counit. Fix
resolutions and use proposition-cohomology-p-1-over-henselian--1 to identify all choices.
2. By situation-conventions and naturality of cohomological pullback,
exchange followed by the edge map is pullback followed by cohomology of its adjunct.
3. Naturality and composition of cohomological pullback reduce the required equality
to the equality of sheaf morphisms from `(fZ')^* B` to `(iY')^* π^* G`.
4. The counit for `π ≫ f` composed with inverse image of `f_* η_π` is inverse image
of the counit for `f`, after the composition comparison. This follows from the unit
formula of lem-weil-pbc-inverse-image-composition, naturality of the unit, and the
triangle identity of situation-conventions.
5. Expand the adjunct for the second square and move the unit morphism through the
composition isomorphisms by naturality; apply step 4.
6. Expand the adjunct for the first square and move its counit through the comparison
κ by naturality of the composition isomorphisms.
7. The remaining comparisons agree by associativity of the composition isomorphisms
(lem-weil-pbc-derived-inverse-image-composition), applied to `(f, π, iY')`,
`(f, iY, πZ)` and `(i, fZ, πZ)` in the node's order of composition.
8. Substitute this comparison identity in steps 5 and 6, then apply step 3.
No finiteness hypothesis is used; the identity base change is included. -/
theorem cohomology_baseChange_unit_edge_compatibility
    {X Y Y' Z YZ YZ' : Scheme.{u}} (f : Y ⟶ X) (π : Y' ⟶ Y) (i : Z ⟶ X)
    (iY : YZ ⟶ Y) (fZ : YZ ⟶ Z) (iY' : YZ' ⟶ Y') (fZ' : YZ' ⟶ Z)
    (πZ : YZ' ⟶ YZ) (sq : IsPullback iY fZ f i)
    (sq' : IsPullback iY' fZ' (π ≫ f) i)
    (sqπ : CommSq iY' πZ π iY) (hZ : πZ ≫ fZ = fZ')
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} fZ').counit.app
        ((upperStar AddCommGrpCat.{u + 1} iY').obj
          ((upperStar AddCommGrpCat.{u + 1} π).obj G))) q).comp
      ((cohomologyMap fZ' ((lowerStar AddCommGrpCat.{u + 1} fZ').obj
        ((upperStar AddCommGrpCat.{u + 1} iY').obj
          ((upperStar AddCommGrpCat.{u + 1} π).obj G))) q).comp
        ((Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1} sq'.toCommSq).app
          ((upperStar AddCommGrpCat.{u + 1} π).obj G)) q).comp
          (Sheaf.H.map ((upperStar AddCommGrpCat.{u + 1} i).map
            ((lowerStar AddCommGrpCat.{u + 1} f).map
                ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} π).unit.app G) ≫
              (lowerStarComp AddCommGrpCat.{u + 1} π f).hom.app
                ((upperStar AddCommGrpCat.{u + 1} π).obj G))) q))) =
      (Sheaf.H.map ((squareUpperStarIso AddCommGrpCat.{u + 1} sqπ).hom.app G) q).comp
        ((cohomologyMap πZ ((upperStar AddCommGrpCat.{u + 1} iY).obj G) q).comp
          ((Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} fZ).counit.app
            ((upperStar AddCommGrpCat.{u + 1} iY).obj G)) q).comp
            ((cohomologyMap fZ ((lowerStar AddCommGrpCat.{u + 1} fZ).obj
              ((upperStar AddCommGrpCat.{u + 1} iY).obj G)) q).comp
              (Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app G) q)))) := by
  subst fZ'
  let F := (lowerStar AddCommGrpCat.{u + 1} f).obj G
  let B := (upperStar AddCommGrpCat.{u + 1} i).obj F
  let E := (upperStar AddCommGrpCat.{u + 1} π).obj G
  let U := (lowerStar AddCommGrpCat.{u + 1} f).map ((upperStarLowerStarAdjunction AddCommGrpCat.{u +
    1} π).unit.app G) ≫
    (lowerStarComp AddCommGrpCat.{u + 1} π f).hom.app E
  let V := (upperStar AddCommGrpCat.{u + 1} i).map U
  let θ₁ := (squareUpperStarIso AddCommGrpCat.{u + 1} sq.toCommSq).hom.app F
  let θ₂ := (squareUpperStarIso AddCommGrpCat.{u + 1} sq'.toCommSq).hom.app ((lowerStar
    AddCommGrpCat.{u + 1} (π ≫ f)).obj E)
  let ε₁ := (upperStar AddCommGrpCat.{u + 1} iY).map ((upperStarLowerStarAdjunction AddCommGrpCat.{u
    + 1} f).counit.app G)
  let ε₂ := (upperStar AddCommGrpCat.{u + 1} iY').map
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (π ≫ f)).counit.app E)
  let κ := (squareUpperStarIso AddCommGrpCat.{u + 1} sqπ).hom.app G
  let c := (upperStarComp AddCommGrpCat.{u + 1} πZ fZ).hom.app B
  -- Compare the two adjuncts using the composite counit and vertical square pasting.
  have hm : (upperStar AddCommGrpCat.{u + 1} (πZ ≫ fZ)).map V ≫ θ₂ ≫ ε₂ =
      c ≫ (upperStar AddCommGrpCat.{u + 1} πZ).map (θ₁ ≫ ε₁) ≫ κ := by
    have hn := (squareUpperStarIso AddCommGrpCat.{u + 1} sq'.toCommSq).hom.naturality U
    dsimp only [Functor.comp_obj, Functor.comp_map] at hn
    change (upperStar AddCommGrpCat.{u + 1} (πZ ≫ fZ)).map V ≫ θ₂ ≫ ε₂ = _
    rw [← Category.assoc, hn]
    simp only [Category.assoc]
    rw [← Functor.map_comp]
    rw [counit_pushforward_unit f π G]
    simp only [Functor.map_comp, Category.assoc]
    have hp := NatTrans.congr_app
      (squareUpperStarIso_paste_vert_hom AddCommGrpCat.{u + 1} sqπ sq.toCommSq sq'.toCommSq) F
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_obj, TwoSquare.vComp_app] at hp
    dsimp only [F] at hp
    dsimp only [θ₂, θ₁, c, B, F, V, ε₂, Functor.id_obj]
    rw [hp]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    dsimp only [Functor.comp_obj]
    rw [(upperStar AddCommGrpCat.{u + 1} iY').map_id, Category.id_comp]
    have hk := (squareUpperStarIso AddCommGrpCat.{u + 1} sqπ).hom.naturality
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app G)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hk
    dsimp only [ε₁, κ]
    rw [← hk]
  -- Express each exchange followed by its edge map as cohomology of its adjunct.
  ext x
  change Sheaf.H.map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (πZ ≫ fZ)).counit.app
        ((upperStar AddCommGrpCat.{u + 1} iY').obj E)) q
      (cohomologyMap (πZ ≫ fZ) _ q
        (Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1} sq'.toCommSq).app E) q (Sheaf.H.map V q
          x))) =
    Sheaf.H.map κ q (cohomologyMap πZ _ q
      (Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} fZ).counit.app
        ((upperStar AddCommGrpCat.{u + 1} iY).obj G)) q
        (cohomologyMap fZ _ q (Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app G)
          q x))))
  have h₂ := exchange_edge_apply sq'.toCommSq E q (Sheaf.H.map V q x)
  have h₁ := exchange_edge_apply sq.toCommSq G q x
  refine h₂.trans ?_
  refine Eq.trans ?_ (congrArg (fun z ↦ Sheaf.H.map κ q
    (cohomologyMap πZ ((upperStar AddCommGrpCat.{u + 1} iY).obj G) q z)) h₁).symm
  change Sheaf.H.map (θ₂ ≫ ε₂) q
      (cohomologyMap (πZ ≫ fZ) _ q (Sheaf.H.map V q x)) =
    Sheaf.H.map κ q (cohomologyMap πZ _ q
      (Sheaf.H.map (θ₁ ≫ ε₁) q (cohomologyMap fZ B q x)))
  -- Both sides now factor through pullback along the same composite.
  let d := cohomologyMap (πZ ≫ fZ) B q x
  have hl : Sheaf.H.map (θ₂ ≫ ε₂) q
      (cohomologyMap (πZ ≫ fZ) _ q (Sheaf.H.map V q x)) =
      Sheaf.H.map ((upperStar AddCommGrpCat.{u + 1} (πZ ≫ fZ)).map V ≫ θ₂ ≫ ε₂) q d := by
    calc
      _ = Sheaf.H.map (θ₂ ≫ ε₂) q
          (Sheaf.H.map ((upperStar AddCommGrpCat.{u + 1} (πZ ≫ fZ)).map V) q d) :=
        congrArg (Sheaf.H.map (θ₂ ≫ ε₂) q) (cohomologyMap_map (πZ ≫ fZ) q V x)
      _ = _ := (Sheaf.H.map_comp_apply _ _ d).symm
  have hr : Sheaf.H.map κ q (cohomologyMap πZ _ q
      (Sheaf.H.map (θ₁ ≫ ε₁) q (cohomologyMap fZ B q x))) =
      Sheaf.H.map (c ≫ (upperStar AddCommGrpCat.{u + 1} πZ).map (θ₁ ≫ ε₁) ≫ κ) q d := by
    let y := cohomologyMap πZ ((upperStar AddCommGrpCat.{u + 1} fZ).obj B) q (cohomologyMap fZ B q
      x)
    let φ := (upperStar AddCommGrpCat.{u + 1} πZ).map (θ₁ ≫ ε₁)
    calc
      _ = Sheaf.H.map κ q (Sheaf.H.map φ q y) :=
        congrArg (Sheaf.H.map κ q)
          (cohomologyMap_map πZ q (θ₁ ≫ ε₁) (cohomologyMap fZ B q x))
      _ = Sheaf.H.map (φ ≫ κ) q y := (Sheaf.H.map_comp_apply φ κ y).symm
      _ = Sheaf.H.map (φ ≫ κ) q (Sheaf.H.map c q d) :=
        congrArg (Sheaf.H.map (φ ≫ κ) q)
          ((cohomologyPullbackFunctorial πZ fZ B q).2.1 x)
      _ = _ := (Sheaf.H.map_comp_apply c (φ ≫ κ) d).symm
  exact hl.trans ((congrArg (fun φ ↦ Sheaf.H.map φ q d) hm).trans hr.symm)

end AlgebraicGeometry.Etale

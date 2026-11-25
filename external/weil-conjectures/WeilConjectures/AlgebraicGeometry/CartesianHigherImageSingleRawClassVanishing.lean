/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageTransitions
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
import WeilConjectures.AlgebraicGeometry.CartesianRawClassChartRepresentative
import WeilConjectures.AlgebraicGeometry.RestrictedOverAbelianCohomologyPresentation
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawComplexPresentation
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Eventual vanishing of one raw cartesian derived class

Source: Stacks Project, Tags 0EYM, 0EYL and 0GIT.
(blueprint: stage3-cartesian-higher-image-single-raw-class-vanishing).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

noncomputable local instance singleRawClassVanishingHasShift (T : Scheme.{u}) :
    HasShift (DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) ℤ :=
  inferInstance

noncomputable local instance singleRawClassVanishingHasZeroMorphisms (T : Scheme.{u}) :
    HasZeroMorphisms (DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
  inferInstance

private theorem iso_reflects_zero {A B : AddCommGrpCat.{u + 1}} (e : A ≅ B) (x : A)
    (h : e.hom x = 0) : x = 0 := by
  have hi := congrArg e.inv h
  simpa only [Iso.hom_inv_id_apply, map_zero] using hi

section
attribute [local irreducible] restrictedOverCohomology restrictedOverCohomologyMap

set_option backward.isDefEq.respectTransparency true in
private theorem restrictedOver_eventually_zero
    {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    {J : Type u} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Over W)
    [∀ {i j : J} (a : i ⟶ j), IsAffineHom (D.map a).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (U : S.Etale) [IsAffine U.left] (i : J)
    (x : restrictedOverCohomology k F q (D.obj i) U)
    (hx : restrictedOverCohomologyMap k F q (c.π.app i) U x = 0) :
    ∃ (j : J) (a : j ⟶ i), restrictedOverCohomologyMap k F q (D.map a) U x = 0 := by
  obtain ⟨H, B, e, e₀, hdata, hm, hleg⟩ :=
    exists_restrictedOverAbelian_cohomology_presentation k F q D c hc U
  obtain ⟨hB⟩ := EtaleComplexCohomologyPresentation.isColimit hdata
  have := preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (forget AddCommGrpCat.{u + 1})
  let y := (e i).inv x
  have hy : B.ι.app (op i) y = 0 := by
    have h := ConcreteCategory.congr_hom (hleg i) y
    simp only [AddCommGrpCat.comp_apply, y, Iso.inv_hom_id_apply] at h
    exact iso_reflects_zero e₀ _ (h.trans hx)
  have heq : B.ι.app (op i) y = B.ι.app (op i) 0 := by rw [hy, map_zero]
  obtain ⟨j, a, ha⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (forget AddCommGrpCat.{u + 1}) hB) y 0).mp heq
  refine ⟨j.unop, a.unop, ?_⟩
  have h := ConcreteCategory.congr_hom (hm i j.unop a.unop) y
  have ha' : H.map a y = 0 := by
    change H.map a y = H.map a 0 at ha
    simpa only [map_zero] using ha
  simp only [AddCommGrpCat.comp_apply, Quiver.Hom.op_unop, y,
    Iso.inv_hom_id_apply] at h
  rw [ha', map_zero] at h
  exact h.symm

end

/-- A single raw cartesian derived class killed at the limit is killed at a later stage.

Source: Stacks Project, Tags 0EYM, 0EYL and 0GIT. Apply affine cohomology continuity
to the descended qcqs chart system and identify its transition with the displayed
raw map by exchange naturality.
(blueprint: stage3-cartesian-higher-image-single-raw-class-vanishing).

The proof is the affine cohomology continuity argument for one test object: descend the
finite-presentation chart and the raw derived class, apply continuity of the resulting
bounded-below cohomology system, and identify the resulting stage map with the displayed
cartesian transition by exchange naturality. This is strictly the one-class case; no
finite-family equalization is included. Empty affine objects and degree zero are covered
by the same construction.
-/
theorem exists_cartesianHigherImage_single_raw_class_eq_zero
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (i : I) (V : c.pt.left.Etale) [IsAffine V.left]
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((abelianComparisonFree c.pt.left).obj V) ⟶
        ((D+(((c.π.app i).left)^*[AddCommGrpCat.{u + 1}])).obj
          (cartesianDerivedImage f (D.obj i).hom
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧)
    (hz : z ≫ (shiftFunctor _ (q : ℤ)).map
      (cartesianDerivedImageMap f (D.obj i).hom c.pt.hom (c.π.app i).left
        (Over.w (c.π.app i)).symm ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) = 0) :
    ∃ (j : I) (a : j ⟶ i),
      z ≫ (shiftFunctor _ (q : ℤ)).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
          (c.π.app j).left (D.map a).left (c.π.app i).left
          (congrArg (fun b ↦ b.left) (c.w a)).symm).hom.app _ ≫
          (D+(((c.π.app j).left)^*[AddCommGrpCat.{u + 1}])).map
            (cartesianDerivedImageMap f (D.obj i).hom (D.obj j).hom
              (D.map a).left (Over.w (D.map a)).symm
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) = 0 := by
  classical
  obtain ⟨j, W, hW, r, hr, l, b, x, hlimit, htrans⟩ :=
    exists_cartesianRawClass_chart_representative D c hc f F q i V z
  let : IsAffine W.left := hW
  obtain ⟨⟨hchart⟩, haff, hqc, hqs, hqc₀, hqs₀⟩ :=
    cartesianChartSystem_properties f D c hc j
  let : ∀ {s t : Over j} (a : s ⟶ t),
      IsAffineHom ((cartesianChartDiagram f D j).map a).left := fun a ↦ haff a
  let := hqc
  let := hqs
  let := hqc₀
  let := hqs₀
  have hx : restrictedOverCohomologyMap (pullback.snd f (D.obj j).hom)
      (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartCone f D c j).π.app l) W x = 0 := by
    have h := congrArg
      (cartesianChartCohomologyIso f (D.obj j).hom (c.π.app j).left c.pt.hom
        (Over.w (c.π.app j)).symm F q W V r hr).inv (hlimit.symm.trans hz)
    simpa only [Iso.hom_inv_id_apply, map_zero] using h
  obtain ⟨m, a, ha⟩ := restrictedOver_eventually_zero
    (pullback.snd f (D.obj j).hom)
    (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
    (q : ℤ) (cartesianChartDiagram f D j) (cartesianChartCone f D c j) hchart W l x hx
  refine ⟨m.left, a.left ≫ b, ?_⟩
  rw [htrans m a, ha]
  simp only [cartesianChartCohomologyLift, map_zero, cartesianChartClassPullback,
    Functor.map_zero, Limits.comp_zero, Limits.zero_comp]

end AlgebraicGeometry.Etale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # The cartesian scheme system above one stage

Source: Stacks Project, Tag 0EYM, second proof.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Restrict the base system above i and pull it back to X times the i-th base.
This is an actual functor of fibre products, without any chosen descent data.
(blueprint: def-sc-cartesian-higher-image-chart-system). -/
noncomputable def cartesianChartDiagram
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (i : I) :
    Over i ⥤ Over (pullback f (D.obj i).hom) :=
  Over.post (X := i) (D ⋙ Over.forget S) ⋙ Over.pullback (pullback.snd f (D.obj i).hom)

/-- The same explicit pullback construction on the limiting cone.
(blueprint: def-sc-cartesian-higher-image-chart-system). -/
noncomputable def cartesianChartCone
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D) (i : I) :
    Cone (cartesianChartDiagram f D i) :=
  (Over.pullback (pullback.snd f (D.obj i).hom)).mapCone
    (((Over.forget S).mapCone c).overPost i)

/-- The chart system is limiting and has affine arrows and qcqs structure maps.
Source: Stacks Project, Tags 0EYM, 01YZ and 01Z6.
(blueprint: lem-sc-cartesian-higher-image-chart-system).

Proof: Restrict the underlying scheme cone to Over i. Its forgetful functor is
initial because I is cofiltered; therefore this restriction is limiting. Pullback
to X times_S S_i preserves limits. Forgetting an over-category preserves connected
limits, and Over i is cofiltered, hence connected. This gives the underlying
limiting cone of cartesianChartDiagram. Each transition map is the base change of
an original affine transition. The projection of the original limit to S_i is
affine, so the apex structure map is affine as well. Each stage structure map is
the base change of an original affine transition to S_i. Compose these affine
maps with X times_S S_i to S_i, which is qcqs as the base change of f. Thus the
stage and apex maps to S_i are qcqs. This construction uses no etale test object,
coefficient sheaf, cohomology comparison, or continuity assertion. -/
theorem cartesianChartSystem_properties
    {S X : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over S)
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (i : I) :
    Nonempty (IsLimit ((Over.forget _).mapCone (cartesianChartCone f D c i))) ∧
    (∀ {j l : Over i} (a : j ⟶ l),
      IsAffineHom ((cartesianChartDiagram f D i).map a).left) ∧
    (∀ j : Over i, QuasiCompact
      (((cartesianChartDiagram f D i).obj j).hom ≫ pullback.snd f (D.obj i).hom)) ∧
    (∀ j : Over i, QuasiSeparated
      (((cartesianChartDiagram f D i).obj j).hom ≫ pullback.snd f (D.obj i).hom)) ∧
    QuasiCompact ((cartesianChartCone f D c i).pt.hom ≫ pullback.snd f (D.obj i).hom) ∧
    QuasiSeparated ((cartesianChartCone f D c i).pt.hom ≫
      pullback.snd f (D.obj i).hom) := by
  classical
  let h := pullback.snd f (D.obj i).hom
  let E := D ⋙ Over.forget S
  let d := (Over.forget S).mapCone c
  have (j l : I) (a : j ⟶ l) : IsAffineHom (E.map a) :=
    inferInstanceAs (IsAffineHom (D.map a).left)
  have hπ : IsAffineHom (d.π.app i) := isAffineHom_π_app E d hc i
  have hlimit : IsLimit ((Over.forget _).mapCone (cartesianChartCone f D c i)) := by
    let P := Over.pullback h ⋙ Over.forget (pullback f (D.obj i).hom)
    have : IsConnected (Over i) := IsCofiltered.isConnected (Over i)
    exact isLimitOfPreserves P (hc.overPost i)
  refine ⟨⟨hlimit⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro j l a
    change @IsAffineHom (pullback (E.map j.hom) h) (pullback (E.map l.hom) h)
      (pullback.lift
      (pullback.fst (E.map j.hom) h ≫ E.map a.left)
      (pullback.snd (E.map j.hom) h) _)
    have hm := MorphismProperty.pullbackMap (P := @IsAffineHom)
      (f := E.map j.hom) (g := h) (f' := E.map l.hom) (g' := h)
      (i₁ := E.map a.left) (i₂ := 𝟙 _) (by infer_instance) (by infer_instance)
      (by simp [← E.map_comp, Over.w a]) (by simp)
    simpa only [pullback.map, Category.comp_id] using hm
  · intro j
    change QuasiCompact (pullback.snd (E.map j.hom) h ≫ h)
    have : IsAffineHom (E.map j.hom) := inferInstance
    infer_instance
  · intro j
    change QuasiSeparated (pullback.snd (E.map j.hom) h ≫ h)
    have : IsAffineHom (E.map j.hom) := inferInstance
    infer_instance
  · change QuasiCompact (pullback.snd (d.π.app i) h ≫ h)
    infer_instance
  · change QuasiSeparated (pullback.snd (d.π.app i) h ≫ h)
    infer_instance

end AlgebraicGeometry.Etale

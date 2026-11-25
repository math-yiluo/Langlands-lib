/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over

/-! # Tensor pullback of a presentation on a specified open

Source: Stacks Project, Modules, Tag 01BG, Lemma 17.10.4.
(blueprint: lem-pc-ringed-space-tensor-pullback-presentation-over)

The restriction comparison follows by comparing right adjoints: inverse image of opens
commutes with intersection, and naturality of the structure map identifies the scalar maps.
-/

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry.RingedSpace

noncomputable section

open CategoryTheory.Limits TopologicalSpace in
private local instance tensorPullbackOver_continuous
    {X Y : RingedSpace.{u}} (g : X ⟶ Y) (V : Opens Y) :
    (Over.post (X := V) (Opens.map g.hom.base)).IsContinuous
      ((Opens.grothendieckTopology Y).over V)
      ((Opens.grothendieckTopology X).over ((Opens.map g.hom.base).obj V)) := by
  have : Limits.PreservesFiniteLimits (Opens.map g.hom.base) :=
    preservesFiniteLimits_of_flat _
  have : RepresentablyFlat (Over.post (X := V) (Opens.map g.hom.base)) :=
    flat_of_preservesFiniteLimits _
  exact Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    ((coverPreserving_opens_map g.hom.base).overPost V)

open CategoryTheory.Limits TopologicalSpace in
private local instance tensorPullbackOver_final
    {X Y : RingedSpace.{u}} (g : X ⟶ Y) (V : Opens Y) :
    (Over.post (X := V) (Opens.map g.hom.base)).Final := by
  have : Limits.PreservesFiniteLimits (Opens.map g.hom.base) :=
    preservesFiniteLimits_of_flat _
  infer_instance

open CategoryTheory.Limits TopologicalSpace in
/-- The structure map restricted to the slice site over V. -/
private def tensorPullbackOverRingHom
    {X Y : RingedSpace.{u}} (g : X ⟶ Y) (V : Opens Y) :
    (moduleRings Y).over V ⟶
      ((Over.post (X := V) (Opens.map g.hom.base)).sheafPushforwardContinuous
        RingCat.{u} ((Opens.grothendieckTopology Y).over V)
        ((Opens.grothendieckTopology X).over ((Opens.map g.hom.base).obj V))).obj
          ((moduleRings X).over ((Opens.map g.hom.base).obj V)) :=
  ((Over.forget V).sheafPushforwardContinuous RingCat.{u}
    ((Opens.grothendieckTopology Y).over V) (Opens.grothendieckTopology Y)).map
      (show moduleRings Y ⟶
        ((Opens.map g.hom.base).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj
            (moduleRings X) from
        ⟨Functor.whiskerRight g.hom.c (forget₂ CommRingCat RingCat)⟩)

-- The product comparison expresses g⁻¹(V ∩ W) = g⁻¹(V) ∩ g⁻¹(W).
open CategoryTheory.Limits TopologicalSpace in
private def tensorPullbackOverStarIso
    {X Y : RingedSpace.{u}} (g : X ⟶ Y) (V : Opens Y) :
    Opens.map g.hom.base ⋙ Over.star ((Opens.map g.hom.base).obj V) ≅
      Over.star V ⋙ Over.post (Opens.map g.hom.base) := by
  have : Limits.PreservesFiniteLimits (Opens.map g.hom.base) :=
    preservesFiniteLimits_of_flat _
  refine NatIso.ofComponents (fun W ↦
    Over.isoMk (Limits.PreservesLimitPair.iso (Opens.map g.hom.base) V W).symm ?_) ?_
  · apply Subsingleton.elim
  · intro W W' f
    ext
    apply Subsingleton.elim

-- Right adjoints to the two orders of restriction and pullback agree. The final
-- calculation checks the scalar maps, rather than only the underlying abelian sheaves.
open CategoryTheory.Limits TopologicalSpace in
private def tensorPullbackOverRightIso
    {X Y : RingedSpace.{u}} (g : X ⟶ Y) (V : Opens Y) :
    SheafOfModules.pushforward.{u}
      (SheafOfModules.pushforwardOver (R := moduleRings X) ((Opens.map g.hom.base).obj V)) ⋙
        moduleDirectImage g ≅
      SheafOfModules.pushforward.{u} (tensorPullbackOverRingHom g V) ⋙
        SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver (R := moduleRings Y) V) := by
  let F := Opens.map g.hom.base
  let U := F.obj V
  let J := Opens.grothendieckTopology Y
  let K := Opens.grothendieckTopology X
  let φ : moduleRings Y ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj
      (moduleRings X) := ⟨Functor.whiskerRight g.hom.c (forget₂ CommRingCat RingCat)⟩
  let ψX := SheafOfModules.pushforwardOver (R := moduleRings X) U
  let ψY := SheafOfModules.pushforwardOver (R := moduleRings Y) V
  have : (F ⋙ Over.star U).IsContinuous J (K.over U) :=
    Functor.isContinuous_comp _ _ _ K _
  have : (Over.star V ⋙ Over.post F).IsContinuous J (K.over U) :=
    Functor.isContinuous_comp _ _ _ (J.over V) _
  refine SheafOfModules.pushforwardComp φ ψX ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp ψY (tensorPullbackOverRingHom g V)).symm
  refine SheafOfModules.pushforwardCongr₂ _
    (tensorPullbackOverStarIso g V).symm ?_
  ext W r
  simp only [Iso.symm_hom, Category.assoc, ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app, Functor.whiskerRight_app, Functor.op_obj,
    Functor.comp_obj, NatTrans.op_app, Functor.sheafPushforwardContinuous_obj_obj_map,
    Over.forget_obj, Quiver.Hom.unop_op, Over.forget_map, RingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply]
  change X.sheaf.obj.map (prodComparison (Opens.map g.hom.base) V W.unop).op
    (X.sheaf.obj.map prod.snd.op (g.hom.c.app W r)) =
      g.hom.c.app (Opposite.op (V ⨯ W.unop)) (Y.sheaf.obj.map prod.snd.op r)
  rw [← Functor.map_comp_apply, ← op_comp, Limits.prodComparison_snd]
  exact (ConcreteCategory.congr_hom
    (g.hom.c.naturality (Limits.prod.snd : V ⨯ W.unop ⟶ W.unop).op) r).symm

-- Transport the right-adjoint comparison to left adjoints, then use the prescribed
-- object formula of the concrete tensor pullback.
open CategoryTheory.Limits TopologicalSpace in
private theorem tensorPullbackOverComparison
    {X Y : RingedSpace.{u}} (g : X ⟶ Y) (V : Opens Y)
    (G : SheafOfModules.{u} (moduleRings Y)) :
    Nonempty
      ((SheafOfModules.pullback.{u} (tensorPullbackOverRingHom g V)).obj (G.over V) ≅
        (SheafOfModules.changeOfRings.{u, u, u}
          (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
          (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf G)).over
            ((Opens.map g.hom.base).obj V)) := by
  obtain ⟨P, hP, _, _, ⟨adjP⟩⟩ := exists_tensorModulePullback g
  let U := (Opens.map g.hom.base).obj V
  let adjX := SheafOfModules.overPushforwardOverAdj (R := moduleRings X) U
  let adjY := SheafOfModules.overPushforwardOverAdj (R := moduleRings Y) V
  let adjV := SheafOfModules.pullbackPushforwardAdjunction.{u} (tensorPullbackOverRingHom g V)
  let e := Adjunction.leftAdjointUniq (adjY.comp adjV)
    ((adjP.comp adjX).ofNatIsoRight (tensorPullbackOverRightIso g V))
  exact ⟨e.app G ≪≫ (SheafOfModules.overFunctor (moduleRings X) U).mapIso (eqToIso (hP G))⟩

/-- Tensor pullback transports a global presentation over an open subset.
Source: Stacks Project, Modules, Tag 01BG, Lemma 17.10.4, global presentation step.
(blueprint: lem-pc-ringed-space-tensor-pullback-presentation-over)

Proof: Put U = g⁻¹(V) and restrict g to the morphism of ringed spaces U → V.
Restriction commutes with inverse image and with sheafified extension of scalars:
on an open W contained in U, the inverse-image presheaf is computed using opens
of Y containing g(W), and those contained in V form a cofinal subposet. The
structure maps and tensor products on these opens agree; sheafification commutes
with restriction. Thus the displayed module over U identifies with the tensor
pullback of G over V along this restricted morphism. Its inverse-image and
extension-of-scalars functors are left adjoints, so preserve coproducts and
cokernels. The pullback of the unit module is the unit module: the tensor map
b ⊗ a ↦ b g-sharp(a) has inverse b ↦ b ⊗ 1. Consequently each free module in the
presentation p pulls back to the free module with the same indexing set. Apply
the composite functor to the cokernel presentation furnished by p. Preservation
of its cokernel gives an exact free presentation of the pulled-back module.
Mathlib's Presentation.map packages this construction, and Presentation.ofIsIso
transports it through the restriction comparison above. No choices of a cover
or of a neighbourhood of a point occur in this statement. -/
theorem tensorModulePullback_presentation_over
    {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (G : SheafOfModules.{u} (moduleRings Y)) (V : TopologicalSpace.Opens Y)
    (p : (G.over V).Presentation) :
    Nonempty
      (((SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf G)).over
          ((TopologicalSpace.Opens.map g.hom.base).obj V)).Presentation) := by
  obtain ⟨e⟩ := tensorPullbackOverComparison g V G
  exact ⟨SheafOfModules.Presentation.ofIsIso e.hom
    (p.map (SheafOfModules.pullback.{u} (tensorPullbackOverRingHom g V))
      (asIso (SheafOfModules.pullbackObjUnitToUnit (tensorPullbackOverRingHom g V))).symm)⟩

end

end AlgebraicGeometry.RingedSpace

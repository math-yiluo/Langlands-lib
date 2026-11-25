/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The ordinary affine model comparison

Source: Stacks Project, perfect.tex, Tags 06Z0, 08DV, 08DW and 0AA7.
(blueprint: new-affine-extension-sections-underived-model).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
-- Affine functor identifications need to unfold the scheme module carrier.
/-- The affine extension/sections comparison on associated sheaves, with its unit equation.
Source: Stacks Project, Schemes, Tag 01I9, and perfect.tex, Tag 0AA7.
(blueprint: new-affine-extension-sections-underived-model).
Proof: Compose the tilde/sections adjunction with tensor pullback/direct image.
The comparison v identifies its right adjoint with B-sections followed by restriction
of scalars.
The same right adjoint belongs to extension of scalars followed by B-tilde.
Uniqueness of left adjoints supplies the tilde/pullback comparison with its unit
formula. Apply B-sections and cancel the invertible tilde/sections units over R and B.
The result is c, and the unit formula gives the displayed equality. The computation
works for zero rings and zero modules and does not require the ring map to be flat. -/
theorem exists_affineExtensionSections_underived_model
    {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R)
    (v : RingedSpace.moduleDirectImage g.toLRSHom.toShHom ⋙
        affineGlobalSections (𝟙 (Spec R)) ≅
      affineGlobalSections (𝟙 (Spec B)) ⋙
        ModuleCat.restrictScalars.{u} (affineBaseRingMap g)) :
    ∃ c : (@id (ModuleCat.{u} R ⥤
        SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
        (tilde.functor R)) ⋙ affineGlobalSections (𝟙 (Spec R)) ⋙
        ModuleCat.extendScalars.{u, u, u} (affineBaseRingMap g) ≅
      (@id (ModuleCat.{u} R ⥤
        SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
        (tilde.functor R)) ⋙ (@id (SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
        (Scheme.Modules.tensorPullback g)) ⋙
        affineGlobalSections (𝟙 (Spec B)),
      ∀ N : ModuleCat.{u} R,
        (ModuleCat.extendRestrictScalarsAdj (affineBaseRingMap g)).unit.app
            ((affineGlobalSections (𝟙 (Spec R))).obj ((tilde.functor R).obj N)) ≫
          (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).map (c.hom.app N) =
        (affineGlobalSections (𝟙 (Spec R))).map
            ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app
              ((tilde.functor R).obj N)) ≫
          v.hom.app ((Scheme.Modules.tensorPullback g).obj ((tilde.functor R).obj N)) := by
  let TR : ModuleCat.{u} R ⥤ SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace) :=
    tilde.functor R
  let TB : ModuleCat.{u} B ⥤ SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace) :=
    tilde.functor B
  let ΓR : SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace) ⥤ ModuleCat.{u} R :=
    affineGlobalSections (𝟙 (Spec R))
  let ΓB : SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace) ⥤ ModuleCat.{u} B :=
    affineGlobalSections (𝟙 (Spec B))
  let E := ModuleCat.extendScalars.{u, u, u} (affineBaseRingMap g)
  let S := ModuleCat.restrictScalars.{u} (affineBaseRingMap g)
  let P : SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace) :=
    Scheme.Modules.tensorPullback g
  let V : RingedSpace.moduleDirectImage g.toLRSHom.toShHom ⋙ ΓR ≅ ΓB ⋙ S := v
  let br : TR ⊣ ΓR := tilde.adjunction
  let bb : TB ⊣ ΓB := tilde.adjunction
  have : IsIso br.unit := inferInstanceAs (IsIso (tilde.adjunction (R := R)).unit)
  have : IsIso bb.unit := inferInstanceAs (IsIso (tilde.adjunction (R := B)).unit)
  let e : E ⊣ S := ModuleCat.extendRestrictScalarsAdj (affineBaseRingMap g)
  let p : P ⊣ RingedSpace.moduleDirectImage g.toLRSHom.toShHom :=
    Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let a₁ := (br.comp p).ofNatIsoRight V
  let a₂ := e.comp bb
  let θ := a₂.leftAdjointUniq a₁
  let c : TR ⋙ ΓR ⋙ E ≅ TR ⋙ P ⋙ ΓB :=
    Functor.isoWhiskerRight (asIso br.unit).symm E ≪≫ Functor.leftUnitor E ≪≫
      (Functor.rightUnitor E).symm ≪≫ Functor.isoWhiskerLeft E (asIso bb.unit) ≪≫
        Functor.isoWhiskerRight θ ΓB
  refine ⟨c, ?_⟩
  intro N
  have h := a₂.unit_leftAdjointUniq_hom_app a₁ N
  change e.unit.app N ≫ S.map (bb.unit.app (E.obj N)) ≫
      S.map (ΓB.map (θ.hom.app N)) =
    br.unit.app N ≫ ΓR.map (p.unit.app (TR.obj N)) ≫
      V.hom.app (P.obj (TR.obj N)) at h
  change e.unit.app (ΓR.obj (TR.obj N)) ≫ S.map (c.hom.app N) =
    ΓR.map (p.unit.app (TR.obj N)) ≫ V.hom.app (P.obj (TR.obj N))
  dsimp only [c, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app]
  simp only [Category.id_comp, Functor.map_comp]
  change e.unit.app (ΓR.obj (TR.obj N)) ≫
      S.map (E.map ((asIso br.unit).inv.app N)) ≫
        S.map (bb.unit.app (E.obj N)) ≫ S.map (ΓB.map (θ.hom.app N)) = _
  have hn := e.unit.naturality ((asIso br.unit).inv.app N)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  change (asIso br.unit).inv.app N ≫ e.unit.app N =
    e.unit.app (ΓR.obj (TR.obj N)) ≫
      S.map (E.map ((asIso br.unit).inv.app N)) at hn
  rw [← Category.assoc, ← hn, Category.assoc, h]
  change (((asIso br.unit).inv.app N ≫ (asIso br.unit).hom.app N) ≫
    ΓR.map (p.unit.app (TR.obj N))) ≫ V.hom.app (P.obj (TR.obj N)) = _
  rw [Iso.inv_hom_id_app, Category.id_comp]


end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
import all WeilConjectures.AlgebraicGeometry.FiniteFreeStalkMapEquality

/-! # Local equality of morphisms from finite free retracts

Source: Stacks Project, Tag 01CP, finite-type injectivity argument.
(blueprint: lem-sc-perfect-open-stalk-retract-hom-equality).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Maps from a restricted finite free retract to any module sheaf agree nearby
if their maps on the open module stalk agree.

Source: Stacks Project, Tag 01CP, injectivity for a finite-type source;
Tag 09RE, finite-presentation calculation.
(blueprint: lem-sc-perfect-open-stalk-retract-hom-equality).

Proof: Restrict the inclusion and projection exhibiting M as a retract to W.
Precompose a and b with the projection from the restricted finite free sheaf.
Their stalks agree by functoriality. Evaluate on each of its finitely many free
basis sections. The two resulting sections of N have equal germs. The germ
criterion gives a neighbourhood for each equality; intersect these finitely
many neighbourhoods inside W. The two maps from the free sheaf agree there
by their basis values. Precompose with the restricted inclusion and use the
splitting identity to obtain equality of a and b. The equivalence between the
slice site and the open subscheme identifies these germs with the specified
open module stalks; restriction of scalars is faithful. No finiteness of N is
used. For rank zero the retract is zero and both maps are uniquely zero. -/
theorem exists_open_stalk_retract_hom_eq
    (X : Scheme.{u}) (U W : X.Opens) (hWU : W ≤ U)
    (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (hM : ∃ m : ℕ,
      ∃ (ι : M ⟶ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)))
        (π : SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)) ⟶ M),
        ι ≫ π = 𝟙 M)
    (N : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))
    (x : X) (hxW : x ∈ W)
    (a b : (SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE hWU)).obj M ⟶ N)
    (heq : (openModuleStalkFunctor X W ⟨x, hxW⟩).map a =
      (openModuleStalkFunctor X W ⟨x, hxW⟩).map b) :
    ∃ (V : X.Opens) (hVW : V ≤ W), x ∈ V ∧
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVW)).map a =
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVW)).map b := by
  classical
  obtain ⟨m, ι, π, hsplit⟩ := hM
  let R := SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hWU)
  let E := (Modules.overEquiv W).functor
  let T := R ⋙ E
  let y : W.toScheme := ⟨x, hxW⟩
  let S := RingedSpace.moduleStalkFunctor W.toScheme.toRingedSpace y
  let NW := E.obj N
  let ea := E.map a
  let eb := E.map b
  have hs : S.map ea = S.map eb := by
    exact (ModuleCat.restrictScalars (W.ι.stalkMap y).hom).map_injective heq
  let eunit : SheafOfModules.unit W.toScheme.ringCatSheaf ≅
      T.obj (SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)) :=
    (E.mapIso (SheafOfModules.overMapUnitIso (homOfLE hWU)) ≪≫
      (Modules.overEquivFunctorObjUnitIso W).symm).symm
  have : PreservesColimitsOfShape (Discrete (ULift.{u} (Fin m))) T := by
    dsimp [T, R, E]
    infer_instance
  let e := SheafOfModules.mapFreeIso T (ULift.{u} (Fin m)) eunit
  let p := e.hom ≫ T.map π
  let i := T.map ι ≫ e.inv
  have hip : i ≫ p = 𝟙 (E.obj (R.obj M)) := by
    simp only [i, p, Category.assoc, Iso.inv_hom_id_assoc,
      ← T.map_comp, hsplit, T.map_id]
    rfl
  let f := p ≫ ea
  let g := p ≫ eb
  have hfg : S.map f = S.map g := by
    simp only [f, g, Functor.map_comp, hs]
  have hg (k : ULift.{u} (Fin m)) :
      NW.presheaf.germ ⊤ y (by trivial)
        (Modules.Hom.app (SheafOfModules.ιFree k ≫ f) ⊤
          (1 : Γ(W.toScheme, ⊤))) =
      NW.presheaf.germ ⊤ y (by trivial)
        (Modules.Hom.app (SheafOfModules.ιFree k ≫ g) ⊤
          (1 : Γ(W.toScheme, ⊤))) := by
    have hh := congrArg (fun t ↦ S.map (SheafOfModules.ιFree k) ≫ t) hfg
    rw [← Functor.map_comp, ← Functor.map_comp] at hh
    have ht := congrArg (fun t ↦ t
      (TopCat.Presheaf.germ (SheafOfModules.unit W.toScheme.ringCatSheaf).val.presheaf
        ⊤ y (by trivial) (1 : Γ(W.toScheme, ⊤)))) hh
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _
      (Modules.Hom.mapPresheaf (SheafOfModules.ιFree k ≫ f)) _).symm.trans
      (ht.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _
        (Modules.Hom.mapPresheaf (SheafOfModules.ιFree k ≫ g)) _))
  obtain ⟨V', _, hyV', heq'⟩ :=
    Modules.exists_restrict_eq_of_free_germs_eq y f g hg ⊤ (by trivial)
  let L := Modules.restrictFunctor V'.ι
  have hab : L.map ea = L.map eb := by
    calc
      L.map ea = L.map i ≫ L.map f := by
        simp only [f, ← L.map_comp, ← Category.assoc, hip]
        congr 1
      _ = L.map i ≫ L.map g := by rw [heq']
      _ = L.map eb := by
        simp only [g, ← L.map_comp, ← Category.assoc, hip]
        congr 1
  let V := W.ι ''ᵁ V'
  have hxV : x ∈ V := ⟨y, hyV', rfl⟩
  have hVW : V ≤ W := by
    intro t ht
    obtain ⟨z, hz, rfl⟩ := ht
    exact z.property
  let j := W.ι.isoImage V'
  let d := X.homOfLE hVW
  have hj : j.hom ≫ d = V'.ι := by
    apply (cancel_mono W.ι).mp
    simpa only [d, Category.assoc, Scheme.homOfLE_ι] using W.ι.isoImage_hom_ι V'
  have hd : (Modules.restrictFunctor d).map ea =
      (Modules.restrictFunctor d).map eb := by
    apply Modules.restrict_map_injective_of_isIso j.hom
    exact Modules.map_eq_of_iso
      (Modules.restrictFunctorCongr hj.symm ≪≫ Modules.restrictFunctorComp j.hom d) hab
  refine ⟨V, hVW, hxV, ?_⟩
  apply (Modules.overEquiv V).functor.map_injective
  exact Modules.map_eq_of_iso (Modules.overMapCompOverEquiv (homOfLE hVW)).symm hd

end
end AlgebraicGeometry.Scheme

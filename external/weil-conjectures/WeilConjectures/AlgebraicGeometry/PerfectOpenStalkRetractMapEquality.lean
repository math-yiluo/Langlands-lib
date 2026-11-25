/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
import all WeilConjectures.AlgebraicGeometry.FiniteFreeStalkMapEquality

/-! # Shrinking stalk equality for a finite retract sheaf

Source: Stacks Project, Tags 09RE, 0BC7 and 01CP.
(blueprint: lem-sc-perfect-open-stalk-retract-map-equality).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equality of endomorphisms of a finite free retract at one stalk holds nearby.
Source: Stacks Project, Tag 01CP, finite-type injectivity proof.
(blueprint: lem-sc-perfect-open-stalk-retract-map-equality).

Proof: Restrict the finite-free inclusion and retraction to Z and transport them
through the equivalence with module sheaves on the open subscheme. These functors
preserve the free coproduct and the splitting identity. Precompose a and b with
the resulting retraction from the finite free sheaf. Faithfulness of restriction
of scalars turns the hypothesis into equality of their module stalk maps. Evaluate
this equality on the germs of the finitely many global basis sections. The proved
finite-free germ calculation gives a common neighbourhood where the precomposed
maps agree. Precomposing with the inclusion and using the splitting identity gives
equality on the retract. Send the neighbourhood to X using the open immersion;
the restriction composition and over-site comparisons give exactly the requested
restriction equality. The empty basis is covered by the same coproduct argument.
No Noetherian hypothesis is used, and repeated equal opens are allowed. -/
theorem exists_open_stalk_retract_map_eq
    (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (hM : ∃ m : ℕ,
      ∃ (ι : M ⟶ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)))
        (π : SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)) ⟶ M),
        ι ≫ π = 𝟙 M)
    (x : X) (V Z : X.Opens) (hxZ : x ∈ Z) (hVU : V ≤ U) (hZV : Z ≤ V)
    (a b :
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hZV)).obj
        ((SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVU)).obj M) ⟶
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hZV)).obj
        ((SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVU)).obj M))
    (heq : (openModuleStalkFunctor X Z ⟨x, hxZ⟩).map a =
      (openModuleStalkFunctor X Z ⟨x, hxZ⟩).map b) :
    ∃ (W : X.Opens) (hWZ : W ≤ Z), x ∈ W ∧
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hWZ)).map a =
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hWZ)).map b := by
  classical
  obtain ⟨m, ι, π, hsplit⟩ := hM
  let R := SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVU) ⋙
    SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hZV)
  let E := (Modules.overEquiv Z).functor
  let T := R ⋙ E
  let y : Z.toScheme := ⟨x, hxZ⟩
  let S := RingedSpace.moduleStalkFunctor Z.toScheme.toRingedSpace y
  let N := E.obj (R.obj M)
  let ea := E.map a
  let eb := E.map b
  have hs : S.map ea = S.map eb := by
    exact (ModuleCat.restrictScalars (Z.ι.stalkMap y).hom).map_injective heq
  let eunit : SheafOfModules.unit Z.toScheme.ringCatSheaf ≅
      T.obj (SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)) :=
    (E.mapIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE hZV)).mapIso (SheafOfModules.overMapUnitIso (homOfLE hVU)) ≪≫
        SheafOfModules.overMapUnitIso (homOfLE hZV)) ≪≫
          (Modules.overEquivFunctorObjUnitIso Z).symm).symm
  have : PreservesColimitsOfShape (Discrete (ULift.{u} (Fin m))) T := by
    dsimp [T, R, E]
    infer_instance
  let e := SheafOfModules.mapFreeIso T (ULift.{u} (Fin m)) eunit
  let p := e.hom ≫ T.map π
  let i := T.map ι ≫ e.inv
  have hip : i ≫ p = 𝟙 N := by
    simp only [i, p, Category.assoc, Iso.inv_hom_id_assoc,
      ← T.map_comp, hsplit, T.map_id]
    rfl
  let f := p ≫ ea
  let g := p ≫ eb
  have hfg : S.map f = S.map g := by
    simp only [f, g, Functor.map_comp, hs]
  have hg (k : ULift.{u} (Fin m)) :
      N.presheaf.germ ⊤ y (by trivial)
        (Modules.Hom.app (SheafOfModules.ιFree k ≫ f) ⊤
          (1 : Γ(Z.toScheme, ⊤))) =
      N.presheaf.germ ⊤ y (by trivial)
        (Modules.Hom.app (SheafOfModules.ιFree k ≫ g) ⊤
          (1 : Γ(Z.toScheme, ⊤))) := by
    have hh := congrArg (fun t ↦ S.map (SheafOfModules.ιFree k) ≫ t) hfg
    rw [← Functor.map_comp, ← Functor.map_comp] at hh
    have ht := congrArg (fun t ↦ t
      (TopCat.Presheaf.germ (SheafOfModules.unit Z.toScheme.ringCatSheaf).val.presheaf
        ⊤ y (by trivial) (1 : Γ(Z.toScheme, ⊤)))) hh
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _
      (Modules.Hom.mapPresheaf (SheafOfModules.ιFree k ≫ f)) _).symm.trans
      (ht.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _
        (Modules.Hom.mapPresheaf (SheafOfModules.ιFree k ≫ g)) _))
  obtain ⟨W', _, hyW', heq'⟩ :=
    Modules.exists_restrict_eq_of_free_germs_eq y f g hg ⊤ (by trivial)
  let L := Modules.restrictFunctor W'.ι
  have hab : L.map ea = L.map eb := by
    calc
      L.map ea = L.map i ≫ L.map f := by
        simp only [f, ← L.map_comp, ← Category.assoc, hip]
        congr 1
      _ = L.map i ≫ L.map g := by rw [heq']
      _ = L.map eb := by
        simp only [g, ← L.map_comp, ← Category.assoc, hip]
        congr 1
  let W := Z.ι ''ᵁ W'
  have hxW : x ∈ W := ⟨y, hyW', rfl⟩
  have hWZ : W ≤ Z := by
    intro t ht
    obtain ⟨z, hz, rfl⟩ := ht
    exact z.property
  let j := Z.ι.isoImage W'
  let d := X.homOfLE hWZ
  have hj : j.hom ≫ d = W'.ι := by
    apply (cancel_mono Z.ι).mp
    simpa only [d, Category.assoc, Scheme.homOfLE_ι] using Z.ι.isoImage_hom_ι W'
  have hd : (Modules.restrictFunctor d).map ea =
      (Modules.restrictFunctor d).map eb := by
    apply Modules.restrict_map_injective_of_isIso j.hom
    exact Modules.map_eq_of_iso
      (Modules.restrictFunctorCongr hj.symm ≪≫ Modules.restrictFunctorComp j.hom d) hab
  refine ⟨W, hWZ, hxW, ?_⟩
  apply (Modules.overEquiv W).functor.map_injective
  exact Modules.map_eq_of_iso (Modules.overMapCompOverEquiv (homOfLE hWZ)).symm hd

end
end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Topology.PresheafStalkTensor
import Mathlib.Topology.Sheaves.Sheafify
import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-!
# Stalk of a tensor product of modules on a ringed space

Source: Stacks Project, Modules, Lemma 17.16.1 (Tag 01CB,
label lemma-stalk-tensor-product) (blueprint: lem-pc-ringed-space-module-stalk-tensor).
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite

universe u

namespace SheafOfModules

set_option autoImplicit false

noncomputable section

section Helpers

variable (X : AlgebraicGeometry.RingedSpace.{u}) (x : X)

set_option hygiene false in
local notation "𝓡" => (sheafCompose (Opens.grothendieckTopology X)
  (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf
@[instance_reducible] private noncomputable def tensorSheafMonoidal :
    MonoidalCategory (SheafOfModules.{u} 𝓡) := monoidalCategory X.sheaf
@[instance_reducible] private noncomputable def tensorPresheafMonoidal :
    MonoidalCategory (PresheafOfModules.{u} (𝓡).obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u}
    (X.presheaf ⋙ forget₂ CommRingCat RingCat)))
attribute [local instance] tensorSheafMonoidal tensorPresheafMonoidal

@[instance_reducible] private noncomputable def tensorSheafificationMonoidal :
    (PresheafOfModules.sheafification.{u} (𝟙 (𝓡).obj)).Monoidal :=
  sheafificationMonoidal.{u} (C := Opens X)
    (J := Opens.grothendieckTopology X) X.sheaf

attribute [local instance] tensorSheafificationMonoidal

private noncomputable abbrev tensorUnitMap (F G : SheafOfModules.{u} 𝓡) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡).obj)).unit.app (F.val ⊗ G.val) ≫
    (forget 𝓡).map (tensorObjIsoSheafification F G).inv

set_option backward.isDefEq.respectTransparency false in
private theorem commStalkMap_linear
    {M N : PresheafOfModules.{u} (𝓡).obj} (f : M ⟶ N)
    (r : X.presheaf.stalk x)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier) M.presheaf x) :
    PresheafOfModules.stalkAddMap f (r • m) = r • PresheafOfModules.stalkAddMap f m := by
  obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx r,
    ← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx m,
    ← PresheafOfModules.germ_smul (R := X.presheaf) M]
  dsimp only [PresheafOfModules.stalkAddMap]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change TopCat.Presheaf.germ N.presheaf _ x hx ((f.app _).hom (_ • _)) = _
  rw [map_smul, PresheafOfModules.germ_smul (R := X.presheaf) N]
  rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def commStalkFunctor :
    PresheafOfModules.{u} (𝓡).obj ⥤ ModuleCat.{u} (X.presheaf.stalk x) where
  obj M := ModuleCat.of _
    (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier) M.presheaf x)
  map f := ModuleCat.ofHom
    { toFun := PresheafOfModules.stalkAddMap f
      map_add' := (PresheafOfModules.stalkAddMap f).map_add
      map_smul' := commStalkMap_linear X x f }
  map_id M := by
    ext m
    change PresheafOfModules.stalkAddMap (𝟙 M) m = m
    simp [PresheafOfModules.stalkAddMap]
    rfl
  map_comp f g := by
    ext m
    change PresheafOfModules.stalkAddMap (f ≫ g) m =
      PresheafOfModules.stalkAddMap g (PresheafOfModules.stalkAddMap f m)
    simp [PresheafOfModules.stalkAddMap]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem tensorUnitMap_stalk_isIso (F G : SheafOfModules.{u} 𝓡) :
    IsIso ((commStalkFunctor X x).map (tensorUnitMap X F G)) := by
  let S := commStalkFunctor X x
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡).obj)
  have hu : IsIso (S.map (A.unit.app (F.val ⊗ G.val))) := by
    rw [← isIso_iff_of_reflects_iso _ (forget₂ _ AddCommGrpCat.{u})]
    change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (𝓡).obj).map (A.unit.app (F.val ⊗ G.val))))
    simp only [A, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x _ _
  change IsIso (S.map (A.unit.app (F.val ⊗ G.val) ≫
    (forget 𝓡).map (tensorObjIsoSheafification F G).inv))
  rw [S.map_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem tensorUnitMap_natural
    {F G F' G' : SheafOfModules.{u} 𝓡} (f : F ⟶ F') (g : G ⟶ G') :
    (f.val ⊗ₘ g.val) ≫ tensorUnitMap X F' G' =
      tensorUnitMap X F G ≫ (forget 𝓡).map (f ⊗ₘ g) := by
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡).obj)
  let H := forget 𝓡 ⋙ PresheafOfModules.restrictScalars (𝟙 (𝓡).obj)
  let : H.LaxMonoidal := A.rightAdjointLaxMonoidal
  have hn := Functor.LaxMonoidal.μ_natural H f g
  ext U m
  exact ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app U) hn) m

set_option backward.isDefEq.respectTransparency false in
private theorem stalkMap_germ {M N : PresheafOfModules.{u} (𝓡).obj}
    (f : M ⟶ N) (U : Opens X) (hx : x ∈ U) (s : M.obj (op U)) :
    (commStalkFunctor X x).map f
        (TopCat.Presheaf.germ M.presheaf U x hx s) =
      TopCat.Presheaf.germ N.presheaf U x hx (f.app (op U) s) := by
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf (𝓡).obj).map f) s

end Helpers

set_option backward.isDefEq.respectTransparency false in
/-- The canonical tensor comparison on stalks is linear and natural in both sheaves.
Source: Stacks Project, Modules, Lemma 17.16.1 (Tag 01CB)
(blueprint: lem-pc-ringed-space-module-stalk-tensor).

Proof:
1. Neighbourhoods of `x` are directed. Module stalks are colimits, with scalar action
   on germs as in `def-weil-pbc-module-stalk`; the presheaf tensor is sectionwise
   (`def-pur-sheaf-tensor-product`).
2. The sheafification unit induces an additive isomorphism on stalks
   (`def-weil-presheaf-modules-sheafification`, `lem-weil-pbc-stalk-sheafification-space`).
   Represent a scalar and a vector on a common neighbourhood to see it is linear.
3. Apply `lem-weil-pbc-filtered-colimit-tensor-varying-rings` to the rings and modules
   on neighbourhoods. This identifies the presheaf tensor stalk with the tensor of
   the stalks, sending the germ of a pure tensor to the tensor of its germs.
4. Compose this identification with the inverse of the sheafification stalk map.
   Pure tensor germs generate, so the displayed germ formula characterizes the map.
5. Both sides of the naturality equation send each pure tensor germ to the tensor
   of its image germs (`def-weil-pbc-module-stalk`). Generation gives equality. 
(blueprint: lem-weil-pbc-module-stalk-tensor)
-/
theorem stalkTensorIso (X : AlgebraicGeometry.RingedSpace.{u}) (x : X) :
    let R := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf
    letI := monoidalCategory X.sheaf
    let S := AlgebraicGeometry.RingedSpace.moduleStalkFunctor X x
    ∃ Φ : ∀ F G : SheafOfModules.{u} R, S.obj (F ⊗ G) ≅ S.obj F ⊗ S.obj G,
      (∀ (F G : SheafOfModules.{u} R) (U : Opens X) (hx : x ∈ U)
        (s : F.val.obj (op U)) (t : G.val.obj (op U)),
        let P := F.val ⊗ G.val
        let θ := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P ≫
          (forget R).map (tensorObjIsoSheafification F G).inv
        (Φ F G).hom (TopCat.Presheaf.germ (F ⊗ G).val.presheaf U x hx
          ((θ.app (op U)) (s ⊗ₜ[X.presheaf.obj (op U)] t))) =
          (TopCat.Presheaf.germ F.val.presheaf U x hx s) ⊗ₜ[X.presheaf.stalk x]
            (TopCat.Presheaf.germ G.val.presheaf U x hx t)) ∧
      (∀ (F G F' G' : SheafOfModules.{u} R) (f : F ⟶ F') (g : G ⟶ G'),
        S.map (f ⊗ₘ g) ≫ (Φ F' G').hom =
          (Φ F G).hom ≫ (S.map f ⊗ₘ S.map g)) := by
  let R := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf
  let := monoidalCategory X.sheaf
  let S := AlgebraicGeometry.RingedSpace.moduleStalkFunctor X x
  let T := commStalkFunctor X x
  -- The presheaf comparison is constructed directly from common-neighborhood germs.
  have he (F G : SheafOfModules.{u} R) :=
    PresheafOfModules.exists_stalk_tensor_iso X.presheaf x F.val G.val
  choose e he using he
  have hi (F G : SheafOfModules.{u} R) :
      IsIso (T.map (tensorUnitMap X F G)) := tensorUnitMap_stalk_isIso X x F G
  let Φ (F G : SheafOfModules.{u} R) : S.obj (F ⊗ G) ≅ S.obj F ⊗ S.obj G :=
    (asIso (T.map (tensorUnitMap X F G))).symm ≪≫ e F G
  refine ⟨Φ, ?_, ?_⟩
  · intro F G U hx s t
    change (Φ F G).hom (TopCat.Presheaf.germ (F ⊗ G).val.presheaf U x hx
      ((tensorUnitMap X F G).app (op U) (s ⊗ₜ[X.presheaf.obj (op U)] t))) = _
    have hg := stalkMap_germ X x (tensorUnitMap X F G) U hx
      (s ⊗ₜ[X.presheaf.obj (op U)] t)
    apply (congrArg (fun z ↦ (Φ F G).hom z) hg).symm.trans
    change ((T.map (tensorUnitMap X F G) ≫ (Φ F G).hom)
      (TopCat.Presheaf.germ (F.val ⊗ G.val).presheaf U x hx
        (s ⊗ₜ[X.presheaf.obj (op U)] t))) = _
    dsimp only [Φ, Iso.trans_hom, Iso.symm_hom, asIso_inv]
    rw [IsIso.hom_inv_id_assoc]
    exact he F G U hx s t
  · intro F G F' G' f g
    apply (cancel_epi (T.map (tensorUnitMap X F G))).mp
    have hn := congrArg T.map (tensorUnitMap_natural X f g)
    have hn' : T.map (f.val ⊗ₘ g.val) ≫ T.map (tensorUnitMap X F' G') =
        T.map (tensorUnitMap X F G) ≫ S.map (f ⊗ₘ g) := by
      have hST : T.map ((forget R).map (f ⊗ₘ g)) = S.map (f ⊗ₘ g) := by
        ext z
        rfl
      calc
        _ = T.map ((f.val ⊗ₘ g.val) ≫ tensorUnitMap X F' G') :=
          (T.map_comp _ _).symm
        _ = T.map (tensorUnitMap X F G ≫ (forget R).map (f ⊗ₘ g)) := hn
        _ = T.map (tensorUnitMap X F G) ≫ T.map ((forget R).map (f ⊗ₘ g)) :=
          T.map_comp _ _
        _ = _ := congrArg (T.map (tensorUnitMap X F G) ≫ ·) hST
    rw [← Category.assoc, ← hn', Category.assoc]
    change T.map (f.val ⊗ₘ g.val) ≫
        (T.map (tensorUnitMap X F' G') ≫ (Φ F' G').hom) =
      (T.map (tensorUnitMap X F G) ≫ (Φ F G).hom) ≫ (S.map f ⊗ₘ S.map g)
    have hcancel (A B : SheafOfModules.{u} R) :
        T.map (tensorUnitMap X A B) ≫ (Φ A B).hom = (e A B).hom := by
      dsimp only [Φ, Iso.trans_hom, Iso.symm_hom, asIso_inv]
      exact IsIso.hom_inv_id_assoc _ _
    rw [hcancel, hcancel]
    ext z
    obtain ⟨U, hx, z, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (F.val ⊗ G.val).presheaf z
    change (e F' G').hom (T.map (f.val ⊗ₘ g.val)
      (TopCat.Presheaf.germ (F.val ⊗ G.val).presheaf U x hx z)) =
      (S.map f ⊗ₘ S.map g) ((e F G).hom
        (TopCat.Presheaf.germ (F.val ⊗ G.val).presheaf U x hx z))
    change TensorProduct (X.presheaf.obj (op U)) (F.val.obj (op U)) (G.val.obj (op U)) at z
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
    | tmul s t =>
      have hg := stalkMap_germ X x (f.val ⊗ₘ g.val) U hx (s ⊗ₜ t)
      apply (congrArg (fun z ↦ (e F' G').hom z) hg).trans
      change (e F' G').hom (TopCat.Presheaf.germ (F'.val ⊗ G'.val).presheaf U x hx
        (f.val.app (op U) s ⊗ₜ[X.presheaf.obj (op U)] g.val.app (op U) t)) = _
      erw [he F' G' U hx, he F G U hx]
      change _ = TensorProduct.map (S.map f).hom (S.map g).hom _
      rw [TensorProduct.map_tmul]
      congr 1
      · exact (stalkMap_germ X x f.val U hx s).symm
      · exact (stalkMap_germ X x g.val U hx t).symm

end

end SheafOfModules

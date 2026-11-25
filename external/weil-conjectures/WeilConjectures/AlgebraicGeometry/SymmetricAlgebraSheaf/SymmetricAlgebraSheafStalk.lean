/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraSheafConstruction
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-! # Symmetric algebras commute with taking stalks

Source: Stacks Project, Modules, Lemma 01CH; Sheaves, Lemma 007K.
(blueprint: lem-pur-symmetric-algebra-sheaf-stalk).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.SymmetricAlgebraSheaf
noncomputable section
variable {X : Scheme.{u}} (F : X.Modules) (x : X)

private abbrev fiber := (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F

private def sectionToStalk (U : X.Opens) (hx : x ∈ U) :
    sections F (op U) →+*
      SymmetricAlgebra (X.presheaf.stalk x) (fiber F x) := by
  let B := SymmetricAlgebra (X.presheaf.stalk x) (fiber F x)
  let : Algebra Γ(X, U) B :=
    ((algebraMap (X.presheaf.stalk x) B).comp (X.presheaf.germ U x hx).hom).toAlgebra
  let l : F.val.obj (op U) →ₗ[Γ(X, U)] B :=
    { toFun := fun m ↦ SymmetricAlgebra.ι (X.presheaf.stalk x) (fiber F x)
        (TopCat.Presheaf.germ F.val.presheaf U x hx m)
      map_add' := by intros; simp
      map_smul' := by
        intro r m
        erw [PresheafOfModules.germ_smul (R := X.presheaf) F.val, map_smul]
        rfl }
  exact (SymmetricAlgebra.lift l).toRingHom

private theorem sectionToStalk_scalar (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
    sectionToStalk F x U hx (algebraMap _ _ r) =
      algebraMap (X.presheaf.stalk x)
        (SymmetricAlgebra (X.presheaf.stalk x) (fiber F x))
          (X.presheaf.germ U x hx r) := by
  let B := SymmetricAlgebra (X.presheaf.stalk x) (fiber F x)
  let : Algebra Γ(X, U) B :=
    ((algebraMap (X.presheaf.stalk x) B).comp (X.presheaf.germ U x hx).hom).toAlgebra
  unfold sectionToStalk
  exact AlgHom.commutes _ r

private theorem sectionToStalk_generator (U : X.Opens) (hx : x ∈ U)
    (m : F.val.obj (op U)) :
    sectionToStalk F x U hx (SymmetricAlgebra.ι Γ(X, U) (F.val.obj (op U)) m) =
      SymmetricAlgebra.ι (X.presheaf.stalk x) (fiber F x)
        (TopCat.Presheaf.germ F.val.presheaf U x hx m) := by
  let B := SymmetricAlgebra (X.presheaf.stalk x) (fiber F x)
  let : Algebra Γ(X, U) B :=
    ((algebraMap (X.presheaf.stalk x) B).comp (X.presheaf.germ U x hx).hom).toAlgebra
  unfold sectionToStalk
  exact SymmetricAlgebra.lift_ι_apply _ m

private theorem sectionToStalk_res (U V : X.Opens) (hVU : V ≤ U) (hx : x ∈ V)
    (a : sections F (op U)) :
    sectionToStalk F x V hx (restriction F (homOfLE hVU).op a) =
      sectionToStalk F x U (hVU hx) a := by
  induction a using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [restriction_algebraMap, sectionToStalk_scalar, sectionToStalk_scalar,
      X.presheaf.germ_res_apply]
  | ι m =>
    rw [restriction_ι, sectionToStalk_generator, sectionToStalk_generator]
    exact congrArg (SymmetricAlgebra.ι (X.presheaf.stalk x) (fiber F x))
      (TopCat.Presheaf.germ_res_apply F.val.presheaf (homOfLE hVU) x hx m)
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

private def presheafStalkMap : TopCat.Presheaf.stalk (presheaf F) x ⟶
    CommRingCat.of (SymmetricAlgebra (X.presheaf.stalk x) (fiber F x)) :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ presheaf F)
    { pt := CommRingCat.of (SymmetricAlgebra (X.presheaf.stalk x) (fiber F x))
      ι :=
        { app (U : (OpenNhds x)ᵒᵖ) := CommRingCat.ofHom (sectionToStalk F x U.unop.1 U.unop.2)
          naturality {U V} k := by
            apply CommRingCat.hom_ext
            ext a
            exact sectionToStalk_res F x U.unop.1 V.unop.1 k.unop.le V.unop.2 a } }

private theorem presheafStalkMap_germ (U : X.Opens) (hx : x ∈ U)
    (a : sections F (op U)) :
    presheafStalkMap F x (TopCat.Presheaf.germ (presheaf F) U x hx a) =
      sectionToStalk F x U hx a := by
  change (TopCat.Presheaf.germ (presheaf F) U x hx ≫ presheafStalkMap F x) a = _
  rw [show TopCat.Presheaf.germ (presheaf F) U x hx ≫ presheafStalkMap F x =
    CommRingCat.ofHom (sectionToStalk F x U hx) from colimit.ι_desc _ _]
  rfl

private def scalarStalk : X.presheaf.stalk x →+*
    TopCat.Presheaf.stalk (C := CommRingCat) (algebra F).right.obj x :=
  ((TopCat.Presheaf.stalkFunctor CommRingCat x).map (algebra F).hom.hom).hom

private theorem scalarStalk_germ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
    scalarStalk F x (X.presheaf.germ U x hx r) =
      TopCat.Presheaf.germ (algebra F).right.obj U x hx
        ((algebra F).hom.hom.app (op U) r) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (algebra F).hom.hom r

private def stalkInclusion : fiber F x →+
    TopCat.Presheaf.stalk (C := CommRingCat) (algebra F).right.obj x :=
  (colimit.desc ((OpenNhds.inclusion x).op ⋙ F.val.presheaf)
    { pt := AddCommGrpCat.of (TopCat.Presheaf.stalk (C := CommRingCat) (algebra F).right.obj x)
      ι :=
        { app (U : (OpenNhds x)ᵒᵖ) := AddCommGrpCat.ofHom
            ((TopCat.Presheaf.germ (algebra F).right.obj U.unop.1 x U.unop.2).hom
              |>.toAddMonoidHom.comp
                ((inclusion F).val.app (op U.unop.1)).hom.toAddMonoidHom)
          naturality {U V} k := by
            ext m
            change TopCat.Presheaf.germ (algebra F).right.obj V.unop.1 x V.unop.2
                ((inclusion F).val.app (op V.unop.1)
                  (F.val.map ((OpenNhds.inclusion x).map k.unop).op m)) =
              TopCat.Presheaf.germ (algebra F).right.obj U.unop.1 x U.unop.2
                ((inclusion F).val.app _ m)
            have hn := ConcreteCategory.congr_hom
              ((inclusion F).val.naturality ((OpenNhds.inclusion x).map k.unop).op) m
            change (inclusion F).val.app (op V.unop.1)
                (F.val.map ((OpenNhds.inclusion x).map k.unop).op m) =
              (algebra F).right.obj.map ((OpenNhds.inclusion x).map k.unop).op
                ((inclusion F).val.app (op U.unop.1) m) at hn
            rw [hn]
            exact TopCat.Presheaf.germ_res_apply (algebra F).right.obj
              ((OpenNhds.inclusion x).map k.unop) x V.unop.2 _ } }).hom

private theorem stalkInclusion_germ (U : X.Opens) (hx : x ∈ U)
    (m : F.val.obj (op U)) :
    stalkInclusion F x (TopCat.Presheaf.germ F.val.presheaf U x hx m) =
      TopCat.Presheaf.germ (algebra F).right.obj U x hx
        ((inclusion F).val.app (op U) m) := by
  unfold stalkInclusion
  change (colimit.ι ((OpenNhds.inclusion x).op ⋙ F.val.presheaf)
    (op (⟨U, hx⟩ : OpenNhds x)) ≫ _) m = _
  rw [colimit.ι_desc]
  rfl

private theorem stalkInclusion_smul (r : X.presheaf.stalk x) (m : fiber F x) :
    stalkInclusion F x (r • m) = scalarStalk F x r * stalkInclusion F x m := by
  obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
  have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left) x hx r,
    ← TopCat.Presheaf.germ_res_apply F.val.presheaf (homOfLE inf_le_right) x hx m]
  erw [← PresheafOfModules.germ_smul (R := X.presheaf) F.val,
    stalkInclusion_germ, stalkInclusion_germ, scalarStalk_germ]
  change TopCat.Presheaf.germ (algebra F).right.obj (U ⊓ V) x hx
      ((inclusion F).val.app _ (_ • _)) = _
  rw [map_smul]
  change TopCat.Presheaf.germ (algebra F).right.obj (U ⊓ V) x hx
    ((algebra F).hom.hom.app _ _ *
      (show (algebra F).right.obj.obj (op (U ⊓ V)) from
        (inclusion F).val.app _ _)) = _
  exact map_mul _ _ _

private def stalkInverse :
    SymmetricAlgebra (X.presheaf.stalk x) (fiber F x) →+*
      TopCat.Presheaf.stalk (C := CommRingCat) (algebra F).right.obj x := by
  let : Algebra (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := CommRingCat) (algebra F).right.obj x) :=
    (scalarStalk F x).toAlgebra
  let l : fiber F x →ₗ[X.presheaf.stalk x]
      TopCat.Presheaf.stalk (C := CommRingCat) (algebra F).right.obj x :=
    { (stalkInclusion F x) with map_smul' := stalkInclusion_smul F x }
  exact (SymmetricAlgebra.lift l).toRingHom

private theorem stalkInverse_scalar (r : X.presheaf.stalk x) :
    stalkInverse F x (algebraMap (X.presheaf.stalk x)
        (SymmetricAlgebra (X.presheaf.stalk x) (fiber F x)) r) = scalarStalk F x r := by
  let : Algebra (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := CommRingCat) (algebra F).right.obj x) :=
    (scalarStalk F x).toAlgebra
  unfold stalkInverse
  exact AlgHom.commutes _ r

private theorem stalkInverse_generator (m : fiber F x) :
    stalkInverse F x (SymmetricAlgebra.ι (X.presheaf.stalk x) (fiber F x) m) =
      stalkInclusion F x m := by
  let : Algebra (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := CommRingCat) (algebra F).right.obj x) :=
    (scalarStalk F x).toAlgebra
  unfold stalkInverse
  exact SymmetricAlgebra.lift_ι_apply _ m

private theorem stalkInverse_sectionToStalk (U : X.Opens) (hx : x ∈ U)
    (a : sections F (op U)) :
    stalkInverse F x (sectionToStalk F x U hx a) =
      TopCat.Presheaf.germ (algebra F).right.obj U x hx (sectionMap F (op U) a) := by
  induction a using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [sectionToStalk_scalar, stalkInverse_scalar, scalarStalk_germ]
    rfl
  | ι m =>
    rw [sectionToStalk_generator, stalkInverse_generator, stalkInclusion_germ]
    rfl
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The canonical stalk isomorphism for the symmetric algebra sheaf fixes scalar germs
and sends every germ of a degree-one generator to the generator of the module germ.
Source: Stacks Project, Modules, Lemma 01CH; Sheaves, Lemma 007K.
(blueprint: lem-pur-symmetric-algebra-sheaf-stalk).

Proof: On each neighbourhood send section scalars and module sections to their germs,
and extend to symmetric algebras. Compatibility with restriction gives a map from the
presheaf stalk. Ring sheafification has the same stalk. In the other direction the germs
of the sheaf's inclusion give a linear map from the module stalk into the algebra stalk;
the symmetric-algebra universal property extends it. The composites fix scalar germs
and generator germs. Symmetric-algebra induction and representation of stalk elements
by germs prove both inverse identities. No quasi-coherence or finiteness is needed. -/
theorem stalk_iso :
    ∃ e : TopCat.Presheaf.stalk (C := CommRingCat) (algebra F).right.obj x ≅
        CommRingCat.of (SymmetricAlgebra (X.presheaf.stalk x)
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)),
      (∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
        e.hom (TopCat.Presheaf.germ (algebra F).right.obj U x hx
          ((algebra F).hom.hom.app (op U) r)) =
            algebraMap (X.presheaf.stalk x)
              (SymmetricAlgebra (X.presheaf.stalk x)
                ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F))
                  (X.presheaf.germ U x hx r)) ∧
      ∀ (U : X.Opens) (hx : x ∈ U) (m : F.val.obj (op U)),
        e.hom (TopCat.Presheaf.germ (algebra F).right.obj U x hx
          ((inclusion F).val.app (op U) m)) =
            SymmetricAlgebra.ι (X.presheaf.stalk x)
              ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)
                (TopCat.Presheaf.germ F.val.presheaf U x hx m) := by
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat (presheaf F)
  let θ := asIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
    (toSheafify (Opens.grothendieckTopology X) (presheaf F)))
  let f := (presheafStalkMap F x).hom.comp θ.inv.hom
  have hfgerm (U : X.Opens) (hx : x ∈ U) (a : sections F (op U)) :
      f (TopCat.Presheaf.germ (algebra F).right.obj U x hx (sectionMap F (op U) a)) =
        sectionToStalk F x U hx a := by
    have hθ := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
      (toSheafify (Opens.grothendieckTopology X) (presheaf F)) a
    change θ.hom (TopCat.Presheaf.germ (presheaf F) U x hx a) =
      TopCat.Presheaf.germ (algebra F).right.obj U x hx (sectionMap F (op U) a) at hθ
    rw [← hθ]
    change presheafStalkMap F x (θ.inv (θ.hom _)) = _
    have hi (a) : θ.inv (θ.hom a) = a := congrArg (fun k ↦ k a) θ.hom_inv_id
    rw [hi]
    exact presheafStalkMap_germ F x U hx a
  have hleft (a : SymmetricAlgebra (X.presheaf.stalk x) (fiber F x)) :
      f (stalkInverse F x a) = a := by
    induction a using SymmetricAlgebra.induction with
    | algebraMap r =>
      obtain ⟨U, hx, r, rfl⟩ := X.presheaf.exists_germ_eq r
      rw [stalkInverse_scalar, scalarStalk_germ]
      change f (TopCat.Presheaf.germ (algebra F).right.obj U x hx
        (sectionMap F (op U) (algebraMap _ _ r))) = _
      rw [hfgerm, sectionToStalk_scalar]
    | ι m =>
      obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
      rw [stalkInverse_generator, stalkInclusion_germ]
      change f (TopCat.Presheaf.germ (algebra F).right.obj U x hx
        (sectionMap F (op U) (SymmetricAlgebra.ι _ _ m))) = _
      rw [hfgerm, sectionToStalk_generator]
    | mul a b ha hb => simp only [map_mul, ha, hb]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hright (a : TopCat.Presheaf.stalk (C := CommRingCat) (algebra F).right.obj x) :
      stalkInverse F x (f a) = a := by
    obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso θ.hom).2 a
    obtain ⟨U, hx, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq (presheaf F) b
    have hθ := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
      (toSheafify (Opens.grothendieckTopology X) (presheaf F)) b
    change θ.hom (TopCat.Presheaf.germ (presheaf F) U x hx b) =
      TopCat.Presheaf.germ (algebra F).right.obj U x hx (sectionMap F (op U) b) at hθ
    rw [hθ]
    change stalkInverse F x (f (TopCat.Presheaf.germ (algebra F).right.obj U x hx
      (sectionMap F (op U) b))) = _
    rw [hfgerm, stalkInverse_sectionToStalk]
  let e : TopCat.Presheaf.stalk (C := CommRingCat) (algebra F).right.obj x ≃+*
      SymmetricAlgebra (X.presheaf.stalk x) (fiber F x) :=
    { f with invFun := stalkInverse F x, left_inv := hright, right_inv := hleft }
  refine ⟨e.toCommRingCatIso, ?_, ?_⟩
  · intro U hx r
    exact (hfgerm U hx (algebraMap _ _ r)).trans (sectionToStalk_scalar F x U hx r)
  · intro U hx m
    exact (hfgerm U hx (SymmetricAlgebra.ι _ _ m)).trans
      (sectionToStalk_generator F x U hx m)

end
end AlgebraicGeometry.SymmetricAlgebraSheaf

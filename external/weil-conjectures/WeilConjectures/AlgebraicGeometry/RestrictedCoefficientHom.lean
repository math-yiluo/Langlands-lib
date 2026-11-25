/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # The coefficient action on an internal Hom

Source: Stacks Project, Algebraization, Tag 099I
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory Opposite

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
  (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
  (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

private abbrev scalarRestriction :=
  restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)

set_option backward.isDefEq.respectTransparency false in
private def sourceScalar (U : C) (b : B.obj.obj (op U)) :
    End ((PresheafOfModules.restrictOver R.obj U).obj
      ((scalarRestriction φ).obj M).val) := End.of {
  app W := ModuleCat.ofHom
    { toFun (m : M.val.obj (op W.unop.left)) := B.obj.map W.unop.hom.op b • m
      map_add' m n := by
        change M.val.obj (op W.unop.left) at m n
        exact smul_add _ m n
      map_smul' a m := by
        change M.val.obj (op W.unop.left) at m
        change (B.obj.map W.unop.hom.op b : B.obj.obj (op W.unop.left)) •
            ((φ.hom.app (op W.unop.left) a : B.obj.obj (op W.unop.left)) • m) =
          (φ.hom.app (op W.unop.left) a : B.obj.obj (op W.unop.left)) •
            ((B.obj.map W.unop.hom.op b : B.obj.obj (op W.unop.left)) • m)
        rw [← mul_smul, ← mul_smul, mul_comm] }
  naturality {W W'} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change M.val.obj (op W.unop.left) at m
    symm
    change M.val.map g.unop.left.op (B.obj.map W.unop.hom.op b • m) =
      @SMul.smul _ _ (M.val.obj (op W'.unop.left)).isModule.toSMul
        (B.obj.map W'.unop.hom.op b) (M.val.map g.unop.left.op m)
    rw [M.val.map_smul]
    have h := ConcreteCategory.congr_hom
      (B.obj.map_comp W.unop.hom.op g.unop.left.op) b
    rw [← op_comp, Over.w] at h
    exact congrArg (fun a ↦
      @SMul.smul _ _ (M.val.obj (op W'.unop.left)).isModule.toSMul a
        (M.val.map g.unop.left.op m)) h.symm }

private def coefficientHomSmul (U : C) (b : B.obj.obj (op U))
    (f : (PresheafOfModules.restrictOver R.obj U).obj ((scalarRestriction φ).obj M).val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj N.val) :=
  (sourceScalar φ M U b).asHom ≫ f

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible]
private def coefficientHomModule (U : C) :
    Module (B.obj.obj (op U))
      ((PresheafOfModules.restrictOver R.obj U).obj ((scalarRestriction φ).obj M).val ⟶
        (PresheafOfModules.restrictOver R.obj U).obj N.val) where
  smul := coefficientHomSmul φ M N U
  one_smul f := by
    ext W m
    change M.val.obj (op W.unop.left) at m
    change f.app W (B.obj.map W.unop.hom.op 1 • m) = f.app W m
    rw [map_one, one_smul]
  mul_smul b c f := by
    ext W m
    change M.val.obj (op W.unop.left) at m
    change f.app W (B.obj.map W.unop.hom.op (b * c) • m) =
      f.app W (B.obj.map W.unop.hom.op c • (B.obj.map W.unop.hom.op b • m))
    rw [map_mul, mul_comm, mul_smul]
  smul_zero b := by
    ext W m
    rfl
  smul_add b f g := by
    ext W m
    rfl
  zero_smul f := by
    ext W m
    change M.val.obj (op W.unop.left) at m
    change f.app W (B.obj.map W.unop.hom.op 0 • m) = 0
    rw [map_zero, zero_smul]
    exact (f.app W).hom.map_zero
  add_smul b c f := by
    ext W m
    change M.val.obj (op W.unop.left) at m
    change f.app W (B.obj.map W.unop.hom.op (b + c) • m) =
      f.app W (B.obj.map W.unop.hom.op b • m) +
        f.app W (B.obj.map W.unop.hom.op c • m)
    rw [map_add, add_smul]
    exact (f.app W).hom.map_add _ _

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientHom_restriction_linear
    {U V : C} (g : V ⟶ U) (b : B.obj.obj (op U))
    (f : (PresheafOfModules.restrictOver R.obj U).obj ((scalarRestriction φ).obj M).val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj N.val) :
    PresheafOfModules.restrictOverMap g (coefficientHomSmul φ M N U b f) =
      coefficientHomSmul φ M N V (B.obj.map g.op b)
        (PresheafOfModules.restrictOverMap g f) := by
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change M.val.obj (op W.unop.left) at m
  change f.app (op ((Over.map g).obj W.unop))
    (B.obj.map ((Over.map g).obj W.unop).hom.op b • m) =
      f.app (op ((Over.map g).obj W.unop))
        (B.obj.map W.unop.hom.op (B.obj.map g.op b) • m)
  exact congrArg (fun a ↦ f.app (op ((Over.map g).obj W.unop)) (a • m))
    (PresheafOfModules.overSections_coe_map_obj g b W)

private def coefficientHomObject (U : C) : ModuleCat.{u} (B.obj.obj (op U)) :=
  letI := coefficientHomModule φ M N U
  ModuleCat.of (B.obj.obj (op U))
    ((PresheafOfModules.restrictOver R.obj U).obj ((scalarRestriction φ).obj M).val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj N.val)

private def coefficientHomPresheaf :
    PresheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj where
  obj X := coefficientHomObject φ M N X.unop
  map {X Y} g := ConcreteCategory.ofHom
    { toFun f := PresheafOfModules.restrictOverMap g.unop f
      map_add' _ _ := rfl
      map_smul' b f := coefficientHom_restriction_linear φ M N g.unop b f }
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact PresheafOfModules.restrictOverMap_id f
  map_comp g h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact PresheafOfModules.restrictOverMap_comp g.unop h.unop f

private theorem coefficientHomPresheaf_isSheaf :
    Presheaf.IsSheaf J (coefficientHomPresheaf φ M N).presheaf := by
  change Presheaf.IsSheaf J
    (PresheafOfModules.homObj ((scalarRestriction φ).obj M).val N.val).presheaf
  exact PresheafOfModules.isSheaf_homObj N.isSheaf

private def coefficientHom :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) where
  val := coefficientHomPresheaf φ M N
  isSheaf := coefficientHomPresheaf_isSheaf φ M N

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientHomBase (U : C) (a : R.obj.obj (op U))
    (f : (PresheafOfModules.restrictOver R.obj U).obj ((scalarRestriction φ).obj M).val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj N.val) :
    coefficientHomSmul φ M N U (φ.hom.app (op U) a) f = a •
      (show (homObj.{u, u, u, u} ((scalarRestriction φ).obj M) N).val.obj (op U) from f) := by
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change M.val.obj (op W.unop.left) at m
  change f.app W (B.obj.map W.unop.hom.op (φ.hom.app (op U) a) • m) =
    R.obj.map W.unop.hom.op a • f.app W m
  have h := CategoryTheory.congr_fun (φ.hom.naturality W.unop.hom.op) a
  change φ.hom.app _ (R.obj.map W.unop.hom.op a) =
    B.obj.map W.unop.hom.op (φ.hom.app (op U) a) at h
  rw [← h]
  exact (f.app W).hom.map_smul (R.obj.map W.unop.hom.op a) m

private def scalarIdentity {A D V : Type u} [Ring A] [Ring D] [AddCommGroup V]
    [Module A V] [Module D V] (α : A →+* D)
    (h : ∀ (a : A) (v : V), α a • v = a • v) :
    (ModuleCat.restrictScalars α).obj (ModuleCat.of D V) ⟶ ModuleCat.of A V :=
  ConcreteCategory.ofHom
    { toFun v := v
      map_add' _ _ := rfl
      map_smul' a v := h a v }

private def coefficientHomComparison :
    (scalarRestriction φ).obj (coefficientHom φ M N) ⟶
      homObj.{u, u, u, u} ((scalarRestriction φ).obj M) N where
  val :=
    { app X :=
        letI : Module (B.obj.obj X)
            ((homObj.{u, u, u, u} ((scalarRestriction φ).obj M) N).val.obj X) :=
          coefficientHomModule φ M N X.unop
        scalarIdentity
          (V := (homObj.{u, u, u, u} ((scalarRestriction φ).obj M) N).val.obj X)
          (φ.hom.app X).hom (coefficientHomBase φ M N X.unop)
      naturality g := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        rfl }

set_option backward.isDefEq.respectTransparency false in
private def coefficientHomMap
    {M' : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)}
    {N' : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : M' ⟶ M) (g : N ⟶ N') :
    coefficientHom φ M N ⟶ coefficientHom φ M' N' where
  val := PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj).map
      (homObjMap ((scalarRestriction φ).map f) g).val) (by
        intro U b h
        apply PresheafOfModules.hom_ext
        intro W
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        change M'.val.obj (op W.unop.left) at m
        change g.val.app (op W.unop.left)
            (h.app W (B.obj.map W.unop.hom.op b • f.val.app (op W.unop.left) m)) =
          g.val.app (op W.unop.left)
            (h.app W (f.val.app (op W.unop.left) (B.obj.map W.unop.hom.op b • m)))
        rw [(f.val.app (op W.unop.left)).hom.map_smul])

private def coefficientHomFunctor :
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))ᵒᵖ ×
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
        SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) where
  obj X := coefficientHom φ X.1.unop X.2
  map f := coefficientHomMap φ _ _ f.1.unop f.2
  map_id X := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl
  map_comp f g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

private theorem coefficientHom_additive_right :
    ((Functor.curry.obj (coefficientHomFunctor φ)).obj (op M)).Additive := by
  constructor
  intro X Y f g
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rfl

private theorem coefficientHom_additive_left :
    ((Functor.curry.obj (coefficientHomFunctor φ)).flip.obj N).Additive := by
  constructor
  intro X Y f g
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change h.app W (f.unop.val.app (op W.unop.left) m +
      g.unop.val.app (op W.unop.left) m) = _
  exact (h.app W).hom.map_add _ _

private def scalarIdentityInv {A D V : Type u} [Ring A] [Ring D] [AddCommGroup V]
    [Module A V] [Module D V] (α : A →+* D)
    (h : ∀ (a : A) (v : V), α a • v = a • v) :
    ModuleCat.of A V ⟶ (ModuleCat.restrictScalars α).obj (ModuleCat.of D V) :=
  ConcreteCategory.ofHom
    { toFun v := v
      map_add' _ _ := rfl
      map_smul' a v := (h a v).symm }

private def coefficientHomComparisonIso :
    (scalarRestriction φ).obj (coefficientHom φ M N) ≅
      homObj.{u, u, u, u} ((scalarRestriction φ).obj M) N where
  hom := coefficientHomComparison φ M N
  inv :=
    { val :=
        { app X :=
            letI : Module (B.obj.obj X)
                ((homObj.{u, u, u, u} ((scalarRestriction φ).obj M) N).val.obj X) :=
              coefficientHomModule φ M N X.unop
            scalarIdentityInv
              (V := (homObj.{u, u, u, u} ((scalarRestriction φ).obj M) N).val.obj X)
              (φ.hom.app X).hom (coefficientHomBase φ M N X.unop)
          naturality g := by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro f
            rfl } }
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    rfl
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    rfl

/-- The internal Hom from a B-module to an R-module has a functorial B-module
structure whose restriction to R is naturally the usual internal Hom.
Source: Stacks Project, Algebraization, Tag 099I, the coefficient action on E prime
(auxiliary; not a blueprint node).
Proof: over U let b act on a local R-linear map by precomposing multiplication by
b on the B-module source. The commuting source endomorphisms give the module
laws. Restriction commutes with these actions, and the underlying additive
presheaf is the usual internal Hom, which is a sheaf. The R-action agrees with
postcomposition by R-linearity. Precomposition with B-linear maps and
postcomposition with R-linear maps are B-linear, giving the bifunctor. The
identity on local maps supplies the natural isomorphism after restriction.
Additivity separately in both variables follows from additivity of composition. -/
theorem exists_restrictedCoefficientHomFunctor :
    ∃ F :
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))ᵒᵖ ×
        SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
          SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B),
      ∃ i : F ⋙ restrictScalars.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) ≅
        ((restrictScalars.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).op.prod (𝟭 _) ⋙
          Functor.uncurry.obj (homFunctor.{u, u, u, u} R)),
        (∀ (M : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
          (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
          (U : C)
          (b : ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj.obj (op U))
          (h : (F.obj (op M, N)).val.obj (op U)) (W : Over U)
          (m : M.val.obj (op W.left)),
          (((i.hom.app (op M, N)).val.app (op U)).hom
            (@SMul.smul _ _ ((F.obj (op M, N)).val.obj (op U)).isModule.toSMul b h)).app (op W) m =
            (((i.hom.app (op M, N)).val.app (op U)).hom h).app (op W)
              (@SMul.smul _ _ (M.val.obj (op W.left)).isModule.toSMul
                (B.obj.map W.hom.op b) m)) ∧
        (∀ M, ((Functor.curry.obj F).obj M).Additive) ∧
        (∀ N, ((Functor.curry.obj F).flip.obj N).Additive) := by
  refine ⟨coefficientHomFunctor φ, NatIso.ofComponents (fun X ↦
    coefficientHomComparisonIso φ X.1.unop X.2) ?_, ?_, ?_, ?_⟩
  · intro X Y f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl
  · intro M N U b h W m
    rfl
  · intro M
    exact coefficientHom_additive_right φ M.unop
  · intro N
    exact coefficientHom_additive_left φ N

end SheafOfModules

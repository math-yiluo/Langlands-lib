/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-!
# The sheaf coinduction functor and action

Source: Stacks Project, Tag 0A6F and Tag 0BUZ.
(blueprint: lem-sc-sheaf-coinduction-action).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

private noncomputable abbrev actionRing {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
    RingCat.{u} _ _).obj Y.ringCatSheaf

private noncomputable abbrev actionSource {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  (SheafOfModules.restrictScalars.{u} f.toRingCatSheafHom).obj
    (SheafOfModules.unit (actionRing f))

private noncomputable abbrev actionHom {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens) :=
  (PresheafOfModules.restrictOver X.sheaf.obj U).obj (actionSource f).val ⟶
    (PresheafOfModules.restrictOver X.sheaf.obj U).obj F.val

set_option backward.isDefEq.respectTransparency false in
private noncomputable def actionMul {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    (a : (actionRing f).obj.obj (op U)) :
    (PresheafOfModules.restrictOver X.sheaf.obj U).obj (actionSource f).val ⟶
      (PresheafOfModules.restrictOver X.sheaf.obj U).obj (actionSource f).val where
  app W := ModuleCat.ofHom
    { toFun b := Mul.mul (α := (actionRing f).obj.obj (op W.unop.left))
        ((actionRing f).obj.map W.unop.hom.op a) b
      map_add' b c := by
        exact mul_add (R := (actionRing f).obj.obj (op W.unop.left)) _ b c
      map_smul' r b := by
        change (actionRing f).obj.obj (op W.unop.left) at b
        change (actionRing f).obj.map W.unop.hom.op a *
          (f.toRingCatSheafHom.hom.app (op W.unop.left) r * b) =
          f.toRingCatSheafHom.hom.app (op W.unop.left) r *
            ((actionRing f).obj.map W.unop.hom.op a * b)
        let : CommRing ((actionRing f).obj.obj (op W.unop.left)) :=
          inferInstanceAs (CommRing (Y.presheaf.obj
            (op ((TopologicalSpace.Opens.map f.base).obj W.unop.left))))
        exact mul_left_comm (G := (actionRing f).obj.obj (op W.unop.left)) _ _ _ }
  naturality {W W'} g := by
    ext b
    change (actionRing f).obj.obj (op W.unop.left) at b
    change Mul.mul (α := (actionRing f).obj.obj (op W'.unop.left))
      ((actionRing f).obj.map W'.unop.hom.op a)
      ((actionRing f).obj.map g.unop.left.op b) =
      (actionRing f).obj.map g.unop.left.op
        (Mul.mul (α := (actionRing f).obj.obj (op W.unop.left))
          ((actionRing f).obj.map W.unop.hom.op a) b)
    have h := RingCat.comp_apply ((actionRing f).obj.map W.unop.hom.op)
      ((actionRing f).obj.map g.unop.left.op) a
    rw [← Functor.map_comp, ← op_comp, Over.w] at h
    exact (congrArg (fun x : (actionRing f).obj.obj (op W'.unop.left) ↦
      x * (actionRing f).obj.map g.unop.left.op b) h).trans
        (((actionRing f).obj.map g.unop.left.op).hom.map_mul _ b).symm

-- The larger ring acts by precomposition with multiplication on the source.
private noncomputable def actionSmul {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
    (a : (actionRing f).obj.obj (op U))
    (φ : actionHom f F U) :
    actionHom f F U :=
  actionMul f U a ≫ φ

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible]
private noncomputable def actionModule {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens) :
    Module ((actionRing f).obj.obj (op U))
      (actionHom f F U) where
  smul := actionSmul f F U
  one_smul φ := by
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change (actionRing f).obj.obj (op W.unop.left) at b
    change φ.app W (Mul.mul (α := (actionRing f).obj.obj (op W.unop.left))
      ((actionRing f).obj.map W.unop.hom.op 1) b) = φ.app W b
    exact congrArg (φ.app W) ((congrArg
      (fun r : (actionRing f).obj.obj (op W.unop.left) ↦ r * b)
      ((actionRing f).obj.map W.unop.hom.op).hom.map_one).trans (one_mul b))
  mul_smul a c φ := by
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change (actionRing f).obj.obj (op W.unop.left) at b
    change φ.app W ((actionRing f).obj.map W.unop.hom.op (a * c) * b) =
      φ.app W ((actionRing f).obj.map W.unop.hom.op c *
        ((actionRing f).obj.map W.unop.hom.op a * b))
    rw [((actionRing f).obj.map W.unop.hom.op).hom.map_mul]
    congr 1
    let : CommRing ((actionRing f).obj.obj (op W.unop.left)) :=
      inferInstanceAs (CommRing (Y.presheaf.obj
        (op ((TopologicalSpace.Opens.map f.base).obj W.unop.left))))
    exact (mul_assoc (G := (actionRing f).obj.obj (op W.unop.left)) _ _ _).trans
      (mul_left_comm (G := (actionRing f).obj.obj (op W.unop.left)) _ _ _)
  smul_zero a := by
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    rfl
  smul_add a φ ψ := by
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    rfl
  add_smul a c φ := by
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change (actionRing f).obj.obj (op W.unop.left) at b
    change φ.app W ((actionRing f).obj.map W.unop.hom.op (a + c) * b) =
      φ.app W ((actionRing f).obj.map W.unop.hom.op a * b) +
        φ.app W ((actionRing f).obj.map W.unop.hom.op c * b)
    rw [((actionRing f).obj.map W.unop.hom.op).hom.map_add, add_mul]
    exact (φ.app W).hom.map_add _ _
  zero_smul φ := by
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change (actionRing f).obj.obj (op W.unop.left) at b
    change φ.app W (Mul.mul (α := (actionRing f).obj.obj (op W.unop.left))
      ((actionRing f).obj.map W.unop.hom.op 0) b) = 0
    exact (congrArg (φ.app W) ((congrArg
      (fun r : (actionRing f).obj.obj (op W.unop.left) ↦ r * b)
      ((actionRing f).obj.map W.unop.hom.op).hom.map_zero).trans (zero_mul _))).trans
        (φ.app W).hom.map_zero

set_option backward.isDefEq.respectTransparency false in
private theorem actionRestrict {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) {U V : X.Opens} (g : V ⟶ U)
    (a : (actionRing f).obj.obj (op U))
    (φ : actionHom f F U) :
    PresheafOfModules.restrictOverMap g (actionSmul f F U a φ) =
      actionSmul f F V ((actionRing f).obj.map g.op a)
        (PresheafOfModules.restrictOverMap g φ) := by
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  change (actionRing f).obj.obj (op W.unop.left) at b
  change φ.app (op ((Over.map g).obj W.unop))
    ((actionRing f).obj.map (W.unop.hom ≫ g).op a * b) =
    φ.app (op ((Over.map g).obj W.unop))
      ((actionRing f).obj.map W.unop.hom.op ((actionRing f).obj.map g.op a) * b)
  have h := RingCat.comp_apply ((actionRing f).obj.map g.op)
    ((actionRing f).obj.map W.unop.hom.op) a
  rw [← Functor.map_comp, ← op_comp] at h
  exact congrArg (fun r : (actionRing f).obj.obj (op W.unop.left) ↦
    φ.app (op ((Over.map g).obj W.unop)) (r * b)) h

private noncomputable def actionFiber {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens) :
    ModuleCat.{u} ((actionRing f).obj.obj (op U)) := by
  letI := actionModule f F U
  exact ModuleCat.of ((actionRing f).obj.obj (op U))
    (actionHom f F U)

private noncomputable def actionPresheaf {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) :
    PresheafOfModules.{u} (actionRing f).obj where
  obj U := actionFiber f F U.unop
  map {U V} g := ConcreteCategory.ofHom
    { toFun φ := PresheafOfModules.restrictOverMap g.unop φ
      map_add' _ _ := rfl
      map_smul' a φ := actionRestrict f F g.unop a φ }
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    exact PresheafOfModules.restrictOverMap_id φ
  map_comp g h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    exact PresheafOfModules.restrictOverMap_comp g.unop h.unop φ

-- The additive presheaf is the existing internal Hom, so its sheaf proof applies.
private noncomputable def actionSheaf {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) : SheafOfModules.{u} (actionRing f) where
  val := actionPresheaf f F
  isSheaf := (SheafOfModules.homObj (R := X.sheaf) (actionSource f) F).isSheaf

set_option backward.isDefEq.respectTransparency false in
private theorem actionBase {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
    (r : X.ringCatSheaf.obj.obj (op U))
    (φ : actionHom f F U) :
    actionSmul f F U (f.toRingCatSheafHom.hom.app (op U) r) φ = r •
      (show (SheafOfModules.homObj (R := X.sheaf) (actionSource f) F).val.obj (op U)
        from φ) := by
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  change (actionRing f).obj.obj (op W.unop.left) at b
  change φ.app W ((actionRing f).obj.map W.unop.hom.op
    (f.toRingCatSheafHom.hom.app (op U) r) * b) =
    X.ringCatSheaf.obj.map W.unop.hom.op r •
      (show F.val.obj (op W.unop.left) from φ.app W b)
  have h := ConcreteCategory.congr_hom
    (f.toRingCatSheafHom.hom.naturality W.unop.hom.op) r
  change f.toRingCatSheafHom.hom.app (op W.unop.left)
    (X.ringCatSheaf.obj.map W.unop.hom.op r) =
      (actionRing f).obj.map W.unop.hom.op
        (f.toRingCatSheafHom.hom.app (op U) r) at h
  exact (congrArg (fun a : (actionRing f).obj.obj (op W.unop.left) ↦
    φ.app W (a * b)) h.symm).trans
      ((φ.app W).hom.map_smul (X.ringCatSheaf.obj.map W.unop.hom.op r) b)

private noncomputable def actionMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    {F G : SheafOfModules.{u} X.ringCatSheaf} (g : F ⟶ G) :
    actionSheaf f F ⟶ actionSheaf f G where
  val :=
    { app U := ConcreteCategory.ofHom
        (show (actionSheaf f F).val.obj U →ₗ[(actionRing f).obj.obj U]
          (actionSheaf f G).val.obj U from
        { toFun (φ : actionHom f F U.unop) :=
            φ ≫ (PresheafOfModules.restrictOver X.sheaf.obj U.unop).map g.val
          map_add' φ ψ := Preadditive.add_comp _ _ _
            (φ : actionHom f F U.unop) (ψ : actionHom f F U.unop) _
          map_smul' a φ := by
            all_goals rfl })
      naturality {U V} h := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        rfl }

private noncomputable def actionFunctor {X Y : Scheme.{u}} (f : Y ⟶ X) :
    SheafOfModules.{u} X.ringCatSheaf ⥤ SheafOfModules.{u} (actionRing f) where
  obj := actionSheaf f
  map := actionMap f
  map_id F := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change φ ≫ (PresheafOfModules.restrictOver X.sheaf.obj U.unop).map (𝟙 F.val) = φ
    exact (congrArg (fun ψ ↦ φ ≫ ψ)
      ((PresheafOfModules.restrictOver X.sheaf.obj U.unop).map_id F.val)).trans
        (Category.comp_id φ)
  map_comp g h := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change φ ≫ (PresheafOfModules.restrictOver X.sheaf.obj U.unop).map (g.val ≫ h.val) =
      (φ ≫ (PresheafOfModules.restrictOver X.sheaf.obj U.unop).map g.val) ≫
        (PresheafOfModules.restrictOver X.sheaf.obj U.unop).map h.val
    simp only [Functor.map_comp, Category.assoc]

private noncomputable abbrev actionRestricted {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) :=
  (SheafOfModules.restrictScalars.{u} f.toRingCatSheafHom).obj (actionSheaf f F)

-- Abstract scalar compatibility keeps the identity maps small to elaborate.
private noncomputable def scalarIdentity {R S V : Type u} [Ring R] [Ring S] [AddCommGroup V]
    [Module R V] [Module S V] (α : R →+* S)
    (h : ∀ (r : R) (v : V), α r • v = r • v) :
    (ModuleCat.restrictScalars α).obj (ModuleCat.of S V) ⟶ ModuleCat.of R V :=
  ConcreteCategory.ofHom
    { toFun v := v
      map_add' _ _ := rfl
      map_smul' r v := h r v }

private noncomputable def scalarIdentityInv {R S V : Type u} [Ring R] [Ring S] [AddCommGroup V]
    [Module R V] [Module S V] (α : R →+* S)
    (h : ∀ (r : R) (v : V), α r • v = r • v) :
    ModuleCat.of R V ⟶ (ModuleCat.restrictScalars α).obj (ModuleCat.of S V) :=
  ConcreteCategory.ofHom
    { toFun v := v
      map_add' _ _ := rfl
      map_smul' r v := (h r v).symm }

private noncomputable def actionIdentityHom {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opensᵒᵖ) :
    (actionRestricted f F).val.obj U ⟶
      (SheafOfModules.homObj (R := X.sheaf) (actionSource f) F).val.obj U :=
  letI : Module ((actionRing f).obj.obj U)
      ((SheafOfModules.homObj (R := X.sheaf) (actionSource f) F).val.obj U) :=
    actionModule f F U.unop
  scalarIdentity (V := (SheafOfModules.homObj (R := X.sheaf)
    (actionSource f) F).val.obj U) (f.toRingCatSheafHom.hom.app U).hom
      (actionBase f F U.unop)

private noncomputable def actionIdentityInv {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opensᵒᵖ) :
    (SheafOfModules.homObj (R := X.sheaf) (actionSource f) F).val.obj U ⟶
      (actionRestricted f F).val.obj U :=
  letI : Module ((actionRing f).obj.obj U)
      ((SheafOfModules.homObj (R := X.sheaf) (actionSource f) F).val.obj U) :=
    actionModule f F U.unop
  scalarIdentityInv (V := (SheafOfModules.homObj (R := X.sheaf)
    (actionSource f) F).val.obj U) (f.toRingCatSheafHom.hom.app U).hom
      (actionBase f F U.unop)

private noncomputable def actionIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) :
    (SheafOfModules.restrictScalars.{u} f.toRingCatSheafHom).obj (actionSheaf f F) ≅
      SheafOfModules.homObj (R := X.sheaf) (actionSource f) F where
  hom :=
    { val :=
        { app U := actionIdentityHom f F U
          naturality h := by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro φ
            rfl } }
  inv :=
    { val :=
        { app U := actionIdentityInv f F U
          naturality h := by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro φ
            rfl } }
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    rfl
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    rfl

private noncomputable def actionNatIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
    actionFunctor f ⋙ SheafOfModules.restrictScalars.{u} f.toRingCatSheafHom ≅
      (SheafOfModules.homFunctor X.sheaf).obj (op (actionSource f)) :=
  NatIso.ofComponents (actionIso f) (fun g ↦ by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    rfl)

/-- Restriction of scalars admits a functor lifting internal Hom to modules over the
larger ring sheaf, with the multiplication action formula. No adjunction is asserted here.

Source: Stacks Project, Modules, Tag 0A6F, lemma-adjoint-tensor-restrict;
Duality, Tag 0BUZ, lemma-compute-sheafhom-affine.
(blueprint: lem-sc-sheaf-coinduction-action).

Proof: For an O_X-module F and open U, take the additive group
Hom_{O_X|U}(A|U,F|U). For a in A(U), precompose a section phi with the
O_X-linear endomorphism of A|U which on W sends b to a|W * b. This is
O_X-linear since A is commutative and the scalar map is a ring map.
These endomorphisms commute with restriction. The identities for addition,
zero, one and multiplication give the A(U)-module laws (commutativity
removes the order reversal from precomposition). Restricting the A-action
along f-sharp gives the existing O_X action on internal Hom, by O_X-linearity
of phi. The restriction maps are additive and semilinear for A, so these
modules form a presheaf. Its additive presheaf is exactly the internal Hom
presheaf; the existing internal Hom sheaf condition makes it an A-module
sheaf. For F -> F', postcomposition defines an A-linear natural morphism.
Identity and composition hold componentwise, yielding H. After restriction
of scalars the identity maps give the natural isomorphism i to K. Unfolding
precomposition gives the claimed action formula. This works also for empty
opens and zero rings, where all modules concerned have the forced zero action. -/
theorem sheafHom_restrictScalars_with_action
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    let A := ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      RingCat.{u} _ _).obj Y.ringCatSheaf
    let T := SheafOfModules.restrictScalars.{u} f.toRingCatSheafHom
    let M := T.obj (SheafOfModules.unit A)
    let K := (SheafOfModules.homFunctor X.sheaf).obj (op M)
    ∃ H : SheafOfModules.{u} X.ringCatSheaf ⥤ SheafOfModules.{u} A,
      ∃ i : H ⋙ T ≅ K,
        ∀ (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
          (a : A.obj.obj (op U)) (φ : (H.obj F).val.obj (op U))
          (W : Over U) (b : A.obj.obj (op W.left)),
          (((i.hom.app F).val.app (op U)).hom (a • φ)).app (op W) b =
            (((i.hom.app F).val.app (op U)).hom φ).app (op W)
              (A.obj.map W.hom.op a * b) := by
  refine ⟨actionFunctor f, actionNatIso f, ?_⟩
  intro F U a φ W b
  rfl

end AlgebraicGeometry

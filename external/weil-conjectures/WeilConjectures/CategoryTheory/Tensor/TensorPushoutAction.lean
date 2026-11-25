/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Scalar actions on a sheafified balanced tensor product

The sectionwise tensor action extends through sheafification. Its normalization
on the two scalar factors determines it uniquely.

Source: Stacks Project, Tag 03EK.
(blueprint: lem-pur-tensor-pushout-action)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u vC uC
open CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings
namespace CategoryTheory

section
variable {A B R V : Type u} [CommRing A] [CommRing B] [CommRing R]
  [AddCommGroup V] [Module R V] (a : A →+* R) (b : A →+* B)
@[instance_reducible]
private noncomputable def tensorAction :
    letI := b.toAlgebra
    letI := a.toAlgebra
    letI := Module.compHom V a
    Module (B ⊗[A] R) (B ⊗[A] V) := by
  letI := b.toAlgebra
  letI := a.toAlgebra
  letI := Module.compHom V a
  letI : IsScalarTower A R V := ⟨fun x y z ↦ mul_smul (a x) y z⟩
  letI : SMulCommClass A R V := ⟨fun x y z ↦ by
    change a x • y • z = y • a x • z
    rw [← mul_smul, mul_comm, mul_smul]⟩
  let f : B ⊗[A] R →ₐ[B] B ⊗[A] Module.End A V :=
    Algebra.TensorProduct.map (AlgHom.id B B) (Algebra.lsmul A A V)
  exact Module.compHom (B ⊗[A] V)
    ((LinearMap.tensorProductEnd A B V).toRingHom.comp f.toRingHom)
private theorem tensorAction_tmul (s t : B) (r : R) (v : V) :
    letI := b.toAlgebra
    letI := a.toAlgebra
    letI := Module.compHom V a
    letI := tensorAction (V := V) a b
    (s ⊗ₜ[A] r) • (t ⊗ₜ[A] v) = (s * t) ⊗ₜ[A] (r • v) := by
  let := b.toAlgebra
  let := a.toAlgebra
  let := Module.compHom V a
  let : IsScalarTower A R V := ⟨fun x y z ↦ mul_smul (a x) y z⟩
  let : SMulCommClass A R V := ⟨fun x y z ↦ by
    change a x • y • z = y • a x • z
    rw [← mul_smul, mul_comm, mul_smul]⟩
  change LinearMap.tensorProductEnd A B V
    ((Algebra.TensorProduct.map (AlgHom.id B B) (Algebra.lsmul A A V))
      (s ⊗ₜ[A] r)) (t ⊗ₜ[A] v) = _
  simp only [LinearMap.tensorProductEnd, Algebra.TensorProduct.algHomOfLinearMapTensorProduct_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearMap.tensorProduct,
    TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul,
    LinearMap.coe_restrictScalars, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.smul_apply, LinearMap.baseChangeHom_apply, LinearMap.baseChange_tmul]
  rfl

end

section Sheaf
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {A B R T : Sheaf J CommRingCat.{u}} (a : A ⟶ R) (b : A ⟶ B)
  (c : R ⟶ T) (d : B ⟶ T)
  (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

private abbrev restricted :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj M

private abbrev rawTensor :=
  SheafOfModules.changeOfRingsPresheafOfUniverses b (restricted a M)

private abbrev tensorSheaf :=
  SheafOfModules.changeOfRingsOfUniverses b (restricted a M)

private noncomputable def rawUnit : (rawTensor a b M).presheaf ⟶
    (tensorSheaf a b M).val.presheaf :=
  (PresheafOfModules.toPresheaf _).map
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).unit.app
        (rawTensor a b M))

@[instance_reducible]
private noncomputable def rawAction (q : ∀ U : Cᵒᵖ,
    letI := (b.hom.app U).hom.toAlgebra
    letI := (a.hom.app U).hom.toAlgebra
    B.obj.obj U ⊗[A.obj.obj U] R.obj.obj U ≃+* T.obj.obj U) (U : Cᵒᵖ) :
    Module (T.obj.obj U) ((rawTensor a b M).obj U) := by
  letI := (b.hom.app U).hom.toAlgebra
  letI := (a.hom.app U).hom.toAlgebra
  letI := tensorAction (V := M.val.obj U) (a.hom.app U).hom (b.hom.app U).hom
  letI := Module.compHom (M.val.obj U) (a.hom.app U).hom
  change Module (T.obj.obj U)
    (B.obj.obj U ⊗[A.obj.obj U] (M.val.obj U))
  exact Module.compHom (R := B.obj.obj U ⊗[A.obj.obj U] R.obj.obj U)
    _ (q U).symm.toRingHom

private theorem rawAction_tmul (e : ∀ U : Cᵒᵖ,
    letI := (b.hom.app U).hom.toAlgebra
    letI := (a.hom.app U).hom.toAlgebra
    B.obj.obj U ⊗[A.obj.obj U] R.obj.obj U ≃+* T.obj.obj U)
    (he : ∀ (U : Cᵒᵖ) (s : B.obj.obj U) (r : R.obj.obj U),
      letI := (b.hom.app U).hom.toAlgebra
      letI := (a.hom.app U).hom.toAlgebra
      e U (s ⊗ₜ[A.obj.obj U] r) = d.hom.app U s * c.hom.app U r) (U : Cᵒᵖ) (s t : B.obj.obj U)
    (r : R.obj.obj U) (x : M.val.obj U) :
    letI := (b.hom.app U).hom.toAlgebra
    letI := (a.hom.app U).hom.toAlgebra
    letI := Module.compHom (M.val.obj U) (a.hom.app U).hom
    letI := rawAction (T := T) a b M e U
    @SMul.smul _ _ (rawAction (T := T) a b M e U).toSMul
      (d.hom.app U s * c.hom.app U r)
      (t ⊗ₜ[A.obj.obj U, (b.hom.app U).hom] x) =
      (s * t) ⊗ₜ[A.obj.obj U, (b.hom.app U).hom] (r • x) := by
  let := (b.hom.app U).hom.toAlgebra
  let := (a.hom.app U).hom.toAlgebra
  let := Module.compHom (M.val.obj U) (a.hom.app U).hom
  let := tensorAction (V := M.val.obj U) (a.hom.app U).hom (b.hom.app U).hom
  rw [← he U]
  change (e U).symm (e U (s ⊗ₜ[A.obj.obj U] r)) •
    (t ⊗ₜ[A.obj.obj U, (b.hom.app U).hom] x) = _
  rw [RingEquiv.symm_apply_apply]
  exact tensorAction_tmul (a.hom.app U).hom (b.hom.app U).hom s t r x

private theorem rawAction_left (e : ∀ U : Cᵒᵖ,
    letI := (b.hom.app U).hom.toAlgebra
    letI := (a.hom.app U).hom.toAlgebra
    B.obj.obj U ⊗[A.obj.obj U] R.obj.obj U ≃+* T.obj.obj U)
    (he : ∀ (U : Cᵒᵖ) (s : B.obj.obj U) (r : R.obj.obj U),
      letI := (b.hom.app U).hom.toAlgebra
      letI := (a.hom.app U).hom.toAlgebra
      e U (s ⊗ₜ[A.obj.obj U] r) = d.hom.app U s * c.hom.app U r) (U : Cᵒᵖ) (s : B.obj.obj U)
    (x : (rawTensor a b M).obj U) :
    @SMul.smul _ _ (rawAction a b M e U).toSMul (d.hom.app U s) x = s • x := by
  let := (b.hom.app U).hom.toAlgebra
  let := (a.hom.app U).hom.toAlgebra
  let := Module.compHom (M.val.obj U) (a.hom.app U).hom
  let := rawAction a b M e U
  change (d.hom.app U s) • x = s • x
  dsimp only [sheafCompose] at *
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [smul_add, hx, hy]
  | tmul t m =>
    have h := rawAction_tmul a b c d M e he U s t 1 m
    have hb := ModuleCat.ExtendScalars.smul_tmul (b.hom.app U).hom s t
      (show (restricted a M).val.obj U from m)
    simp only [map_one, mul_one, one_smul] at h
    exact h.trans hb.symm

private theorem rawAction_restriction (e : ∀ U : Cᵒᵖ,
    letI := (b.hom.app U).hom.toAlgebra
    letI := (a.hom.app U).hom.toAlgebra
    B.obj.obj U ⊗[A.obj.obj U] R.obj.obj U ≃+* T.obj.obj U)
    (he : ∀ (U : Cᵒᵖ) (s : B.obj.obj U) (r : R.obj.obj U),
      letI := (b.hom.app U).hom.toAlgebra
      letI := (a.hom.app U).hom.toAlgebra
      e U (s ⊗ₜ[A.obj.obj U] r) = d.hom.app U s * c.hom.app U r) {U V : Cᵒᵖ} (f : U ⟶ V)
    (z : T.obj.obj U) (x : (rawTensor a b M).obj U) :
    letI := rawAction (T := T) a b M e U
    letI := rawAction (T := T) a b M e V
    (rawTensor a b M).map f (@SMul.smul _ _
      (rawAction (T := T) a b M e U).toSMul z x) =
      @SMul.smul _ _ (rawAction (T := T) a b M e V).toSMul
        (T.obj.map f z) ((rawTensor a b M).map f x) := by
  let (W : Cᵒᵖ) := (b.hom.app W).hom.toAlgebra
  let (W : Cᵒᵖ) := (a.hom.app W).hom.toAlgebra
  let (W : Cᵒᵖ) := Module.compHom (M.val.obj W) (a.hom.app W).hom
  let : Module (T.obj.obj U) ((rawTensor a b M).obj U) := rawAction a b M e U
  let : Module (T.obj.obj V) ((rawTensor a b M).obj V) := rawAction a b M e V
  change (rawTensor a b M).map f (z • x) =
    T.obj.map f z • (show (rawTensor a b M).obj V from (rawTensor a b M).map f x)
  dsimp only [sheafCompose] at *
  obtain ⟨w, rfl⟩ := (e U).surjective z
  induction w using TensorProduct.inductionOn with
  | add w w' hw hw' => simp only [map_add, add_smul, hw, hw']
  | tmul s r =>
    rw [he U]
    have hc (r : R.obj.obj U) :
        T.obj.map f (c.hom.app U r) = c.hom.app V (R.obj.map f r) :=
      ConcreteCategory.congr_hom (c.hom.naturality f).symm r
    have hd (s : B.obj.obj U) :
        T.obj.map f (d.hom.app U s) = d.hom.app V (B.obj.map f s) :=
      ConcreteCategory.congr_hom (d.hom.naturality f).symm s
    rw [map_mul, hd, hc]
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul t m =>
      change B.obj.obj U at t
      change M.val.obj U at m
      have hU := rawAction_tmul a b c d M e he U s t r m
      have hV := rawAction_tmul a b c d M e he V (B.obj.map f s)
        (B.obj.map f t) (R.obj.map f r) (M.val.map f m)
      dsimp only [sheafCompose] at hU hV
      refine (congrArg ((rawTensor a b M).map f) hU).trans ?_
      refine (SheafOfModules.changeOfRingsMap_tmulOfUniverses b (restricted a M) f
        (s * t) (r • m)).trans ?_
      have hmap := SheafOfModules.changeOfRingsMap_tmulOfUniverses b
        (restricted a M) f t m
      have hsmul := congrArg (fun y : (rawTensor a b M).obj V ↦
        (d.hom.app V (B.obj.map f s) * c.hom.app V (R.obj.map f r)) • y) hmap
      refine Eq.trans ?_ (hV.symm.trans hsmul.symm)
      rw [map_mul]
      exact congrArg (fun y : M.val.obj V ↦
        (B.obj.map f s * B.obj.map f t) ⊗ₜ[A.obj.obj V, (b.hom.app V).hom] y)
        (M.val.map_smul f r m)

/-- A sectionwise scalar pushout acts uniquely on the balanced tensor sheaf.

Source: Stacks Project, Tag 03EK; the balanced tensor calculation in step 6 of
`lem-pur-twist-sheaf-locally-free`.
(blueprint: lem-pur-tensor-pushout-action)

Proof: the two scalar actions define a ring map from the scalar tensor to the
endomorphism ring of the balanced module tensor. Transport along the given
scalar comparison and sheafify this module presheaf. The pure tensor formula
proves restriction compatibility. To prove uniqueness, lift a module section
locally before sheafification, expand both tensors into finite sums of pure
tensors, and use the two normalization formulas and the module laws.
-/
theorem tensorPushoutAction_existsUnique (e : ∀ U : Cᵒᵖ,
    letI := (b.hom.app U).hom.toAlgebra
    letI := (a.hom.app U).hom.toAlgebra
    B.obj.obj U ⊗[A.obj.obj U] R.obj.obj U ≃+* T.obj.obj U)
    (he : ∀ (U : Cᵒᵖ) (s : B.obj.obj U) (r : R.obj.obj U),
      letI := (b.hom.app U).hom.toAlgebra
      letI := (a.hom.app U).hom.toAlgebra
      e U (s ⊗ₜ[A.obj.obj U] r) = d.hom.app U s * c.hom.app U r) :
    let M' := (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj M
    let N := SheafOfModules.changeOfRingsOfUniverses b M'
    let P := SheafOfModules.changeOfRingsPresheafOfUniverses b M'
    let φ := (PresheafOfModules.toPresheaf _).map
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).unit.app P)
    ∃! K : ∀ U : Cᵒᵖ, Module (T.obj.obj U) (N.val.obj U),
      (∀ ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V) (z : T.obj.obj U) (x : N.val.obj U),
        N.val.map f (@SMul.smul _ _ (K U).toSMul z x) =
          @SMul.smul _ _ (K V).toSMul (T.obj.map f z) (N.val.map f x)) ∧
      (∀ (U : Cᵒᵖ) (s : B.obj.obj U) (x : N.val.obj U),
        @SMul.smul _ _ (K U).toSMul (d.hom.app U s) x = s • x) ∧
      ∀ (U : Cᵒᵖ) (r : R.obj.obj U) (s : B.obj.obj U) (x : M.val.obj U),
        @SMul.smul _ _ (K U).toSMul (c.hom.app U r)
          (φ.app U (s ⊗ₜ[A.obj.obj U, (b.hom.app U).hom] x)) =
        φ.app U (s ⊗ₜ[A.obj.obj U, (b.hom.app U).hom] (r • x)) := by
  let N := tensorSheaf a b M
  let P₀ := rawTensor a b M
  let : ∀ U : Cᵒᵖ,
      Module (((sheafCompose J (forget₂ CommRingCat RingCat)).obj T).obj.obj U)
        (P₀.presheaf.obj U) := fun U ↦ rawAction a b M e U
  let P : PresheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T).obj :=
    PresheafOfModules.ofPresheaf P₀.presheaf
      (fun {_ _} f z x ↦ rawAction_restriction a b c d M e he f z x)
  let F := (SheafOfModules.toSheaf _).obj N
  let φ : P.presheaf ⟶ F.obj := rawUnit a b M
  have : Presheaf.IsLocallyInjective J φ := by
    change Presheaf.IsLocallyInjective J (toSheafify J P₀.presheaf)
    infer_instance
  have : Presheaf.IsLocallySurjective J φ := by
    change Presheaf.IsLocallySurjective J (toSheafify J P₀.presheaf)
    infer_instance
  let K := PresheafOfModules.Sheafify.module (M₀ := P) (A := F) (𝟙 _) φ
  have hK (U : Cᵒᵖ) (z : T.obj.obj U) (x : P₀.obj U) :
      @SMul.smul _ _ (K U).toSMul z (φ.app U x) =
        φ.app U (@SMul.smul _ _ (rawAction a b M e U).toSMul z x) := by
    change PresheafOfModules.Sheafify.smul (M₀ := P) (𝟙 _) φ z
      (φ.app U x) = φ.app U (z • (show P.obj U from x))
    simpa using (PresheafOfModules.Sheafify.map_smul_eq (M₀ := P) (𝟙 _) φ z
      (φ.app U x) (𝟙 U) z (by simp) x (by simp))
  refine ⟨K, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro U V f z x
    exact PresheafOfModules.Sheafify.map_smul (M₀ := P) (𝟙 _) φ U f z x
  · intro U s x
    apply F.isSeparated _ _ (Presheaf.imageSieve_mem J φ x)
    rintro V f ⟨y, hy⟩
    have hd : d.hom.app (op V) (B.obj.map f.op s) = T.obj.map f.op (d.hom.app U s) :=
      ConcreteCategory.congr_hom (d.hom.naturality f.op) s
    have h₁ := PresheafOfModules.Sheafify.map_smul_eq (M₀ := P) (𝟙 _) φ
      (d.hom.app U s) x f.op (d.hom.app (op V) (B.obj.map f.op s)) hd y hy
    have h₂ := rawAction_left a b c d M e he (op V) (B.obj.map f.op s) y
    have h₃ := (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).unit.app P₀).app
        (op V)).hom.map_smul (B.obj.map f.op s) y
    refine h₁.trans ((congrArg (φ.app (op V)) h₂).trans (h₃.trans ?_))
    exact (congrArg (fun z : N.val.obj (op V) ↦ B.obj.map f.op s • z) hy).trans
      (N.val.map_smul f.op s x).symm
  · intro U r s x
    let := Module.compHom (M.val.obj U) (a.hom.app U).hom
    have hr := rawAction_tmul a b c d M e he U 1 s r x
    have hr' : @SMul.smul _ _ (rawAction a b M e U).toSMul (c.hom.app U r)
        (s ⊗ₜ[A.obj.obj U, (b.hom.app U).hom] x) =
        s ⊗ₜ[A.obj.obj U, (b.hom.app U).hom] (r • x) := by
      simpa only [map_one, one_mul] using hr
    exact (hK U (c.hom.app U r) _).trans (congrArg (φ.app U) hr')
  · intro K' hK'
    have hp (U : Cᵒᵖ) (z : T.obj.obj U) (y : P₀.obj U) :
        @SMul.smul _ _ (K' U).toSMul z (φ.app U y) =
          φ.app U (@SMul.smul _ _ (rawAction a b M e U).toSMul z y) := by
      let := (b.hom.app U).hom.toAlgebra
      let := (a.hom.app U).hom.toAlgebra
      let := Module.compHom (M.val.obj U) (a.hom.app U).hom
      let : Module (B.obj.obj U) (F.obj.obj U) := (N.val.obj U).isModule
      let : Module (T.obj.obj U) (F.obj.obj U) := K' U
      let : Module (T.obj.obj U) (P₀.obj U) := rawAction a b M e U
      change z • φ.app U y = φ.app U (z • y)
      dsimp only [sheafCompose] at *
      obtain ⟨w, rfl⟩ := (e U).surjective z
      induction w using TensorProduct.inductionOn with
      | add w w' hw hw' => simp only [map_add, add_smul, hw, hw']
      | tmul s r =>
        rw [he U]
        induction y using TensorProduct.inductionOn with
        | add y y' hy hy' => simp only [map_add, smul_add, hy, hy']
        | tmul t x =>
          change B.obj.obj U at t
          change M.val.obj U at x
          have hc := hK'.2.2 U r t x
          change c.hom.app U r •
            φ.app U (t ⊗ₜ[A.obj.obj U, (b.hom.app U).hom] x) =
              φ.app U (t ⊗ₜ[A.obj.obj U, (b.hom.app U).hom] (r • x)) at hc
          have hd := hK'.2.1 U s
            (φ.app U (t ⊗ₜ[A.obj.obj U, (b.hom.app U).hom] (r • x)))
          have hunit := (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).unit.app
              P₀).app U).hom.map_smul s
                (t ⊗ₜ[A.obj.obj U, (b.hom.app U).hom] (r • x))
          have htmul := ModuleCat.ExtendScalars.smul_tmul (b.hom.app U).hom s t
            (show (restricted a M).val.obj U from r • x)
          have hraw := rawAction_tmul a b c d M e he U s t r x
          refine (mul_smul (d.hom.app U s) (c.hom.app U r)
            (φ.app U (t ⊗ₜ[A.obj.obj U, (b.hom.app U).hom] x))).trans ?_
          refine (congrArg (fun y : F.obj.obj U ↦ d.hom.app U s • y) hc).trans ?_
          exact hd.trans ((hunit.symm.trans (congrArg (φ.app U) htmul)).trans
            (congrArg (φ.app U) hraw).symm)
    funext U
    apply Module.ext'
    intro z x
    let q : PresheafOfModules.Sheafify.SMulCandidate (M₀ := P) (𝟙 _) φ z x :=
      { x := @SMul.smul _ _ (K' U).toSMul z x
        h := by
          intro V f z₀ hz y hy
          change z₀ = T.obj.map f z at hz
          change φ.app V y = F.obj.map f x at hy
          exact (hK'.1 f z x).trans
            ((congrArg₂ (fun a b ↦ @SMul.smul _ _ (K' V).toSMul a b)
              hz.symm hy.symm).trans (hp V z₀ y)) }
    exact congrArg (fun t ↦ t.x)
      (Subsingleton.elim q (PresheafOfModules.Sheafify.smulCandidate (M₀ := P)
        (𝟙 _) φ z x))

end Sheaf
end CategoryTheory

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryInverseSystem
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryDirectSystemMate

/-! # Direct image and transposition on strict systems

## References

* Zheng Construction 4.1
* Stacks 03D2 and 03DA
* Zheng Construction 4.1, paragraph before Lemma 4.10
* Zheng Construction 4.1 and Stacks 03D7
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (F : ℕ → Sheaf J' CommRingCat.{max c v r}) (σ : ∀ n, F (n + 1) ⟶ F n)
  (I : ∀ n, SheafOfModules.AlgebraicInverseImage uInv (B n) (F n))

private theorem system_transition_apply {m n : ℕ} (h : n ≤ m)
    (M : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ)
    (x : M.val.obj (op (m, U.unop))) :
    ((transition.{c, v, max c v r} J B τ h).app M).val.app U x =
      M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x := by
  exact congrFun (eq_of_heq
    ((transition_exists.{c, v, max c v r} J B τ h).exists.choose_spec M U)) x

private theorem system_hom_ext {M N : Systems.{c, v, max c v r} J B τ}
    {f g : M ⟶ N}
    (h : ∀ n, (evaluation.{c, v, max c v r} J B τ n).map f =
      (evaluation.{c, v, max c v r} J B τ n).map g) : f = g := by
  ext X x
  exact congrArg (fun q ↦ q.val.app (op X.unop.2) x) (h X.unop.1)

private theorem system_evaluation_smul (M : Systems.{c, v, max c v r} J B τ)
    (n : ℕ) (U : Cᵒᵖ) (b : (B n).obj.obj U)
    (x : M.val.obj (op (n, U.unop))) :
    @SMul.smul _ _ (((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U).isModule.toSMul
      b x = @SMul.smul _ _ (M.val.obj (op (n, U.unop))).isModule.toSMul b x := by
  change @SMul.smul _ _ (M.val.obj (op (n, U.unop))).isModule.toSMul
    (((eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom.app U) b) x = _
  rw [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

attribute [local irreducible] transition coefficientMap systemRing ringPresheaf rings

private theorem systemHom_naturality {M N : Systems.{c, v, max c v r} J B τ}
    (f : ∀ n, (evaluation.{c, v, max c v r} J B τ n).obj M ⟶
      (evaluation.{c, v, max c v r} J B τ n).obj N)
    (hf : ∀ {m n : ℕ} (h : n ≤ m),
      f m ≫ (transition.{c, v, max c v r} J B τ h).app N =
        (transition.{c, v, max c v r} J B τ h).app M ≫
          (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)).map (f n))
    {X Y : (ℕ × C)ᵒᵖ} (k : X ⟶ Y) (x : M.val.obj X) :
    (f Y.unop.1).val.app (op Y.unop.2) (M.val.map k x) =
      N.val.map k ((f X.unop.1).val.app (op X.unop.2) x) := by
  let h : Y.unop.1 ≤ X.unop.1 := leOfHom k.unop.1
  let i : (X.unop.1, Y.unop.2) ⟶ X.unop :=
    Prod.mkHom (𝟙 _) k.unop.2
  let j : Y.unop ⟶ (X.unop.1, Y.unop.2) :=
    Prod.mkHom (homOfLE h) (𝟙 _)
  have hk : k = i.op ≫ j.op := by
    apply Quiver.Hom.unop_inj
    apply Prod.hom_ext
    · exact Subsingleton.elim _ _
    · simp [i, j]
  have hm := (M.val.congr_map_apply hk x).trans (M.val.map_comp_apply i.op j.op x)
  have hn := (N.val.congr_map_apply hk ((f X.unop.1).val.app (op X.unop.2) x)).trans
    (N.val.map_comp_apply i.op j.op ((f X.unop.1).val.app (op X.unop.2) x))
  have hv := PresheafOfModules.naturality_apply (f X.unop.1).val k.unop.2.op x
  have hh := congrArg (fun q ↦ q.val.app (op Y.unop.2) (M.val.map i.op x)) (hf h)
  change (f X.unop.1).val.app (op Y.unop.2) (M.val.map i.op x) =
    N.val.map i.op ((f X.unop.1).val.app (op X.unop.2) x) at hv
  change ((transition.{c, v, max c v r} J B τ h).app N).val.app (op Y.unop.2)
      ((f X.unop.1).val.app (op Y.unop.2) (M.val.map i.op x)) =
    (f Y.unop.1).val.app (op Y.unop.2)
      (((transition.{c, v, max c v r} J B τ h).app M).val.app (op Y.unop.2)
        (M.val.map i.op x)) at hh
  have hh' : N.val.map j.op ((f X.unop.1).val.app (op Y.unop.2) (M.val.map i.op x)) =
      (f Y.unop.1).val.app (op Y.unop.2) (M.val.map j.op (M.val.map i.op x)) :=
    (system_transition_apply.{c, v, r} J B τ h N (op Y.unop.2) _).symm.trans
      (hh.trans (congrArg ((f Y.unop.1).val.app (op Y.unop.2))
        (system_transition_apply.{c, v, r} J B τ h M (op Y.unop.2) _)))
  exact (congrArg ((f Y.unop.1).val.app (op Y.unop.2)) hm).trans
    (hh'.symm.trans ((congrArg (N.val.map j.op) hv).trans hn.symm))

section ComponentMap
attribute [local semireducible] systemRing ringPresheaf rings

@[irreducible] private def systemHomApp {M N : Systems.{c, v, max c v r} J B τ}
    (f : ∀ n, (evaluation.{c, v, max c v r} J B τ n).obj M ⟶
      (evaluation.{c, v, max c v r} J B τ n).obj N) (X : (ℕ × C)ᵒᵖ) : M.val.obj X ⟶ N.val.obj X :=
  ModuleCat.ofHom {
    toFun := (f X.unop.1).val.app (op X.unop.2)
    map_add' := map_add _
    map_smul' := fun b x ↦ by
      have hh := ((f X.unop.1).val.app (op X.unop.2)).hom.map_smul b x
      have hm := system_evaluation_smul.{c, v, r} J B τ M X.unop.1 (op X.unop.2) b x
      have hn := system_evaluation_smul.{c, v, r} J B τ N X.unop.1 (op X.unop.2) b
        ((f X.unop.1).val.app (op X.unop.2) x)
      exact (congrArg ((f X.unop.1).val.app (op X.unop.2)) hm.symm).trans (hh.trans hn) }

private theorem systemHomApp_apply {M N : Systems.{c, v, max c v r} J B τ}
    (f : ∀ n, (evaluation.{c, v, max c v r} J B τ n).obj M ⟶
      (evaluation.{c, v, max c v r} J B τ n).obj N) (X : (ℕ × C)ᵒᵖ) (x : M.val.obj X) :
    systemHomApp.{c, v, r} J B τ f X x = (f X.unop.1).val.app (op X.unop.2) x := by
  unfold systemHomApp
  rfl

end ComponentMap

@[irreducible] private def systemHomMk {M N : Systems.{c, v, max c v r} J B τ}
    (f : ∀ n, (evaluation.{c, v, max c v r} J B τ n).obj M ⟶
      (evaluation.{c, v, max c v r} J B τ n).obj N)
    (hf : ∀ {m n : ℕ} (h : n ≤ m),
      f m ≫ (transition.{c, v, max c v r} J B τ h).app N =
        (transition.{c, v, max c v r} J B τ h).app M ≫
          (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)).map (f n)) : M ⟶ N :=
  ⟨{
    app := systemHomApp.{c, v, r} J B τ f
    naturality := fun {X Y} k ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change systemHomApp.{c, v, r} J B τ f Y (M.val.map k x) =
        N.val.map k (systemHomApp.{c, v, r} J B τ f X x)
      simp only [systemHomApp_apply]
      exact systemHom_naturality.{c, v, r} J B τ f hf k x }⟩

private theorem system_evaluation_map_apply {M N : Systems.{c, v, max c v r} J B τ}
    (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U) :
    ((evaluation.{c, v, max c v r} J B τ n).map f).val.app U x =
      f.val.app (op (n, U.unop)) x := rfl

private theorem systemHomMk_apply {M N : Systems.{c, v, max c v r} J B τ}
    (f : ∀ n, (evaluation.{c, v, max c v r} J B τ n).obj M ⟶
      (evaluation.{c, v, max c v r} J B τ n).obj N)
    (hf : ∀ {m n : ℕ} (h : n ≤ m),
      f m ≫ (transition.{c, v, max c v r} J B τ h).app N =
        (transition.{c, v, max c v r} J B τ h).app M ≫
          (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)).map (f n))
    (X : (ℕ × C)ᵒᵖ) (x : M.val.obj X) :
    (systemHomMk.{c, v, r} J B τ f hf).val.app X x =
      systemHomApp.{c, v, r} J B τ f X x := by
  unfold systemHomMk
  rfl

private theorem systemHomMk_evaluation {M N : Systems.{c, v, max c v r} J B τ}
    (f : ∀ n, (evaluation.{c, v, max c v r} J B τ n).obj M ⟶
      (evaluation.{c, v, max c v r} J B τ n).obj N)
    (hf : ∀ {m n : ℕ} (h : n ≤ m),
      f m ≫ (transition.{c, v, max c v r} J B τ h).app N =
        (transition.{c, v, max c v r} J B τ h).app M ≫
          (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)).map (f n))
    (n : ℕ) :
    (evaluation.{c, v, max c v r} J B τ n).map (systemHomMk.{c, v, r} J B τ f hf) = f n := by
  apply (underlying.{c, v, r} J (B n)).map_injective
  ext U x
  exact (system_evaluation_map_apply.{c, v, r} J B τ _ n U x).trans
    ((systemHomMk_apply.{c, v, r} J B τ f hf (op (n, U.unop)) x).trans
      (systemHomApp_apply.{c, v, r} J B τ f (op (n, U.unop)) x))

attribute [local irreducible] evaluation
attribute [local semireducible] coefficientMap systemRing ringPresheaf rings

variable (P : OrdinaryInverseSystem.{c, v, r} J B τ J' uInv F σ I)
  (V : ∀ n, Mod.{c, v, max c v r} J' (F n) ⥤ Mod.{c, v, max c v r} J (B n))
  (a : ∀ n, (I n).modules ⊣ V n)

/-- The componentwise direct image and the restricted levelwise Hom bijection. -/
structure OrdinaryDirectSystem where
  push : Systems.{c, v, max c v r} J' F σ ⥤ Systems.{c, v, max c v r} J B τ
  component : ∀ n,
    push ⋙ evaluation.{c, v, max c v r} J B τ n ≅
      evaluation.{c, v, max c v r} J' F σ n ⋙ V n
  component_sections : ∀ n (M : Systems.{c, v, max c v r} J' F σ) (U : Cᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj (push.obj M)).val.obj U),
    HEq ((((component n).hom.app M).val.app U) x) x
  homEquiv : ∀ (M : Systems.{c, v, max c v r} J B τ)
    (N : Systems.{c, v, max c v r} J' F σ), (P.pull.obj M ⟶ N) ≃ (M ⟶ push.obj N)
  homEquiv_component : ∀ (M : Systems.{c, v, max c v r} J B τ)
    (N : Systems.{c, v, max c v r} J' F σ) (f : P.pull.obj M ⟶ N) (n : ℕ),
    (evaluation.{c, v, max c v r} J B τ n).map (homEquiv M N f) ≫
        (component n).hom.app N =
      (a n).homEquiv _ _ ((P.component n).inv.app M ≫
        (evaluation.{c, v, max c v r} J' F σ n).map f)

/-- The functor and component identifications used by an ordinary direct system.
The local mate condition specifies the horizontal maps: each two-component square
commutes exactly when its transpose commutes. It does not assert a global Hom
bijection or assembly of morphisms. -/
structure OrdinaryDirectSystemCore where
  push : Systems.{c, v, max c v r} J' F σ ⥤ Systems.{c, v, max c v r} J B τ
  component : ∀ n,
    push ⋙ evaluation.{c, v, max c v r} J B τ n ≅
      evaluation.{c, v, max c v r} J' F σ n ⋙ V n
  component_sections : ∀ n (M : Systems.{c, v, max c v r} J' F σ) (U : Cᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj (push.obj M)).val.obj U),
    HEq ((((component n).hom.app M).val.app U) x) x

  transition_mate : ∀ (M : Systems.{c, v, max c v r} J B τ)
    (N : Systems.{c, v, max c v r} J' F σ) {m n : ℕ} (h : n ≤ m)
    (fm : (evaluation.{c, v, max c v r} J' F σ m).obj (P.pull.obj M) ⟶
      (evaluation.{c, v, max c v r} J' F σ m).obj N)
    (fn : (evaluation.{c, v, max c v r} J' F σ n).obj (P.pull.obj M) ⟶
      (evaluation.{c, v, max c v r} J' F σ n).obj N),
    let gm := (a m).homEquiv _ _ ((P.component m).inv.app M ≫ fm) ≫
      (component m).inv.app N
    let gn := (a n).homEquiv _ _ ((P.component n).inv.app M ≫ fn) ≫
      (component n).inv.app N
    (fm ≫ (transition.{c, v, max c v r} J' F σ h).app N =
      (transition.{c, v, max c v r} J' F σ h).app (P.pull.obj M) ≫
        (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J' F σ h)).map fn) ↔
      (gm ≫ (transition.{c, v, max c v r} J B τ h).app (push.obj N) =
        (transition.{c, v, max c v r} J B τ h).app M ≫
          (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)).map gn)

/-- The restricted levelwise Hom data for a fixed direct-system core. -/
structure OrdinaryDirectSystemHomData
    (K : OrdinaryDirectSystemCore.{c, v, r} J B τ J' uInv F σ I P V a) where
  homEquiv : ∀ (M : Systems.{c, v, max c v r} J B τ)
    (N : Systems.{c, v, max c v r} J' F σ), (P.pull.obj M ⟶ N) ≃ (M ⟶ K.push.obj N)
  homEquiv_component : ∀ (M : Systems.{c, v, max c v r} J B τ)
    (N : Systems.{c, v, max c v r} J' F σ) (f : P.pull.obj M ⟶ N) (n : ℕ),
    (evaluation.{c, v, max c v r} J B τ n).map (homEquiv M N f) ≫
        (K.component n).hom.app N =
      (a n).homEquiv _ _ ((P.component n).inv.app M ≫
        (evaluation.{c, v, max c v r} J' F σ n).map f)

/-- The componentwise reassembly of the direct image. -/
theorem ordinaryDirectSystem_core_exists [PreservesFiniteLimits uInv]
    (hI : ∀ n,
      uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).map (τ n)) ≫
          (I n).ringUnderlying.hom =
        (I (n + 1)).ringUnderlying.hom ≫
          (sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r})).map (σ n))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush)
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush)
    (ha : ∀ n (M : Mod.{c, v, max c v r} J (B n))
      (N : Mod.{c, v, max c v r} J' (F n)) (f : (I n).modules.obj M ⟶ N),
      (underlying.{c, v, r} J (B n)).map ((a n).homEquiv M N f) ≫ (eV n).hom.app N =
        adjSet.homEquiv _ _ ((I n).moduleUnderlying.inv.app M ≫
          (underlying.{c, v, r} J' (F n)).map f)) :
    Nonempty (OrdinaryDirectSystemCore.{c, v, r} J B τ J' uInv F σ I P V a) := by
  obtain ⟨D, hD⟩ := ordinaryDirectSystem_core_data_exists.{c, v, r} J B τ J' uInv F σ I V a
    hI uPush adjSet eV ha
  refine ⟨{
    push := D.push
    component := D.component
    component_sections := D.component_sections
    transition_mate := ?_ }⟩
  exact ordinaryDirectSystem_core_transition_mate_exists.{c, v, r} J B τ J' uInv F σ I P V a
    hI uPush adjSet eV ha (D := D) hD

private def systemLevelHomEquiv
    (K : OrdinaryDirectSystemCore.{c, v, r} J B τ J' uInv F σ I P V a)
    (M : Systems.{c, v, max c v r} J B τ)
    (N : Systems.{c, v, max c v r} J' F σ) (n : ℕ) :
    ((evaluation.{c, v, max c v r} J' F σ n).obj (P.pull.obj M) ⟶
      (evaluation.{c, v, max c v r} J' F σ n).obj N) ≃
    ((evaluation.{c, v, max c v r} J B τ n).obj M ⟶
      (evaluation.{c, v, max c v r} J B τ n).obj (K.push.obj N)) where
  toFun f := (a n).homEquiv _ _ ((P.component n).inv.app M ≫ f) ≫
    (K.component n).inv.app N
  invFun g := (P.component n).hom.app M ≫
    ((a n).homEquiv _ _).symm (g ≫ (K.component n).hom.app N)
  left_inv f := by simp [Category.assoc]
  right_inv g := by simp [Category.assoc]

/-- The component Hom bijection for an assembled ordinary direct image. -/
theorem ordinaryDirectSystem_homData_exists
    (K : OrdinaryDirectSystemCore.{c, v, r} J B τ J' uInv F σ I P V a) :
    Nonempty (OrdinaryDirectSystemHomData.{c, v, r} J B τ J' uInv F σ I P V a K) := by
  let t := systemLevelHomEquiv.{c, v, r} J B τ J' uInv F σ I P V a K
  have hforward (M : Systems.{c, v, max c v r} J B τ)
      (N : Systems.{c, v, max c v r} J' F σ) (f : P.pull.obj M ⟶ N)
      {m n : ℕ} (h : n ≤ m) :
      t M N m ((evaluation.{c, v, max c v r} J' F σ m).map f) ≫
          (transition.{c, v, max c v r} J B τ h).app (K.push.obj N) =
        (transition.{c, v, max c v r} J B τ h).app M ≫
          (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)).map
            (t M N n ((evaluation.{c, v, max c v r} J' F σ n).map f)) :=
    (K.transition_mate M N h _ _).mp ((transition.{c, v, max c v r} J' F σ h).naturality f)
  have hbackward (M : Systems.{c, v, max c v r} J B τ)
      (N : Systems.{c, v, max c v r} J' F σ) (g : M ⟶ K.push.obj N)
      {m n : ℕ} (h : n ≤ m) :
      (t M N m).symm ((evaluation.{c, v, max c v r} J B τ m).map g) ≫
          (transition.{c, v, max c v r} J' F σ h).app N =
        (transition.{c, v, max c v r} J' F σ h).app (P.pull.obj M) ≫
          (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J' F σ h)).map
            ((t M N n).symm ((evaluation.{c, v, max c v r} J B τ n).map g)) := by
    apply (K.transition_mate M N h _ _).mpr
    change t M N m ((t M N m).symm _) ≫ _ =
      _ ≫ (res.{c, v, max c v r} _).map (t M N n ((t M N n).symm _))
    simp only [Equiv.apply_symm_apply]
    exact (transition.{c, v, max c v r} J B τ h).naturality g
  let e (M : Systems.{c, v, max c v r} J B τ)
      (N : Systems.{c, v, max c v r} J' F σ) : (P.pull.obj M ⟶ N) ≃ (M ⟶ K.push.obj N) :=
    { toFun := fun f ↦ systemHomMk.{c, v, r} J B τ
        (fun n ↦ t M N n ((evaluation.{c, v, max c v r} J' F σ n).map f))
        (hforward M N f)
      invFun := fun g ↦ systemHomMk.{c, v, r} J' F σ
        (fun n ↦ (t M N n).symm ((evaluation.{c, v, max c v r} J B τ n).map g))
        (hbackward M N g)
      left_inv := fun f ↦ by
        apply system_hom_ext.{c, v, r} J' F σ
        intro n
        rw [systemHomMk_evaluation.{c, v, r}, systemHomMk_evaluation.{c, v, r},
          Equiv.symm_apply_apply]
      right_inv := fun g ↦ by
        apply system_hom_ext.{c, v, r} J B τ
        intro n
        rw [systemHomMk_evaluation.{c, v, r}, systemHomMk_evaluation.{c, v, r},
          Equiv.apply_symm_apply] }
  refine ⟨{ homEquiv := e, homEquiv_component := ?_ }⟩
  intro M N f n
  change (evaluation.{c, v, max c v r} J B τ n).map (systemHomMk.{c, v, r} J B τ
    (fun k ↦ t M N k ((evaluation.{c, v, max c v r} J' F σ k).map f))
    (hforward M N f)) ≫ _ = _
  rw [systemHomMk_evaluation]
  change ((a n).homEquiv _ _ (_ ≫ _) ≫ (K.component n).inv.app N) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- Assemble right adjoints on systems from the compatible inverse-image transitions.
This asserts the system construction and its Hom bijection; its naturality, adjunction,
additivity and unit equations are proved by the caller. -/
theorem ordinaryDirectSystem_exists [PreservesFiniteLimits uInv]
    (hI : ∀ n,
      uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).map (τ n)) ≫
          (I n).ringUnderlying.hom =
        (I (n + 1)).ringUnderlying.hom ≫
          (sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r})).map (σ n))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush)
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush)
    (ha : ∀ n (M : Mod.{c, v, max c v r} J (B n))
      (N : Mod.{c, v, max c v r} J' (F n)) (f : (I n).modules.obj M ⟶ N),
      (underlying.{c, v, r} J (B n)).map ((a n).homEquiv M N f) ≫ (eV n).hom.app N =
        adjSet.homEquiv _ _ ((I n).moduleUnderlying.inv.app M ≫
          (underlying.{c, v, r} J' (F n)).map f)) :
    Nonempty (OrdinaryDirectSystem.{c, v, r} J B τ J' uInv F σ I P V a) := by
  obtain ⟨K⟩ := ordinaryDirectSystem_core_exists.{c, v, r} J B τ J' uInv F σ I P V a
    hI uPush adjSet eV ha
  obtain ⟨H⟩ := ordinaryDirectSystem_homData_exists.{c, v, r} J B τ J' uInv F σ I P V a K
  exact ⟨{
    push := K.push
    component := K.component
    component_sections := K.component_sections
    homEquiv := H.homEquiv
    homEquiv_component := H.homEquiv_component }⟩

end WeilConjectures.SemilinearSections

end

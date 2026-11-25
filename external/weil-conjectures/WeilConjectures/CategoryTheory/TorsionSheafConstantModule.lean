/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Module.ZMod

/-! # The canonical constant Z/N module structure of a torsion sheaf

Source: Stacks Project, Lemma 18.11.1, Tag 03CY
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe w vC uC

open CategoryTheory

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J RingCat.{max vC uC}]

/-- The constant sheaf of rings with value `Z/N`, lifted to the coefficient universe.
Source: Stacks Project, Tag 03CY (auxiliary; not a blueprint node). -/
noncomputable abbrev constantZModRingSheaf (N : ℕ) : Sheaf J RingCat.{max vC uC} :=
  (constantSheaf J RingCat.{max vC uC}).obj (RingCat.of (ULift.{max vC uC} (ZMod N)))

/-- A module structure on the fixed underlying groups, normalized on constant sections,
with semilinear restrictions. The normalization uses every integer representative.
Source: Stacks Project, Tag 03CY (auxiliary; not a blueprint node). -/
def IsConstantZModSheafModuleStructure (N : ℕ) (F : Sheaf J AddCommGrpCat.{w})
    (M : ∀ U : Cᵒᵖ, Module ((constantZModRingSheaf J N).obj.obj U) (F.obj.obj U)) : Prop :=
  (∀ (U : Cᵒᵖ) (z : ℤ) (x : F.obj.obj U),
    @SMul.smul _ _ (M U).toSMul
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{max vC uC} (ZMod N))))).app U
        (ULift.up (z : ZMod N))) x = z • x) ∧
  ∀ ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V) (a : (constantZModRingSheaf J N).obj.obj U)
      (x : F.obj.obj U),
    F.obj.map f (@SMul.smul _ _ (M U).toSMul a x) =
      @SMul.smul _ _ (M V).toSMul ((constantZModRingSheaf J N).obj.map f a) (F.obj.map f x)

set_option backward.isDefEq.respectTransparency false in
/-- A sheaf killed by `N` has exactly one normalized constant `Z/N` module structure.
Source: Stacks Project, Tag 03CY (auxiliary; not a blueprint node).
Proof: the annihilation hypothesis makes each group a `ZMod N`-module, with integer
representatives acting by integer multiples. Additive restriction maps are linear over this
constant presheaf. Lemma 03CY uniquely extends this action to the sheafification of that
presheaf of rings; the abelian sheaf is already a sheaf, so its sheafification is itself.
The resulting action commutes with restrictions. The uniqueness part of 03CY proves
uniqueness of the family of module structures. -/
theorem existsUnique_constantZModSheafModuleStructure (N : ℕ) (hN : 0 < N)
    (F : Sheaf J AddCommGrpCat.{w}) (hF : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), N • x = 0) :
    ∃! M : ∀ U : Cᵒᵖ, Module ((constantZModRingSheaf J N).obj.obj U) (F.obj.obj U),
      IsConstantZModSheafModuleStructure J N F M := by
  have _hN := hN
  let α := toSheafify J
    ((Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{max vC uC} (ZMod N))))
  have : Limits.PreservesFilteredColimitsOfSize.{max vC uC, max vC uC}
      (forget RingCat.{max vC uC}) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{max vC uC, max vC uC,
      max vC uC, max vC uC} _
  have hi : Presheaf.IsLocallyInjective J α := by dsimp [α]; infer_instance
  have hs : Presheaf.IsLocallySurjective J α := by dsimp [α]; infer_instance
  let : ∀ U : Cᵒᵖ, Module (ZMod N) (F.obj.obj U) :=
    fun U ↦ AddCommGroup.zmodModule (hF U)
  let R₀ := (Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{max vC uC} (ZMod N)))
  let : ∀ U : Cᵒᵖ, Module (R₀.obj U) (F.obj.obj U) :=
    fun _ ↦ ULift.module
  let P : PresheafOfModules R₀ :=
    PresheafOfModules.ofPresheaf F.obj (fun {_ _} f r x ↦
      ZMod.map_smul (F.obj.map f).hom r.down x)
  let φ : P.presheaf ⟶ F.obj := 𝟙 F.obj
  have : Presheaf.IsLocallyInjective J φ := by
    apply Presheaf.isLocallyInjective_of_injective
    intro U
    exact Function.injective_id
  have : Presheaf.IsLocallySurjective J φ := by
    apply Presheaf.isLocallySurjective_of_surjective
    intro U
    exact Function.surjective_id
  let M := PresheafOfModules.Sheafify.module (M₀ := P) (A := F) α φ
  have hM : IsConstantZModSheafModuleStructure J N F M := by
    constructor
    · intro U z x
      change PresheafOfModules.Sheafify.smul α φ (α.app U (ULift.up (z : ZMod N))) x = _
      have h := PresheafOfModules.Sheafify.map_smul_eq α φ
        (α.app U (ULift.up (z : ZMod N))) x (𝟙 U)
        (ULift.up (z : ZMod N)) (by simp) x (by
          change x = F.obj.map (𝟙 U) x
          rw [Functor.map_id]
          rfl)
      rw [Functor.map_id] at h
      change PresheafOfModules.Sheafify.smul α φ _ x = (z : ZMod N) • x at h
      exact h.trans (Int.cast_smul_eq_zsmul (ZMod N) z x)
    · intro U V f a x
      exact PresheafOfModules.Sheafify.map_smul α φ U f a x
  refine ⟨M, hM, ?_⟩
  intro M' hM'
  funext U
  apply Module.ext'
  intro a x
  let c : PresheafOfModules.Sheafify.SMulCandidate α φ a x :=
    { x := @SMul.smul _ _ (M' U).toSMul a x
      h := by
        intro V f r hr y hy
        let y' : F.obj.obj V := y
        change y' = F.obj.map f x at hy
        change (α.app V) r = (constantZModRingSheaf J N).obj.map f a at hr
        change F.obj.map f (@SMul.smul _ _ (M' U).toSMul a x) = r.down • y'
        rw [hM'.2 f, ← hr, ← hy]
        obtain ⟨r⟩ := r
        obtain ⟨z, rfl⟩ := ZMod.intCast_surjective r
        exact (hM'.1 V z y').trans (Int.cast_smul_eq_zsmul (ZMod N) z y').symm }
  exact congrArg (fun t ↦ t.x)
    (Subsingleton.elim c (PresheafOfModules.Sheafify.smulCandidate α φ a x))

/-- The unique normalized scalar action; choice is from an existence-and-uniqueness theorem.
Source: Stacks Project, Tag 03CY (auxiliary; not a blueprint node). -/
@[instance_reducible]
noncomputable def torsionSheafModuleStructure (N : ℕ) (hN : 0 < N)
    (F : Sheaf J AddCommGrpCat.{w}) (hF : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), N • x = 0) :
    ∀ U : Cᵒᵖ, Module ((constantZModRingSheaf J N).obj.obj U) (F.obj.obj U) :=
  (existsUnique_constantZModSheafModuleStructure J N hN F hF).exists.choose

/-- The chosen unique action satisfies normalization and semilinearity.
Source: Stacks Project, Tag 03CY (auxiliary; not a blueprint node).
Proof: apply the specification of the unique witness in
`existsUnique_constantZModSheafModuleStructure`, which constructs the action by 03CY. -/
theorem torsionSheafModuleStructure_spec (N : ℕ) (hN : 0 < N)
    (F : Sheaf J AddCommGrpCat.{w}) (hF : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), N • x = 0) :
    IsConstantZModSheafModuleStructure J N F (torsionSheafModuleStructure J N hN F hF) := by
  exact (existsUnique_constantZModSheafModuleStructure J N hN F hF).exists.choose_spec

/-- The corresponding module sheaf has exactly the original underlying abelian presheaf.
Source: Stacks Project, Tag 03CY (auxiliary; not a blueprint node). -/
noncomputable def torsionSheafModule (N : ℕ) (hN : 0 < N)
    (F : Sheaf J AddCommGrpCat.{w}) (hF : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), N • x = 0) :
    ringedSiteModules (constantZModRingSheaf J N) :=
  letI := torsionSheafModuleStructure J N hN F hF
  ⟨PresheafOfModules.ofPresheaf F.obj (torsionSheafModuleStructure_spec J N hN F hF).2,
    F.property⟩

/-- Conversely, every module sheaf over the constant `Z/N` ring is killed by `N`.
Source: Stacks Project, Tag 03CY (auxiliary; not a blueprint node).
Proof: the image of the integer `N` in the constant presheaf `ZMod N` is zero.
The sheafified image is still zero. Its action is multiplication by `N`, so the
module axioms give `N • x = 0` on every section. -/
theorem constantZModModuleSheaf_nsmul (N : ℕ) (hN : 0 < N)
    (F : ringedSiteModules (constantZModRingSheaf J N))
    (U : Cᵒᵖ) (x : F.val.obj U) : N • x = 0 := by
  have _hN := hN
  let α := toSheafify J
    ((Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{max vC uC} (ZMod N))))
  have hz : (N : ULift.{max vC uC} (ZMod N)) = 0 := by
    apply ULift.ext
    exact ZMod.natCast_self N
  have he : (N : (constantZModRingSheaf J N).obj.obj U) = 0 := by
    calc
      (N : (constantZModRingSheaf J N).obj.obj U) =
          (α.app U).hom (N : ULift.{max vC uC} (ZMod N)) := (map_natCast _ _).symm
      _ = 0 := by rw [hz, map_zero]
  rw [← Nat.cast_smul_eq_nsmul ((constantZModRingSheaf J N).obj.obj U), he, zero_smul]

set_option backward.isDefEq.respectTransparency false in
/-- Conjugation by an additive sheaf automorphism preserves normalization and restriction
compatibility. Uniqueness of the normalized action therefore makes the automorphism linear.
Source: Stacks Project, Tag 03CY, uniqueness of the compatible action
(auxiliary; not a blueprint node). -/
private theorem normalized_automorphism_linear (N : ℕ) (hN : 0 < N)
    (F : Sheaf J AddCommGrpCat.{w}) (hF : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), N • x = 0)
    (M : ∀ U : Cᵒᵖ, Module ((constantZModRingSheaf J N).obj.obj U) (F.obj.obj U))
    (hM : IsConstantZModSheafModuleStructure J N F M) (e : F ≅ F) :
    ∀ (U : Cᵒᵖ) (a : (constantZModRingSheaf J N).obj.obj U) (x : F.obj.obj U),
      e.hom.hom.app U (@SMul.smul _ _ (M U).toSMul a x) =
        @SMul.smul _ _ (M U).toSMul a (e.hom.hom.app U x) := by
  let eU (U : Cᵒᵖ) : F.obj.obj U ≃+ F.obj.obj U :=
    { toFun := e.hom.hom.app U
      invFun := e.inv.hom.app U
      left_inv := fun x ↦ by
        have h := congrArg (fun f : F ⟶ F ↦ f.hom.app U x) e.hom_inv_id
        exact h
      right_inv := fun x ↦ by
        have h := congrArg (fun f : F ⟶ F ↦ f.hom.app U x) e.inv_hom_id
        exact h
      map_add' := (e.hom.hom.app U).hom.map_add }
  let (U : Cᵒᵖ) : Module ((constantZModRingSheaf J N).obj.obj U) (F.obj.obj U) := M U
  let M' (U : Cᵒᵖ) : Module ((constantZModRingSheaf J N).obj.obj U) (F.obj.obj U) :=
    (eU U).module ((constantZModRingSheaf J N).obj.obj U)
  have hM' : IsConstantZModSheafModuleStructure J N F M' := by
    constructor
    · intro U z x
      change (eU U).symm (@SMul.smul _ _ (M U).toSMul _ (eU U x)) = z • x
      exact (congrArg (eU U).symm (hM.1 U z (eU U x))).trans (by
        simp only [map_zsmul, AddEquiv.symm_apply_apply])
    · intro U V f a x
      change F.obj.map f ((eU U).symm (@SMul.smul _ _ (M U).toSMul a (eU U x))) =
        (eU V).symm (@SMul.smul _ _ (M V).toSMul
          ((constantZModRingSheaf J N).obj.map f a) (eU V (F.obj.map f x)))
      change F.obj.map f (e.inv.hom.app U
          (@SMul.smul _ _ (M U).toSMul a (e.hom.hom.app U x))) =
        e.inv.hom.app V (@SMul.smul _ _ (M V).toSMul
          ((constantZModRingSheaf J N).obj.map f a) (e.hom.hom.app V (F.obj.map f x)))
      rw [← NatTrans.naturality_apply e.inv.hom f, hM.2 f,
        NatTrans.naturality_apply e.hom.hom f]
  have heq : M' = M :=
    (existsUnique_constantZModSheafModuleStructure J N hN F hF).unique hM' hM
  intro U a x
  have hs : @SMul.smul _ _ (M' U).toSMul a x =
      @SMul.smul _ _ (M U).toSMul a x := by rw [heq]
  have hh := congrArg (eU U) hs
  change eU U ((eU U).symm (@SMul.smul _ _ (M U).toSMul a (eU U x))) =
    eU U (@SMul.smul _ _ (M U).toSMul a x) at hh
  rw [AddEquiv.apply_symm_apply] at hh
  exact hh.symm

set_option backward.isDefEq.respectTransparency false in
/-- Every additive sheaf morphism between `N`-torsion sheaves is linear for their canonical
constant `Z/N` module structures.
Source: Stacks Project, Tag 03CY (auxiliary; not a blueprint node).
Proof: first, transport a normalized action by an additive sheaf automorphism. The
transported action is normalized and commutes with restrictions, so uniqueness makes it
the original action; hence the automorphism is linear. On the direct sum of the two given
module sheaves, apply this to the shear `(x, y) ↦ (x, y + φ(x))`, whose inverse subtracts
`φ(x)`. Composing this linear shear with the first inclusion and second projection gives
exactly `φ`, which is therefore linear. -/
theorem torsionSheaf_hom_linear (N : ℕ) (hN : 0 < N)
    (F G : Sheaf J AddCommGrpCat.{w})
    (hF : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), N • x = 0)
    (hG : ∀ (U : Cᵒᵖ) (x : G.obj.obj U), N • x = 0) (φ : F ⟶ G)
    (M : ∀ U : Cᵒᵖ, Module ((constantZModRingSheaf J N).obj.obj U) (F.obj.obj U))
    (M' : ∀ U : Cᵒᵖ, Module ((constantZModRingSheaf J N).obj.obj U) (G.obj.obj U))
    (hM : IsConstantZModSheafModuleStructure J N F M)
    (hM' : IsConstantZModSheafModuleStructure J N G M') :
    ∀ (U : Cᵒᵖ) (a : (constantZModRingSheaf J N).obj.obj U) (x : F.obj.obj U),
      φ.hom.app U (@SMul.smul _ _ (M U).toSMul a x) =
        @SMul.smul _ _ (M' U).toSMul a (φ.hom.app U x) := by
  have _hF := hF
  have _hG := hG
  let R := constantZModRingSheaf J N
  let A : SheafOfModules.{w} R :=
    ⟨@PresheafOfModules.ofPresheaf _ _ _ F.obj M hM.2, F.property⟩
  let B : SheafOfModules.{w} R :=
    ⟨@PresheafOfModules.ofPresheaf _ _ _ G.obj M' hM'.2, G.property⟩
  have : Limits.HasBinaryBiproduct A B := Limits.HasBinaryBiproduct.of_hasBinaryProduct A B
  let P := Limits.biprod A B
  let V := SheafOfModules.toSheaf.{w} R
  let H := V.obj P
  let i : F ⟶ H := V.map (Limits.biprod.inl : A ⟶ P)
  let p : H ⟶ F := V.map (Limits.biprod.fst : P ⟶ A)
  let j : G ⟶ H := V.map (Limits.biprod.inr : B ⟶ P)
  let q : H ⟶ G := V.map (Limits.biprod.snd : P ⟶ B)
  have hji : j ≫ p = 0 := by
    change V.map _ ≫ V.map _ = 0
    rw [← V.map_comp, Limits.biprod.inr_fst, V.map_zero]
  have hip : i ≫ p = 𝟙 F := by
    change V.map (Limits.biprod.inl : A ⟶ P) ≫ V.map Limits.biprod.fst = 𝟙 (V.obj A)
    rw [← V.map_comp, Limits.biprod.inl_fst, V.map_id]
  have hjq : j ≫ q = 𝟙 G := by
    change V.map (Limits.biprod.inr : B ⟶ P) ≫ V.map Limits.biprod.snd = 𝟙 (V.obj B)
    rw [← V.map_comp, Limits.biprod.inr_snd, V.map_id]
  have hiq : i ≫ q = 0 := by
    change V.map _ ≫ V.map _ = 0
    rw [← V.map_comp, Limits.biprod.inl_snd, V.map_zero]
  let n : H ⟶ H := p ≫ φ ≫ j
  have hn : n ≫ n = 0 := by
    calc
      n ≫ n = p ≫ φ ≫ (j ≫ p) ≫ φ ≫ j := by simp [n, Category.assoc]
      _ = 0 := by rw [hji]; simp
  let e : H ≅ H :=
    { hom := 𝟙 H + n
      inv := 𝟙 H - n
      hom_inv_id := by
        simp [Preadditive.add_comp, Preadditive.comp_sub, hn]
      inv_hom_id := by
        simp [Preadditive.sub_comp, Preadditive.comp_add, hn] }
  let MH (U : Cᵒᵖ) : Module (R.obj.obj U) (P.val.obj U) := inferInstance
  have hMH : IsConstantZModSheafModuleStructure J N H MH := by
    constructor
    · intro U z x
      change @SMul.smul _ _ (MH U).toSMul
        (((toSheafify J ((Functor.const Cᵒᵖ).obj
          (RingCat.of (ULift.{max vC uC} (ZMod N))))).app U).hom
            (z : ULift.{max vC uC} (ZMod N))) x = z • x
      rw [map_intCast]
      exact @Int.cast_smul_eq_zsmul _ _ _ _ (MH U) z x
    · intro U W f a x
      exact P.val.map_smul f a x
  have he := normalized_automorphism_linear J N hN H
    (fun U x ↦ constantZModModuleSheaf_nsmul J N hN P U x) MH hMH e
  let ee : P ⟶ P :=
    ⟨PresheafOfModules.homMk e.hom.hom (fun U a x ↦ he U a x)⟩
  have hf : V.map ((Limits.biprod.inl : A ⟶ P) ≫ ee ≫ Limits.biprod.snd) = φ := by
    change i ≫ (𝟙 H + n) ≫ q = φ
    rw [Preadditive.add_comp, Preadditive.comp_add]
    simp only [Category.id_comp, hiq, zero_add]
    dsimp [n]
    simp only [Category.assoc]
    rw [← Category.assoc i p, hip, Category.id_comp, hjq, Category.comp_id]
  intro U a x
  let f := (Limits.biprod.inl : A ⟶ P) ≫ ee ≫ Limits.biprod.snd
  have hh := congrArg (fun g : F ⟶ G ↦ g.hom.app U) hf
  change (V.map f).hom.app U = φ.hom.app U at hh
  rw [← hh]
  exact (f.val.app U).hom.map_smul a x

end CategoryTheory

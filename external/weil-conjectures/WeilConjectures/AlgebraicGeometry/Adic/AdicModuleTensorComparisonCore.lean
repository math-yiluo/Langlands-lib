/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleSectionComparison
import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
import WeilConjectures.AlgebraicGeometry.AdicTensorComparison.AdicSectionTensorUniversal

/-! # Tensor part of the normalized adic module comparison -/

@[expose] public section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

/-- The tensor part of the normalized comparison for the explicit adic section equivalence.
Source: Stacks 03EK and 03EO
(blueprint: lem-sf-adic-module-tensor-comparison-core). -/
structure AdicModuleTensorComparisonCore (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) where
  /-- The tensor comparison is natural in the first variable. -/
  tensorIso : ∀ M : AdicSheaf l X,
    Mod.tensorLeft M ⋙ (comparisonModuleFunctor l X) ≅
      (comparisonModuleFunctor l X) ⋙ SheafOfModules.siteSheafTensorRight
        (A := comparisonRing l X) ((comparisonModuleFunctor l X).obj M)
  /-- It is natural in the second variable too. -/
  tensor_naturality : ∀ {M M' N N' : AdicSheaf l X} (f : M ⟶ M') (g : N ⟶ N'),
    (comparisonModuleFunctor l X).map ((Mod.tensorLeft N).map f ≫ (Mod.tensorLeftMap g).app M') ≫
        (tensorIso N').hom.app M' =
      (tensorIso N).hom.app M ≫
        (SheafOfModules.siteSheafTensorRight (A := comparisonRing l X)
          ((comparisonModuleFunctor l X).obj N)).map ((comparisonModuleFunctor l X).map f) ≫
          SheafOfModules.siteSheafTensorSecondMap (A := comparisonRing l X)
            ((comparisonModuleFunctor l X).obj M') ((comparisonModuleFunctor l X).map g)
  /-- Tensor comparison sends each canonical pure tensor to the same pure tensor. -/
  tensor_sections : ∀ (M N : AdicSheaf l X) (V : X.ProEtᵒᵖ)
    (x : M.X.obj.obj V) (y : N.X.obj.obj V),
    ((tensorIso N).hom.app M).val.app V
        ((AddEquiv.refl _) (adicComparisonTmul M N V x y)) =
      SheafOfModules.siteSheafTensorTmul (A := comparisonRing l X)
        ((comparisonModuleFunctor l X).obj M) ((comparisonModuleFunctor l X).obj N) V
        ((AddEquiv.refl _) x) ((AddEquiv.refl _) y)

open AdicTensorComparison

attribute [local irreducible] Mod.tensorLeft

open scoped CategoryTheory.Obj

open Functor.LaxMonoidal in
private lemma mapBilinear
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalCategory D] [BraidedCategory D]
    {A : C} [MonObj A] (G : C ⥤ D) [G.LaxBraided]
    {M N P : Mod C A} {q : M.X ⊗ N.X ⟶ P.X} (hq : Mod.IsBilinear q) :
    Mod.IsBilinear (P := (G.mapMod A).obj M) (M := (G.mapMod A).obj N)
      (N := (G.mapMod A).obj P) (Functor.LaxMonoidal.μ G M.X N.X ≫ G.map q) := by
  have hlinear := hq.linear
  rw [← Category.assoc] at hlinear
  constructor
  · change (α_ _ _ _).inv ≫ (μ G A M.X ≫ G.map (Mod.act M.X)) ▷ _ ≫
        (μ G M.X N.X ≫ G.map q) =
      G.obj A ◁ (μ G M.X N.X ≫ G.map q) ≫ (μ G A P.X ≫ G.map (Mod.act P.X))
    simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [μ_natural_left_assoc, ← associativity_inv_assoc, ← G.map_comp_assoc,
      ← G.map_comp, hlinear, G.map_comp, μ_natural_right_assoc]
  · change G.obj M.X ◁ (μ G A N.X ≫ G.map (Mod.act N.X)) ≫
        (μ G M.X N.X ≫ G.map q) =
      (α_ _ _ _).inv ≫
        ((β_ _ _).hom ≫ (μ G A M.X ≫ G.map (Mod.act M.X))) ▷ _ ≫
          (μ G M.X N.X ≫ G.map q)
    simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [μ_natural_right_assoc, ← G.map_comp, hq.balanced, G.map_comp,
      associativity_inv_assoc, G.map_comp, ← μ_natural_left_assoc]
    simp only [Mod.rightAct, G.map_comp, comp_whiskerRight, Category.assoc]
    rw [← comp_whiskerRight_assoc, Functor.LaxBraided.braided,
      comp_whiskerRight_assoc]

private noncomputable def presheafPairing {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M N P : Mod (X.ProEtᵒᵖ ⥤ WeilCoefficients.{u} l) (adicConstantSheaf l X).obj)
    (q : M.X ⊗ N.X ⟶ P.X) (hq : Mod.IsBilinear q) (V : X.ProEtᵒᵖ) :
    (comparisonModulePresheaf M).obj V →ₗ[(comparisonRing l X).obj.obj V]
      (comparisonModulePresheaf N).obj V →ₗ[(comparisonRing l X).obj.obj V]
        (comparisonModulePresheaf P).obj V := by
  refine LinearMap.mk₂ _ (fun (x : M.X.obj V) (y : N.X.obj V) ↦ q.app V (x ⊗ₜ y)) ?_ ?_ ?_ ?_
  · intro x x' y
    rw [TensorProduct.add_tmul, map_add]
  · intro r x y
    change ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l V.unop.left) at r
    change M.X.obj V at x
    change N.X.obj V at y
    exact ConcreteCategory.congr_hom (congr_app hq.linear V) (r ⊗ₜ (x ⊗ₜ y))
  · intro x y y'
    rw [TensorProduct.tmul_add, map_add]
  · intro r x y
    change ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l V.unop.left) at r
    change M.X.obj V at x
    change N.X.obj V at y
    have h := ConcreteCategory.congr_hom (congr_app hq.balanced V)
      (x ⊗ₜ (TensorProduct.tmul (ULift.{u + 1} (PadicAlgCl l))
        (M := (adicConstantSheaf l X).obj.obj V) (N := N.X.obj V) r y))
    exact h.trans (ConcreteCategory.congr_hom (congr_app hq.linear V)
      (r ⊗ₜ (x ⊗ₜ y)))

private noncomputable def nativePairing {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M N : AdicSheaf l X) (V : X.ProEtᵒᵖ) :
    ((comparisonModuleFunctor l X).obj M).val.obj V →ₗ[(comparisonRing l X).obj.obj V]
      ((comparisonModuleFunctor l X).obj N).val.obj V →ₗ[(comparisonRing l X).obj.obj V]
        ((comparisonModuleFunctor l X).obj ((Mod.tensorLeft N).obj M)).val.obj V := by
  let G := sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)
  let q := Functor.LaxMonoidal.μ G M.X N.X ≫ G.map (Mod.tensorπ M N)
  have hq : Mod.IsBilinear
      (P := (comparisonPresheafFunctor l X).obj M)
      (M := (comparisonPresheafFunctor l X).obj N)
      (N := (comparisonPresheafFunctor l X).obj ((Mod.tensorLeft N).obj M)) q := by
    have h := mapBilinear G (Mod.isBilinear_tensorπ M N)
    constructor
    · dsimp only [comparisonPresheafFunctor, Functor.comp_obj]
      rw [Mod.act_comap_obj, Mod.act_comap_obj]
      simpa only [id_whiskerRight, Category.id_comp, Mod.comap, G, q,
        Functor.act_mapMod_obj, Functor.mapMod, ObjectProperty.ι_obj] using h.linear
    · dsimp only [comparisonPresheafFunctor, Functor.comp_obj]
      simp only [Mod.rightAct, Mod.act_comap_obj, id_whiskerRight, Category.id_comp]
      simpa only [Mod.rightAct, Mod.comap, G, q, Functor.act_mapMod_obj,
        Functor.mapMod, ObjectProperty.ι_obj] using h.balanced
  exact presheafPairing _ _ _ q hq V

private lemma nativePairing_naturality {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M N : AdicSheaf l X) {V W : X.ProEtᵒᵖ} (i : V ⟶ W)
    (x : M.X.obj.obj V) (y : N.X.obj.obj V) :
    nativePairing M N W (M.X.obj.map i x) (N.X.obj.map i y) =
      ((Mod.tensorLeft N).obj M).X.obj.map i (nativePairing M N V x y) := by
  let q := Sheaf.tensorObjComparison (Scheme.ProEt.topology X) M.X N.X ≫
    (Mod.tensorπ M N).hom
  exact (ConcreteCategory.congr_hom (q.naturality i) (x ⊗ₜ y))

open Functor.LaxMonoidal in
private lemma nativeBilinear_of_presheaf {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M N P : AdicSheaf l X) (q : M.X ⊗ N.X ⟶ P.X)
    (hq : Mod.IsBilinear
      (P := ((sheafToPresheaf (Scheme.ProEt.topology X)
        (WeilCoefficients.{u} l)).mapMod (adicConstantSheaf l X)).obj M)
      (M := ((sheafToPresheaf (Scheme.ProEt.topology X)
        (WeilCoefficients.{u} l)).mapMod (adicConstantSheaf l X)).obj N)
      (N := ((sheafToPresheaf (Scheme.ProEt.topology X)
        (WeilCoefficients.{u} l)).mapMod (adicConstantSheaf l X)).obj P)
      (μ (sheafToPresheaf _ _) M.X N.X ≫ q.hom)) : Mod.IsBilinear q := by
  let G := sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)
  let A := adicConstantSheaf l X
  have hlinear : (α_ (G.obj A) (G.obj M.X) (G.obj N.X)).inv ≫
      (μ G A M.X ≫ G.map (Mod.act M.X)) ▷ G.obj N.X ≫ (μ G M.X N.X ≫ G.map q) =
      G.obj A ◁ (μ G M.X N.X ≫ G.map q) ≫ (μ G A P.X ≫ G.map (Mod.act P.X)) :=
    hq.linear
  have hbalanced : G.obj M.X ◁ (μ G A N.X ≫ G.map (Mod.act N.X)) ≫
      (μ G M.X N.X ≫ G.map q) =
      (α_ (G.obj M.X) (G.obj A) (G.obj N.X)).inv ≫
        ((β_ (G.obj M.X) (G.obj A)).hom ≫ (μ G A M.X ≫ G.map (Mod.act M.X))) ▷
          G.obj N.X ≫ (μ G M.X N.X ≫ G.map q) := hq.balanced
  constructor
  · have hl : Mod.act M.X ▷ N.X ≫ q =
        (α_ A M.X N.X).hom ≫ A ◁ q ≫ Mod.act P.X := by
      apply sheafTriple_ext
      change μ G A M.X ▷ G.obj N.X ≫ μ G (A ⊗ M.X) N.X ≫
          G.map (Mod.act M.X ▷ N.X ≫ q) =
        μ G A M.X ▷ G.obj N.X ≫ μ G (A ⊗ M.X) N.X ≫
          G.map ((α_ A M.X N.X).hom ≫ A ◁ q ≫ Mod.act P.X)
      simp only [G.map_comp]
      rw [← μ_natural_left_assoc G, associativity_assoc G, ← μ_natural_right_assoc G]
      simpa only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
        Category.assoc, Iso.hom_inv_id_assoc] using
          congrArg ((α_ (G.obj A) (G.obj M.X) (G.obj N.X)).hom ≫ ·) hlinear
    rw [hl, Iso.inv_hom_id_assoc]
  · have hb : (α_ M.X A N.X).hom ≫ M.X ◁ Mod.act N.X ≫ q =
        Mod.rightAct M ▷ N.X ≫ q := by
      apply sheafTriple_ext
      change μ G M.X A ▷ G.obj N.X ≫ μ G (M.X ⊗ A) N.X ≫
          G.map ((α_ M.X A N.X).hom ≫ M.X ◁ Mod.act N.X ≫ q) =
        μ G M.X A ▷ G.obj N.X ≫ μ G (M.X ⊗ A) N.X ≫
          G.map (Mod.rightAct M ▷ N.X ≫ q)
      simp only [G.map_comp]
      rw [associativity_assoc G, ← μ_natural_right_assoc G, ← μ_natural_left_assoc G]
      have ha : μ G M.X A ≫ G.map (Mod.rightAct M) =
          (β_ (G.obj M.X) (G.obj A)).hom ≫ μ G A M.X ≫ G.map (Mod.act M.X) := by
        change μ G M.X A ≫ G.map ((β_ M.X A).hom ≫ Mod.act M.X) = _
        rw [G.map_comp, Functor.LaxBraided.braided_assoc]
      rw [← comp_whiskerRight_assoc, ha]
      simpa only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
        Category.assoc, Iso.hom_inv_id_assoc] using
          congrArg ((α_ (G.obj M.X) (G.obj A) (G.obj N.X)).hom ≫ ·) hbalanced
    rw [← hb, Iso.inv_hom_id_assoc]

private lemma nativeTensor_exists {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M N P : AdicSheaf l X)
    (b : ∀ V : X.ProEtᵒᵖ,
      ((comparisonModuleFunctor l X).obj M).val.obj V →ₗ[(comparisonRing l X).obj.obj V]
        ((comparisonModuleFunctor l X).obj N).val.obj V →ₗ[(comparisonRing l X).obj.obj V]
          ((comparisonModuleFunctor l X).obj P).val.obj V)
    (hb : ∀ {V W : X.ProEtᵒᵖ} (i : V ⟶ W) (x : M.X.obj.obj V) (y : N.X.obj.obj V),
      b W (M.X.obj.map i x) (N.X.obj.map i y) = P.X.obj.map i (b V x y)) :
    ∃! f : (Mod.tensorLeft N).obj M ⟶ P,
      ∀ (V : X.ProEtᵒᵖ) (x : M.X.obj.obj V) (y : N.X.obj.obj V),
        f.hom.hom.app V (adicComparisonTmul M N V x y) = b V x y := by
  let bk (V : X.ProEtᵒᵖ) :
      M.X.obj.obj V →ₗ[ULift.{u + 1} (PadicAlgCl l)]
        N.X.obj.obj V →ₗ[ULift.{u + 1} (PadicAlgCl l)] P.X.obj.obj V :=
    LinearMap.mk₂ _ (fun x y ↦ b V x y)
      (fun x x' y ↦ LinearMap.congr_fun ((b V).map_add x x') y)
      (fun c x y ↦ by
        rw [← comparison_constant_smul M V c x,
          ← comparison_constant_smul P V c (b V x y)]
        exact LinearMap.congr_fun ((b V).map_smul _ x) y)
      (fun x y y' ↦ (b V x).map_add y y')
      (fun c x y ↦ by
        rw [← comparison_constant_smul N V c y,
          ← comparison_constant_smul P V c (b V x y)]
        exact (b V x).map_smul _ y)
  let q : M.X.obj ⊗ N.X.obj ⟶ P.X.obj :=
    { app V := ModuleCat.ofHom (TensorProduct.lift (bk V))
      naturality := by
        intro V W i
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        exact hb i }
  obtain ⟨f, hf⟩ := sheafTensor_exists M.X N.X P.X q
  have hq : Mod.IsBilinear
      (P := ((sheafToPresheaf (Scheme.ProEt.topology X)
        (WeilCoefficients.{u} l)).mapMod (adicConstantSheaf l X)).obj M)
      (M := ((sheafToPresheaf (Scheme.ProEt.topology X)
        (WeilCoefficients.{u} l)).mapMod (adicConstantSheaf l X)).obj N)
      (N := ((sheafToPresheaf (Scheme.ProEt.topology X)
        (WeilCoefficients.{u} l)).mapMod (adicConstantSheaf l X)).obj P) q := by
    constructor
    · apply NatTrans.ext
      funext V
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro r z
      induction z using TensorProduct.inductionOn with
      | add z w hz hw => simp only [TensorProduct.tmul_add, map_add, hz, hw]
      | tmul x y =>
        exact LinearMap.congr_fun ((b V).map_smul r x) y
    · apply NatTrans.ext
      funext V
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x z
      induction z using TensorProduct.inductionOn with
      | add z w hz hw => simp only [TensorProduct.tmul_add, map_add, hz, hw]
      | tmul r y =>
        exact ((b V x).map_smul r y).trans
          (LinearMap.congr_fun ((b V).map_smul r x) y).symm
  have hf' : Mod.IsBilinear f :=
    nativeBilinear_of_presheaf M N P f (by rw [hf]; exact hq)
  let t := Mod.tensorDesc f hf'
  have ht : ∀ (V : X.ProEtᵒᵖ) (x : M.X.obj.obj V) (y : N.X.obj.obj V),
      t.hom.hom.app V (adicComparisonTmul M N V x y) = b V x y := by
    intro V x y
    have he := congrArg (fun s ↦ s.hom.app V
      ((Sheaf.tensorObjComparison (Scheme.ProEt.topology X) M.X N.X).app V (x ⊗ₜ y)))
        (Mod.tensorπ_tensorDesc f hf')
    exact he.trans (ConcreteCategory.congr_hom (congr_app hf V) (x ⊗ₜ y))
  refine ⟨t, ht, fun g hg ↦ nativeTensor_ext M N P g t ?_⟩
  intro V x y
  exact (hg V x y).trans (ht V x y).symm

private lemma nativeTensorImage_ext {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M N : AdicSheaf l X) (P : SectionModule (l := l) (X := X))
    (f g : (comparisonModuleFunctor l X).obj ((Mod.tensorLeft N).obj M) ⟶ P)
    (h : ∀ (V : X.ProEtᵒᵖ) (x : M.X.obj.obj V) (y : N.X.obj.obj V),
      f.val.app V (adicComparisonTmul M N V x y) =
        g.val.app V (adicComparisonTmul M N V x y)) : f = g := by
  let e := comparisonLiftCounit P
  have he : comparisonPreimageMap (f ≫ e.inv) = comparisonPreimageMap (g ≫ e.inv) := by
    apply nativeTensor_ext M N (comparisonLiftModule P)
    intro V x y
    exact congrArg (e.inv.val.app V) (h V x y)
  apply (cancel_mono e.inv).mp
  calc
    f ≫ e.inv = (comparisonModuleFunctor l X).map
        (comparisonPreimageMap (f ≫ e.inv)) :=
      ((comparisonModuleFullyFaithful l X).map_preimage _).symm
    _ = (comparisonModuleFunctor l X).map
        (comparisonPreimageMap (g ≫ e.inv)) := congrArg _ he
    _ = g ≫ e.inv := (comparisonModuleFullyFaithful l X).map_preimage _

private lemma nativeTensorImage_exists {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M N : AdicSheaf l X) :
    ∃ f : (comparisonModuleFunctor l X).obj ((Mod.tensorLeft N).obj M) ⟶
      (SheafOfModules.siteSheafTensorRight (A := comparisonRing l X)
        ((comparisonModuleFunctor l X).obj N)).obj ((comparisonModuleFunctor l X).obj M),
      ∀ (V : X.ProEtᵒᵖ) (x : M.X.obj.obj V) (y : N.X.obj.obj V),
        f.val.app V (adicComparisonTmul M N V x y) =
          SheafOfModules.siteSheafTensorTmul (A := comparisonRing l X)
            ((comparisonModuleFunctor l X).obj M) ((comparisonModuleFunctor l X).obj N) V x y := by
  let F := comparisonModuleFunctor l X
  let T := (SheafOfModules.siteSheafTensorRight (A := comparisonRing l X)
    (F.obj N)).obj (F.obj M)
  let P := comparisonLiftModule T
  let e : F.obj P ≅ T := comparisonLiftCounit T
  let b (V : X.ProEtᵒᵖ) := (sectionPairing (F.obj M) (F.obj N) V).compr₂
    (e.inv.val.app V).hom
  have hb : ∀ {V W : X.ProEtᵒᵖ} (i : V ⟶ W) (x : M.X.obj.obj V) (y : N.X.obj.obj V),
      b W (M.X.obj.map i x) (N.X.obj.map i y) = P.X.obj.map i (b V x y) := by
    intro V W i x y
    change e.inv.val.app W (sectionPairing (F.obj M) (F.obj N) W
      ((F.obj M).val.map i x) ((F.obj N).val.map i y)) = _
    rw [sectionPairing_naturality]
    exact PresheafOfModules.naturality_apply e.inv.val i _
  obtain ⟨f, hf, _⟩ := nativeTensor_exists M N P b hb
  refine ⟨F.map f ≫ e.hom, ?_⟩
  intro V x y
  change e.hom.val.app V (f.hom.hom.app V (adicComparisonTmul M N V x y)) = _
  rw [hf]
  exact congrArg (fun t : T ⟶ T ↦ t.val.app V
    (SheafOfModules.siteSheafTensorTmul (F.obj M) (F.obj N) V x y)) e.inv_hom_id

/-- The normalized tensor comparison exists for every prime and scheme.

Proof: construct the map from the native balanced coequalizer and the sectionwise
sheaf tensor by the universal property of sheafification.  The two balancing
squares are checked on threefold pure tensors, and the inverse is obtained from
the native quotient pairing.  Pure-tensor extensionality proves the two maps
inverse and gives both naturality and the displayed section formula.
Source: Stacks 03EK and 03EO
(blueprint: lem-sf-adic-module-tensor-comparison-core). -/
theorem adicModuleTensorComparisonCore (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Nonempty (AdicModuleTensorComparisonCore l X) := by
  classical
  let F := comparisonModuleFunctor l X
  choose f hf using (fun M N : AdicSheaf l X ↦ nativeTensorImage_exists M N)
  have hinv (M N : AdicSheaf l X) := sectionTensor_exists
    (F.obj M) (F.obj N) (F.obj ((Mod.tensorLeft N).obj M))
      (nativePairing M N) (nativePairing_naturality M N)
  choose g hg _ using hinv
  let e (M N : AdicSheaf l X) : F.obj ((Mod.tensorLeft N).obj M) ≅
      (SheafOfModules.siteSheafTensorRight (A := comparisonRing l X) (F.obj N)).obj
        (F.obj M) :=
    { hom := f M N
      inv := g M N
      hom_inv_id := by
        apply nativeTensorImage_ext
        intro V x y
        change (g M N).val.app V ((f M N).val.app V (adicComparisonTmul M N V x y)) = _
        rw [hf, hg]
        rfl
      inv_hom_id := by
        apply sectionTensor_ext
        intro V x y
        change (f M N).val.app V ((g M N).val.app V
          (SheafOfModules.siteSheafTensorTmul (F.obj M) (F.obj N) V x y)) = _
        rw [hg]
        exact hf M N V x y }
  have he (M N : AdicSheaf l X) (V : X.ProEtᵒᵖ)
      (x : M.X.obj.obj V) (y : N.X.obj.obj V) :
      (e M N).hom.val.app V (adicComparisonTmul M N V x y) =
        SheafOfModules.siteSheafTensorTmul (F.obj M) (F.obj N) V x y := hf M N V x y
  have hnat {M M' N N' : AdicSheaf l X} (a : M ⟶ M') (b : N ⟶ N') :
      F.map ((Mod.tensorLeft N).map a ≫ (Mod.tensorLeftMap b).app M') ≫ (e M' N').hom =
        (e M N).hom ≫
          (SheafOfModules.siteSheafTensorRight (A := comparisonRing l X) (F.obj N)).map
            (F.map a) ≫ SheafOfModules.siteSheafTensorSecondMap (F.obj M') (F.map b) := by
    apply nativeTensorImage_ext
    intro V x y
    change (e M' N').hom.val.app V
      (((Mod.tensorLeft N).map a ≫ (Mod.tensorLeftMap b).app M').hom.hom.app V
        (adicComparisonTmul M N V x y)) = _
    rw [nativeTensor_map, he]
    change _ =
      ((SheafOfModules.siteSheafTensorRight (A := comparisonRing l X) (F.obj N)).map
          (F.map a) ≫ SheafOfModules.siteSheafTensorSecondMap (F.obj M') (F.map b)).val.app V
        ((e M N).hom.val.app V (adicComparisonTmul M N V x y))
    rw [he, sectionTensor_map]
    rfl
  let t (N : AdicSheaf l X) : Mod.tensorLeft N ⋙ F ≅
      F ⋙ SheafOfModules.siteSheafTensorRight (A := comparisonRing l X) (F.obj N) :=
    NatIso.ofComponents (fun M ↦ e M N) (fun {M M'} a ↦ by
      have h := hnat a (𝟙 N)
      simpa only [Mod.tensorLeftMap_id, NatTrans.id_app, Category.comp_id,
        F.map_id, sectionTensor_second_id, Functor.comp_obj, Functor.comp_map] using h)
  exact ⟨{ tensorIso := t
           tensor_naturality := hnat
           tensor_sections := he }⟩

end AlgebraicGeometry.ProEtale

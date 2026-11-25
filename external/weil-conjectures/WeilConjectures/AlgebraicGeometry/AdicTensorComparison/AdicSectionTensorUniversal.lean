/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleSectionComparison
import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose

/-! # Universal properties of sectionwise and vector-space sheaf tensors

The sectionwise tensor represents natural bilinear pairings by the module-sheafification
adjunction. Vector-space sheafification similarly detects tensor diagrams and extends
presheaf pairings. These are the sheafification steps in the native tensor comparison.
Source: Stacks, Sites of Modules, Tags 03EK and 03EO.
(blueprint: lem-sf-adic-section-tensor-universal).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale.AdicTensorComparison

attribute [local irreducible] Mod.tensorLeft

private lemma nativeTensorator_eq {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M N : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) :
    Functor.LaxMonoidal.μ (sheafToPresheaf _ _) M N =
      Sheaf.tensorObjComparison (Scheme.ProEt.topology X) M N := by
  rfl

/-- Native tensor maps are determined on their canonical pure-tensor sections.
Source: native balanced coequalizer descent and sheaf tensor extensionality.
(blueprint: lem-sf-adic-section-tensor-universal). -/
lemma nativeTensor_ext {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M N P : AdicSheaf l X) (f g : (Mod.tensorLeft N).obj M ⟶ P)
    (h : ∀ (V : X.ProEtᵒᵖ) (x : M.X.obj.obj V) (y : N.X.obj.obj V),
      f.hom.hom.app V (adicComparisonTmul M N V x y) =
        g.hom.hom.app V (adicComparisonTmul M N V x y)) : f = g := by
  apply Mod.tensorLeft_obj_hom_ext
  apply Sheaf.tensor_hom_ext
  rw [nativeTensorator_eq]
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  exact h V

/-- Native tensor maps act on the two pure-tensor factors sectionwise.
Source: naturality of the native tensor quotient and vector-space sheaf tensorator.
(blueprint: lem-sf-adic-section-tensor-universal). -/
lemma nativeTensor_map {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    {M M' N N' : AdicSheaf l X} (f : M ⟶ M') (g : N ⟶ N')
    (V : X.ProEtᵒᵖ) (x : M.X.obj.obj V) (y : N.X.obj.obj V) :
    ((Mod.tensorLeft N).map f ≫ (Mod.tensorLeftMap g).app M').hom.hom.app V
        (adicComparisonTmul M N V x y) =
      adicComparisonTmul M' N' V (f.hom.hom.app V x) (g.hom.hom.app V y) := by
  have h := Mod.tensorπ_map N f
  have h' := Mod.tensorπ_tensorLeftMap M' g
  have ht := Sheaf.tensorObjComparison_naturality f.hom g.hom
  have hh : Mod.tensorπ M N ≫
      ((Mod.tensorLeft N).map f ≫ (Mod.tensorLeftMap g).app M').hom =
      (f.hom ⊗ₘ g.hom) ≫ Mod.tensorπ M' N' := by
    rw [Mod.comp_hom', ← Category.assoc, h, Category.assoc, h']
    simp only [← Category.assoc, tensorHom_def]
  have he := congrArg (fun t ↦ t.hom.app V
    ((Sheaf.tensorObjComparison (Scheme.ProEt.topology X) M.X N.X).app V
      (x ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] y))) hh
  change _ = (Mod.tensorπ M' N').hom.app V
    ((f.hom ⊗ₘ g.hom).hom.app V
      ((Sheaf.tensorObjComparison (Scheme.ProEt.topology X) M.X N.X).app V
        (x ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] y))) at he
  exact he.trans (congrArg ((Mod.tensorπ M' N').hom.app V)
    (ConcreteCategory.congr_hom (congr_app ht V) (x ⊗ₜ y)))

section SiteTensor

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

abbrev SectionModule := SheafOfModules.{u + 1}
  ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l X))

lemma sectionTensor_ext (M N P : SectionModule (l := l) (X := X))
    (f g : (SheafOfModules.siteSheafTensorRight (A := comparisonRing l X) N).obj M ⟶ P)
    (h : ∀ (V : X.ProEtᵒᵖ) (x : M.val.obj V) (y : N.val.obj V),
      f.val.app V (SheafOfModules.siteSheafTensorTmul M N V x y) =
        g.val.app V (SheafOfModules.siteSheafTensorTmul M N V x y)) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l X)) (𝟙 _)
  apply (adj.homEquiv (SheafOfModules.siteTensorPresheaf M.val N.val) P).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext V : 1
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  exact h V

lemma sectionTensor_map {M M' N N' : SectionModule (l := l) (X := X)}
    (f : M ⟶ M') (g : N ⟶ N') (V : X.ProEtᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    ((SheafOfModules.siteSheafTensorRight (A := comparisonRing l X) N).map f ≫
        SheafOfModules.siteSheafTensorSecondMap M' g).val.app V
      (SheafOfModules.siteSheafTensorTmul M N V x y) =
        SheafOfModules.siteSheafTensorTmul M' N' V (f.val.app V x) (g.val.app V y) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l X)) (𝟙 _)
  let q := SheafOfModules.siteTensorHom f.val N.val ≫
    SheafOfModules.siteTensorSecondMap M'.val g.val
  have h := adj.unit.naturality q
  have he := congrArg (fun t ↦ (t.app V) (x ⊗ₜ[(comparisonRing l X).obj.obj V] y)) h
  change SheafOfModules.siteSheafTensorTmul M' N' V (f.val.app V x) (g.val.app V y) =
    (((PresheafOfModules.sheafification
      (R := (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l X))
      (𝟙 _)).map q).val.app V)
      (SheafOfModules.siteSheafTensorTmul M N V x y) at he
  rw [Functor.map_comp] at he
  exact he.symm

/-- Natural bilinear pairings extend uniquely across the sectionwise sheaf tensor.

Proof: use `TensorProduct.lift` at every site object, apply the module-sheafification
adjunction to the resulting presheaf morphism, and compute the extension on pure tensors
with the adjunction unit. Tensor extensionality and injectivity of the adjunction bijection
prove uniqueness. This also applies to zero modules and empty site objects.
Source: Stacks, Sites of Modules, Tag 03EK.
(blueprint: lem-sf-adic-section-tensor-universal). -/
lemma sectionTensor_exists (M N P : SectionModule (l := l) (X := X))
    (b : ∀ V : X.ProEtᵒᵖ, M.val.obj V →ₗ[(comparisonRing l X).obj.obj V]
      N.val.obj V →ₗ[(comparisonRing l X).obj.obj V] P.val.obj V)
    (hb : ∀ {V W : X.ProEtᵒᵖ} (i : V ⟶ W) (x : M.val.obj V) (y : N.val.obj V),
      b W (M.val.map i x) (N.val.map i y) = P.val.map i (b V x y)) :
    ∃! f : (SheafOfModules.siteSheafTensorRight (A := comparisonRing l X) N).obj M ⟶ P,
      ∀ (V : X.ProEtᵒᵖ) (x : M.val.obj V) (y : N.val.obj V),
        f.val.app V (SheafOfModules.siteSheafTensorTmul M N V x y) = b V x y := by
  let q : SheafOfModules.siteTensorPresheaf M.val N.val ⟶ P.val :=
    { app V := ModuleCat.ofHom (TensorProduct.lift (b V))
      naturality := by
        intro V W i
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        exact hb i }
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l X)) (𝟙 _)
  let f := (adj.homEquiv _ P).symm q
  have hf : ∀ (V : X.ProEtᵒᵖ) (x : M.val.obj V) (y : N.val.obj V),
      f.val.app V (SheafOfModules.siteSheafTensorTmul M N V x y) = b V x y := by
    intro V x y
    have h := (adj.homEquiv _ P).apply_symm_apply q
    rw [Adjunction.homEquiv_unit] at h
    exact congrArg (fun t ↦ t.app V (x ⊗ₜ[(comparisonRing l X).obj.obj V] y)) h
  refine ⟨f, hf, fun g hg ↦ sectionTensor_ext M N P g f ?_⟩
  intro V x y
  exact (hg V x y).trans (hf V x y).symm

noncomputable def sectionPairing (M N : SectionModule (l := l) (X := X))
    (V : X.ProEtᵒᵖ) : M.val.obj V →ₗ[(comparisonRing l X).obj.obj V]
      N.val.obj V →ₗ[(comparisonRing l X).obj.obj V]
        ((SheafOfModules.siteSheafTensorRight (A := comparisonRing l X) N).obj M).val.obj V :=
  (TensorProduct.mk ((comparisonRing l X).obj.obj V) (M.val.obj V) (N.val.obj V)).compr₂
    (((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l X)) (𝟙 _)).unit.app
      (SheafOfModules.siteTensorPresheaf M.val N.val)).app V).hom

lemma sectionPairing_naturality (M N : SectionModule (l := l) (X := X))
    {V W : X.ProEtᵒᵖ} (i : V ⟶ W) (x : M.val.obj V) (y : N.val.obj V) :
    sectionPairing M N W (M.val.map i x) (N.val.map i y) =
      ((SheafOfModules.siteSheafTensorRight (A := comparisonRing l X) N).obj M).val.map i
        (sectionPairing M N V x y) := by
  exact PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l X)) (𝟙 _)).unit.app
        (SheafOfModules.siteTensorPresheaf M.val N.val)) i (x ⊗ₜ y)

lemma sectionTensor_second_id (M N : SectionModule (l := l) (X := X)) :
    SheafOfModules.siteSheafTensorSecondMap (A := comparisonRing l X) M (𝟙 N) =
      𝟙 ((SheafOfModules.siteSheafTensorRight (A := comparisonRing l X) N).obj M) := by
  apply sectionTensor_ext
  intro V x y
  have h := sectionTensor_map (𝟙 M) (𝟙 N) V x y
  rw [(SheafOfModules.siteSheafTensorRight (A := comparisonRing l X) N).map_id,
    Category.id_comp] at h
  simpa only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] using h

end SiteTensor

open Functor.LaxMonoidal in
lemma sheafTriple_ext {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M N P Q : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))
    (f g : (M ⊗ N) ⊗ P ⟶ Q)
    (h : μ (sheafToPresheaf _ _) M N ▷ P.obj ≫
      μ (sheafToPresheaf _ _) (M ⊗ N) P ≫ f.hom =
      μ (sheafToPresheaf _ _) M N ▷ P.obj ≫
        μ (sheafToPresheaf _ _) (M ⊗ N) P ≫ g.hom) : f = g := by
  let G := sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)
  let L := presheafToSheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)
  let adj := sheafificationAdjunction (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)
  have hi : IsIso (L.map (μ G M N)) := by
    have he : (adj.homEquiv _ _).symm (μ G M N) =
        Functor.OplaxMonoidal.δ L _ _ ≫ (adj.counit.app M ⊗ₘ adj.counit.app N) :=
      (adj.homEquiv _ _).symm_apply_apply _
    have : IsIso ((adj.homEquiv _ _).symm (μ G M N)) := by
      rw [he]
      infer_instance
    rw [Adjunction.homEquiv_counit] at this
    exact IsIso.of_isIso_comp_right _ (adj.counit.app (M ⊗ N))
  have his : IsIso (L.map (μ G M N ▷ P.obj)) := by
    have : IsIso (μ L _ P.obj ≫ L.map (μ G M N ▷ P.obj)) := by
      rw [← μ_natural_left]
      infer_instance
    exact IsIso.of_isIso_comp_left (μ L _ P.obj) _
  apply Sheaf.tensor_hom_ext
  apply (adj.homEquiv _ Q).symm.injective
  apply (cancel_epi (L.map (μ G M N ▷ P.obj))).mp
  simpa only [Adjunction.homEquiv_naturality_left_symm, Category.assoc,
    G, L, ObjectProperty.ι_map] using
    congrArg (adj.homEquiv _ Q).symm h

lemma sheafTensor_exists {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M N P : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))
    (q : M.obj ⊗ N.obj ⟶ P.obj) :
    ∃ f : M ⊗ N ⟶ P,
      Functor.LaxMonoidal.μ (sheafToPresheaf _ _) M N ≫ f.hom = q := by
  let L := presheafToSheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)
  let adj := sheafificationAdjunction (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)
  let e : L.obj (M.obj ⊗ N.obj) ≅ M ⊗ N :=
    asIso (Functor.OplaxMonoidal.δ L _ _ ≫ (adj.counit.app M ⊗ₘ adj.counit.app N))
  let f := e.inv ≫ (adj.homEquiv _ P).symm q
  refine ⟨f, ?_⟩
  change adj.homEquiv _ _ e.hom ≫ (sheafToPresheaf _ _).map f = q
  rw [← Adjunction.homEquiv_naturality_right]
  dsimp only [f]
  rw [← Category.assoc, e.hom_inv_id]
  erw [Category.id_comp]
  exact (adj.homEquiv _ P).apply_symm_apply q

end AlgebraicGeometry.ProEtale.AdicTensorComparison

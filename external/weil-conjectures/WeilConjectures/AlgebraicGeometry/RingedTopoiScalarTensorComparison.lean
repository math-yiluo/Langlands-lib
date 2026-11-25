/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import all WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction

/-! # Scalar extension and the normalized tensor comparison

Source: Stacks Project, Modules on Sites, Tags 03EL and 0GMW.
(auxiliary; not a blueprint node).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings TensorProduct
namespace SheafOfModules.RingedTensor
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {A B : Sheaf J CommRingCat.{u}} (c : A ⟶ B)

private noncomputable def rawContraction
    (M N : SheafOfModules.{u} (ringSheaf A)) (W : Cᵒᵖ) :
    (changeOfRingsPresheaf.{u, u, u} c M).obj W ⊗[B.obj.obj W]
      (changeOfRingsPresheaf.{u, u, u} c N).obj W →ₗ[B.obj.obj W]
        (changeOfRingsPresheaf.{u, u, u} c ((monoidalCategory A).tensorObj M N)).obj W := by
  letI := (c.hom.app W).hom.toAlgebra
  exact ((ModuleCat.extendScalars (c.hom.app W).hom).map
    ((pureMap A M N).app W)).hom.comp
      (TensorProduct.AlgebraTensorModule.distribBaseChange
        (A.obj.obj W) (B.obj.obj W) (M.val.obj W) (N.val.obj W)).symm.toLinearMap

private theorem rawContraction_tmul
    (M N : SheafOfModules.{u} (ringSheaf A)) (W : Cᵒᵖ)
    (s t : B.obj.obj W) (m : M.val.obj W) (n : N.val.obj W) :
    rawContraction c M N W
      ((s ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m) ⊗ₜ[B.obj.obj W]
        (t ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n)) =
      (s * t) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] pure A M N W m n := by
  let := (c.hom.app W).hom.toAlgebra
  change ((ModuleCat.extendScalars (c.hom.app W).hom).map
    ((pureMap A M N).app W)).hom
      ((TensorProduct.AlgebraTensorModule.distribBaseChange
        (A.obj.obj W) (B.obj.obj W) (M.val.obj W) (N.val.obj W)).symm
          ((s ⊗ₜ[A.obj.obj W] m) ⊗ₜ[B.obj.obj W] (t ⊗ₜ[A.obj.obj W] n))) = _
  rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]
  rfl

private noncomputable def rawPairing
    (M N : SheafOfModules.{u} (ringSheaf A)) (W : Cᵒᵖ) :
    (changeOfRingsPresheaf.{u, u, u} c M).obj W →ₗ[B.obj.obj W]
      (changeOfRingsPresheaf.{u, u, u} c N).obj W →ₗ[B.obj.obj W]
        (changeOfRings.{u, u, u} c ((monoidalCategory A).tensorObj M N)).val.obj W :=
  TensorProduct.curry
    ((((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)).unit.app
      (changeOfRingsPresheaf.{u, u, u} c ((monoidalCategory A).tensorObj M N))).app W).hom.comp
        (rawContraction c M N W))

private theorem rawPairing_tmul
    (M N : SheafOfModules.{u} (ringSheaf A)) (W : Cᵒᵖ)
    (s t : B.obj.obj W) (m : M.val.obj W) (n : N.val.obj W) :
    rawPairing c M N W
      (s ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)
      (t ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) =
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)).unit.app
      (changeOfRingsPresheaf.{u, u, u} c ((monoidalCategory A).tensorObj M N))).app W
        ((s * t) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] pure A M N W m n)) := by
  change (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)).unit.app
    (changeOfRingsPresheaf.{u, u, u} c ((monoidalCategory A).tensorObj M N))).app W
      (rawContraction c M N W _) = _)
  exact congrArg _ (rawContraction_tmul c M N W s t m n)

private theorem rawPairing_restrict
    (M N : SheafOfModules.{u} (ringSheaf A)) {W V : Cᵒᵖ} (i : W ⟶ V)
    (x : (changeOfRingsPresheaf.{u, u, u} c M).obj W)
    (y : (changeOfRingsPresheaf.{u, u, u} c N).obj W) :
    rawPairing c M N V ((changeOfRingsPresheaf.{u, u, u} c M).map i x)
      ((changeOfRingsPresheaf.{u, u, u} c N).map i y) =
    (changeOfRings.{u, u, u} c ((monoidalCategory A).tensorObj M N)).val.map i
      (rawPairing c M N W x y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul s m =>
    change B.obj.obj W at s
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul t n =>
      change B.obj.obj W at t
      rw [tensorRestriction_tmul, tensorRestriction_tmul, rawPairing_tmul,
        rawPairing_tmul]
      have h := PresheafOfModules.naturality_apply
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)).unit.app
          (changeOfRingsPresheaf.{u, u, u} c ((monoidalCategory A).tensorObj M N)))
        i ((s * t) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] pure A M N W m n)
      have hm := tensorRestriction_tmul c ((monoidalCategory A).tensorObj M N) i
        (s * t) (pure A M N W m n)
      rw [map_mul, pure_restrict] at hm
      exact (congrArg
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)).unit.app
          (changeOfRingsPresheaf.{u, u, u} c ((monoidalCategory A).tensorObj M N))).app V)
        hm).symm.trans h

private noncomputable def forwardPairing
    (M N : SheafOfModules.{u} (ringSheaf A)) (W : Cᵒᵖ) :
    M.val.obj W →ₗ[A.obj.obj W] N.val.obj W →ₗ[A.obj.obj W]
      ((restriction c).obj ((monoidalCategory B).tensorObj
        (changeOfRings.{u, u, u} c M) (changeOfRings.{u, u, u} c N))).val.obj W :=
  LinearMap.mk₂ _
    (fun m n ↦ pure B _ _ W (((tensorAdjunction c).unit.app M).val.app W m)
      (((tensorAdjunction c).unit.app N).val.app W n))
    (by
      intro m m' n
      rw [map_add]
      exact (pureBilin B _ _ W).map_add₂ _ _ _)
    (by
      intro r m n
      rw [map_smul]
      change pure B _ _ W ((c.hom.app W r) • _) _ =
        (c.hom.app W r) • pure B _ _ W _ _
      exact (pureBilin B _ _ W).map_smul₂ _ _ _)
    (by
      intro m n n'
      rw [map_add]
      exact ((pureBilin B _ _ W) _).map_add _ _)
    (by
      intro r m n
      rw [map_smul]
      change pure B _ _ W _ ((c.hom.app W r) • _) =
        (c.hom.app W r) • pure B _ _ W _ _
      exact ((pureBilin B _ _ W) _).map_smul _ _)

private theorem forwardPairing_restrict
    (M N : SheafOfModules.{u} (ringSheaf A)) {W V : Cᵒᵖ} (i : W ⟶ V)
    (m : M.val.obj W) (n : N.val.obj W) :
    forwardPairing c M N V (M.val.map i m) (N.val.map i n) =
      ((monoidalCategory B).tensorObj (changeOfRings.{u, u, u} c M)
        (changeOfRings.{u, u, u} c N)).val.map i
        (forwardPairing c M N W m n) := by
  change pure B _ _ V (((tensorAdjunction c).unit.app M).val.app V (M.val.map i m))
      (((tensorAdjunction c).unit.app N).val.app V (N.val.map i n)) =
    ((monoidalCategory B).tensorObj (changeOfRings.{u, u, u} c M)
      (changeOfRings.{u, u, u} c N)).val.map i
      (pure B _ _ W _ _)
  have hm := PresheafOfModules.naturality_apply ((tensorAdjunction c).unit.app M).val i m
  have hn := PresheafOfModules.naturality_apply ((tensorAdjunction c).unit.app N).val i n
  exact (congrArg₂ (pure B _ _ V) hm hn).trans (pure_restrict B _ _ i _ _).symm

private theorem exists_forward
    (M N : SheafOfModules.{u} (ringSheaf A)) :
    ∃ f : changeOfRings.{u, u, u} c ((monoidalCategory A).tensorObj M N) ⟶
        (monoidalCategory B).tensorObj (changeOfRings.{u, u, u} c M) (changeOfRings.{u, u, u} c N),
      ∀ (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W), f.val.app W
        ((tensorUnit c ((monoidalCategory A).tensorObj M N)).hom.app W
          (pure A M N W m n)) =
        pure B _ _ W ((tensorUnit c M).hom.app W m) ((tensorUnit c N).hom.app W n) := by
  let H := (monoidalCategory B).tensorObj (changeOfRings.{u, u, u} c M)
    (changeOfRings.{u, u, u} c N)
  obtain ⟨a, ha, _⟩ := tensor_bilinear_universal A M N ((restriction c).obj H)
    (forwardPairing c M N) (forwardPairing_restrict c M N)
  let f := ((tensorAdjunction c).homEquiv _ H).symm a
  refine ⟨f, ?_⟩
  intro W m n
  have hf := ((tensorAdjunction c).homEquiv _ H).apply_symm_apply a
  have he := tensorAdjunction_underlying c ((monoidalCategory A).tensorObj M N) H f
  change (underlying A).map ((tensorAdjunction c).homEquiv _ H f) =
    tensorUnit c _ ≫ (underlying B).map f at he
  rw [hf] at he
  exact (congrArg (fun k ↦ k.hom.app W (pure A M N W m n)) he).symm.trans (ha W m n)

private theorem exists_backward
    (M N : SheafOfModules.{u} (ringSheaf A)) :
    ∃ f : (monoidalCategory B).tensorObj (changeOfRings.{u, u, u} c M)
        (changeOfRings.{u, u, u} c N) ⟶
        changeOfRings.{u, u, u} c ((monoidalCategory A).tensorObj M N),
      ∀ (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W), f.val.app W
        (pure B _ _ W ((tensorUnit c M).hom.app W m) ((tensorUnit c N).hom.app W n)) =
      (tensorUnit c ((monoidalCategory A).tensorObj M N)).hom.app W (pure A M N W m n) := by
  let E := changeOfRingsPresheaf.{u, u, u} c M
  let F := changeOfRingsPresheaf.{u, u, u} c N
  let H := changeOfRings.{u, u, u} c ((monoidalCategory A).tensorObj M N)
  have : Presheaf.IsLocallyInjective J (𝟙 (ringSheaf B).obj) := inferInstance
  have : Presheaf.IsLocallySurjective J (𝟙 (ringSheaf B).obj) := inferInstance
  obtain ⟨γ, hγ, _⟩ := PresheafOfModules.existsUnique_bilinear_sheafification_extension
    B.obj B (𝟙 (ringSheaf B).obj) E F H (rawPairing c M N) (rawPairing_restrict c M N)
  obtain ⟨f, hf, _⟩ := tensor_bilinear_universal B (changeOfRings.{u, u, u} c M)
    (changeOfRings.{u, u, u} c N) H γ hγ.1
  change ∀ (W : Cᵒᵖ) (m : (changeOfRings.{u, u, u} c M).val.obj W)
    (n : (changeOfRings.{u, u, u} c N).val.obj W),
      f.val.app W (pure B _ _ W m n) = γ W m n at hf
  refine ⟨f, ?_⟩
  intro W m n
  erw [tensorUnit_apply, tensorUnit_apply]
  refine (hf W _ _).trans ((hγ.2 W _ _).trans ?_)
  refine (rawPairing_tmul c M N W 1 1 m n).trans ?_
  rw [one_mul]
  exact (tensorUnit_apply c _ W (pure A M N W m n)).symm

private noncomputable def ins (M : SheafOfModules.{u} (ringSheaf A))
    (W : Cᵒᵖ) (m : M.val.obj W) : (changeOfRings.{u, u, u} c M).val.obj W :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)).unit.app
    (changeOfRingsPresheaf.{u, u, u} c M)).app W
      ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m))
-- Expand the two scalar extensions through the sheafification adjunction.
private theorem scalar_tensor_ext
    (M N : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf B))
    {f g : (monoidalCategory B).tensorObj (changeOfRings.{u, u, u} c M)
      (changeOfRings.{u, u, u} c N) ⟶ H}
    (h : ∀ (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W),
      f.val.app W (pure B _ _ W (ins c M W m) (ins c N W n)) =
      g.val.app W (pure B _ _ W (ins c M W m) (ins c N W n))) : f = g := by
  let := monoidalCategory B
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)
  let S := PresheafOfModules.sheafification (𝟙 (ringSheaf B).obj)
  let E := changeOfRingsPresheaf.{u, u, u} c M
  let F := changeOfRingsPresheaf.{u, u, u} c N
  let ηE := adj.unit.app E
  let ηF := adj.unit.app F
  have hη (G : PresheafOfModules.{u} (ringSheaf B).obj) :
      (J.W.inverseImage (PresheafOfModules.toPresheaf (ringSheaf B).obj)) (adj.unit.app G) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (ringSheaf B).obj)]
    change IsIso (S.map (adj.unit.app G))
    have hc : IsIso (adj.counit.app (S.obj G)) := inferInstance
    have hh : IsIso (S.map (adj.unit.app G) ≫ adj.counit.app (S.obj G)) := by
      have ht := adj.left_triangle_components G
      change S.map (adj.unit.app G) ≫ adj.counit.app (S.obj G) = 𝟙 _ at ht
      rw [ht]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (adj.counit.app (S.obj G))
  have hηη := (J.W.inverseImage (PresheafOfModules.toPresheaf (ringSheaf B).obj)).tensorHom_mem
    ηE ηF (hη E) (hη F)
  have hi : IsIso (S.map (ηE ⊗ₘ ηF)) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (ringSheaf B).obj)] at hηη
    exact hηη
  let q := S.map (ηE ⊗ₘ ηF) ≫ (tensorObjIsoSheafification (S.obj E) (S.obj F)).inv
  have : IsIso q := inferInstance
  apply (cancel_epi q).mp
  apply (adj.homEquiv (E ⊗ F) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro W
  let : CommRing ((ringSheaf B).obj.obj W) := inferInstanceAs (CommRing (B.obj.obj W))
  let a : (E.obj W) ⊗[(ringSheaf B).obj.obj W] (F.obj W) →ₗ[(ringSheaf B).obj.obj W]
      H.val.obj W := ((adj.unit.app (E ⊗ F) ≫
        (forget (ringSheaf B) ⋙ PresheafOfModules.restrictScalars (𝟙 (ringSheaf B).obj)).map
          (q ≫ f)).app W).hom
  let b : (E.obj W) ⊗[(ringSheaf B).obj.obj W] (F.obj W) →ₗ[(ringSheaf B).obj.obj W]
      H.val.obj W := ((adj.unit.app (E ⊗ F) ≫
        (forget (ringSheaf B) ⋙ PresheafOfModules.restrictScalars (𝟙 (ringSheaf B).obj)).map
          (q ≫ g)).app W).hom
  have hh : ModuleCat.ofHom (X := E.obj W)
      (Y := ModuleCat.of ((ringSheaf B).obj.obj W)
        ((F.obj W) →ₗ[(ringSheaf B).obj.obj W] H.val.obj W))
        (TensorProduct.curry a) = ModuleCat.ofHom (X := E.obj W)
        (Y := ModuleCat.of ((ringSheaf B).obj.obj W)
        ((F.obj W) →ₗ[(ringSheaf B).obj.obj W] H.val.obj W))
          (TensorProduct.curry b) := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change TensorProduct.curry a _ = TensorProduct.curry b _
    have hm : ModuleCat.ofHom (X := F.obj W) (Y := H.val.obj W)
        (TensorProduct.curry a ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) =
        ModuleCat.ofHom (X := F.obj W) (Y := H.val.obj W)
          (TensorProduct.curry b ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) := by
      apply ModuleCat.ExtendScalars.hom_ext
      intro n
      have hn := adj.unit.naturality (ηE ⊗ₘ ηF)
      have he := congrArg (fun k ↦ (k.app W)
        (((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m) ⊗ₜ[B.obj.obj W]
          ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n))) hn
      change (adj.unit.app ((S.obj E).val ⊗ (S.obj F).val)).app W
          (ηE.app W ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)
            ⊗ₜ[B.obj.obj W]
            ηF.app W ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n)) =
        (S.map (ηE ⊗ₘ ηF)).val.app W
          ((adj.unit.app (E ⊗ F)).app W
            (((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m) ⊗ₜ[B.obj.obj W]
              ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n))) at he
      change f.val.app W ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv.val.app W
          ((S.map (ηE ⊗ₘ ηF)).val.app W ((adj.unit.app (E ⊗ F)).app W _))) =
        g.val.app W ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv.val.app W
          ((S.map (ηE ⊗ₘ ηF)).val.app W ((adj.unit.app (E ⊗ F)).app W _)))
      exact (congrArg (fun v ↦ f.val.app W
        ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv.val.app W v)) he.symm).trans
          ((h W m n).trans (congrArg (fun v ↦ g.val.app W
            ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv.val.app W v)) he))
    exact congrArg ModuleCat.Hom.hom hm
  exact ModuleCat.hom_ext (TensorProduct.curry_injective (congrArg ModuleCat.Hom.hom hh))

private theorem extendedTensor_hom_ext
    (M N : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf B))
    {f g : changeOfRings.{u, u, u} c ((monoidalCategory A).tensorObj M N) ⟶ H}
    (h : ∀ (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W),
      f.val.app W ((tensorUnit c ((monoidalCategory A).tensorObj M N)).hom.app W
        (pure A M N W m n)) =
      g.val.app W ((tensorUnit c ((monoidalCategory A).tensorObj M N)).hom.app W
        (pure A M N W m n))) : f = g := by
  apply ((tensorAdjunction c).homEquiv _ H).injective
  apply pure_hom_ext A M N ((restriction c).obj H)
  intro W m n
  have hf := tensorAdjunction_underlying c ((monoidalCategory A).tensorObj M N) H f
  have hg := tensorAdjunction_underlying c ((monoidalCategory A).tensorObj M N) H g
  exact (congrArg (fun k ↦ k.hom.app W (pure A M N W m n)) hf).trans
    ((h W m n).trans (congrArg (fun k ↦ k.hom.app W (pure A M N W m n)) hg).symm)

/-- Scalar extension preserves the sheaf tensor product and its normalized pairing.
Source: Stacks Project, Modules on Sites, Tag 03EL, first and last equalities;
Tag 0GMW for descent through module sheafification.
(auxiliary; not a blueprint node).

Proof: Extend the bilinear pairing of the two scalar-extension units to obtain the
forward map. For the inverse use the sectionwise formula
(s tensor m) tensor (t tensor n) mapped to st tensor (m tensor n), and extend this
bilinear map through both sheafifications. The tensor universal property supplies
the inverse map. Both composites are identities on the generating original pure
tensors; uniqueness of bilinear extension and of sheafification proves the identities.
The same generators establish simultaneous naturality. The formula holds by construction.
No flatness or nonzero-ring hypothesis is used. -/
theorem exists_scalarTensorComparison :
    ∃ e : ∀ M N : SheafOfModules.{u} (ringSheaf A),
        changeOfRings.{u, u, u} c ((monoidalCategory A).tensorObj M N) ≅
          (monoidalCategory B).tensorObj (changeOfRings.{u, u, u} c M)
            (changeOfRings.{u, u, u} c N),
      (∀ {M M' N N' : SheafOfModules.{u} (ringSheaf A)} (f : M ⟶ M') (g : N ⟶ N'),
        (tensorFunctor c).map ((monoidalCategory A).tensorHom f g) ≫ (e M' N').hom =
          (e M N).hom ≫ (monoidalCategory B).tensorHom
            ((tensorFunctor c).map f) ((tensorFunctor c).map g)) ∧
      ∀ M N W m n, (e M N).hom.val.app W
        ((tensorUnit c ((monoidalCategory A).tensorObj M N)).hom.app W
          (pure A M N W m n)) =
        pure B _ _ W ((tensorUnit c M).hom.app W m) ((tensorUnit c N).hom.app W n) := by
  classical
  have hs M N : ∃ e : changeOfRings.{u, u, u} c ((monoidalCategory A).tensorObj M N) ≅
      (monoidalCategory B).tensorObj (changeOfRings.{u, u, u} c M)
        (changeOfRings.{u, u, u} c N),
      ∀ (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W), e.hom.val.app W
        ((tensorUnit c ((monoidalCategory A).tensorObj M N)).hom.app W
          (pure A M N W m n)) =
        pure B _ _ W ((tensorUnit c M).hom.app W m) ((tensorUnit c N).hom.app W n) := by
    obtain ⟨f, hf⟩ := exists_forward c M N
    obtain ⟨g, hg⟩ := exists_backward c M N
    refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
    · apply extendedTensor_hom_ext c M N
      intro W m n
      change g.val.app W (f.val.app W _) = _
      exact (congrArg (g.val.app W) (hf W m n)).trans (hg W m n)
    · apply scalar_tensor_ext c M N
      intro W m n
      change f.val.app W (g.val.app W _) = _
      have hm := tensorUnit_apply c M W m
      have hn := tensorUnit_apply c N W n
      change (tensorUnit c M).hom.app W m = ins c M W m at hm
      change (tensorUnit c N).hom.app W n = ins c N W n at hn
      rw [← hm, ← hn]
      exact (congrArg (f.val.app W) (hg W m n)).trans (hf W m n)
  choose e he using hs
  refine ⟨e, ?_, he⟩
  intro M M' N N' f g
  apply extendedTensor_hom_ext c M N
  intro W m n
  have hu (P Q : SheafOfModules.{u} (ringSheaf A)) (a : P ⟶ Q) (x : P.val.obj W) :
      ((tensorFunctor c).map a).val.app W ((tensorUnit c P).hom.app W x) =
        (tensorUnit c Q).hom.app W (a.val.app W x) := by
    exact (congrArg (fun k ↦ k.val.app W x) ((tensorAdjunction c).unit.naturality a)).symm
  change (e M' N').hom.val.app W
      (((tensorFunctor c).map ((monoidalCategory A).tensorHom f g)).val.app W _) =
    ((monoidalCategory B).tensorHom ((tensorFunctor c).map f)
      ((tensorFunctor c).map g)).val.app W ((e M N).hom.val.app W _)
  rw [hu, pure_map, he, he, pure_map, hu, hu]

end SheafOfModules.RingedTensor

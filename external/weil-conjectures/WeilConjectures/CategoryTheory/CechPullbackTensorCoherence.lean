/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
/-!
# Tensor coherence for a Cech pullback functor

Source: Stacks Project, sites-modules.tex, Tag 03EL.
(blueprint: lem-weil-pbc-cech-pullback-tensor-coherence).

The tensor comparison and its unit compatibility are isolated here so that the
ordinary-complex assembly can use them as a single piece of data. The tensor
products are the canonical ones, `SheafOfModules.monoidalCategory`, which are
the tensor products of `ringedExtendedCech`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory

/-- A natural tensor comparison `F (X ⊗ Y) ≅ F X ⊗ F Y` together with identifications of
`U`, `V` with the tensor units under which `u` is compatible with the comparison at the
unit and the left unitor. -/
structure TensorCoherence {A : Type u} {B : Type v} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B]
    (F : A ⥤ B) (U : A) (V : B) (u : F.obj U ≅ V) where
  tensor : ∀ X Y, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y
  naturality : ∀ {X X' Y Y'} (f : X ⟶ X') (g : Y ⟶ Y'),
    F.map (f ⊗ₘ g) ≫ (tensor X' Y').hom =
      (tensor X Y).hom ≫ (F.map f ⊗ₘ F.map g)
  unitA : U ≅ 𝟙_ A
  unitB : V ≅ 𝟙_ B
  unit : (tensor (𝟙_ A) (𝟙_ A)).hom ≫
      ((F.map unitA.inv ≫ u.hom ≫ unitB.hom) ⊗ₘ
        (F.map unitA.inv ≫ u.hom ≫ unitB.hom)) ≫
      (λ_ (𝟙_ B)).hom =
    F.map (λ_ (𝟙_ A)).hom ≫ F.map unitA.inv ≫ u.hom ≫ unitB.hom

private theorem tensor_unit_end
    {B : Type v} [Category B] [MonoidalCategory B]
    (a b : 𝟙_ B ⟶ 𝟙_ B) :
    (a ⊗ₘ b) ≫ (λ_ (𝟙_ B)).hom = (λ_ (𝟙_ B)).hom ≫ a ≫ b := by
  simp only [tensorHom_def, id_whiskerLeft, whiskerRight_id, ← unitors_equal, ← unitors_inv_equal,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem tensorCoherence_of_comparison
    {A : Type u} {B : Type v} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B]
    (F : A ⥤ B)
    (t : ∀ X Y, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (ht : ∀ {X X' Y Y'} (f : X ⟶ X') (g : Y ⟶ Y'),
      F.map (f ⊗ₘ g) ≫ (t X' Y').hom =
        (t X Y).hom ≫ (F.map f ⊗ₘ F.map g))
    (v : F.obj (𝟙_ A) ≅ 𝟙_ B) :
    Nonempty (TensorCoherence F (𝟙_ A) (𝟙_ B) v) := by
  -- Normalize through the target unit identification, which the structure lets us choose.
  let w : F.obj (𝟙_ A) ≅ 𝟙_ B :=
    (F.mapIso (λ_ (𝟙_ A))).symm ≪≫ t (𝟙_ A) (𝟙_ A) ≪≫
      tensorIso v v ≪≫ λ_ (𝟙_ B)
  let a : 𝟙_ B ≅ 𝟙_ B := v.symm ≪≫ w
  have hw : (t (𝟙_ A) (𝟙_ A)).hom ≫ (v.hom ⊗ₘ v.hom) ≫
      (λ_ (𝟙_ B)).hom = F.map (λ_ (𝟙_ A)).hom ≫ w.hom := by
    simp only [w, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, tensorIso_hom,
      ← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]
  have ha : w.hom ≫ a.inv = v.hom := by
    simp only [a, Iso.trans_inv, Iso.symm_inv, Iso.hom_inv_id_assoc]
  refine ⟨⟨t, ht, Iso.refl _, a.symm, ?_⟩⟩
  simp only [Iso.refl_inv, F.map_id, Category.id_comp, Iso.symm_hom]
  rw [← tensorHom_comp_tensorHom, Category.assoc, tensor_unit_end]
  simp only [← Category.assoc] at hw ⊢
  rw [hw]
  simp only [Category.assoc, ha]

/--
For the canonical tensor products of sheaves of modules, the supplied left adjoint `F` of
`h.modules` carries a tensor comparison normalized at `v`.

Proof. By uniqueness of left adjoints, `F` is isomorphic to the module pullback along `h`,
which preserves tensor products (Stacks 03EL; lem-weil-pbc-ringed-topoi-module-pullback-tensor);
transporting that comparison through the isomorphism gives `tensor`, natural in both variables.
Take `unitA`, `unitB` the identities (`SheafOfModules.unit` is the tensor unit). The canonical
comparison satisfies the unit equation with the canonical unit comparison `v0`; `v = v0 ≫ a`
for an automorphism `a` of the target unit, i.e. a unit global section acting centrally, and
multiplying the tensor comparison by `a⁻¹` keeps it natural and turns the unit equation for
`v0` into the one for `v`.
(blueprint: lem-weil-pbc-cech-pullback-tensor-coherence)
-/
theorem cech_pullback_tensor_coherence
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (h : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (F : ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    [F.PreservesZeroMorphisms] (hF : F ⊣ h.modules)
    (v : F.obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≅
      SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)) :
    Nonempty (@TensorCoherence _ _ _ _
      (SheafOfModules.monoidalCategory R) (SheafOfModules.monoidalCategory S) F
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)) v) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := h.leftExact
  obtain ⟨RI, ⟨I⟩⟩ := algebraic_image J K h.inverse h.direct h.adj R
  obtain ⟨c, hc⟩ := structural_map K J S R h RI I
  let G := I.modules ⋙ SheafOfModules.tensorFunctor c
  obtain ⟨hG⟩ : Nonempty (G ⊣ h.modules) := supplied_adjunction h RI I c hc
  have hobj : ∀ M, G.obj M = SheafOfModules.changeOfRings c (I.modules.obj M) :=
    fun _ ↦ rfl
  have hmap : ∀ {M N} (f : M ⟶ N), G.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm := by
    intro M N f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨k⟩ := SheafOfModules.canonicalRingedTensorComparison_nonempty
    R S RI h.inverse I c G hobj h.direct h.adj hmap
  let e := Adjunction.leftAdjointUniq hF hG
  let kg : tensor _ ⋙ G ≅ G.prod G ⋙ tensor _ :=
    NatIso.ofComponents (fun MN ↦ k.mu MN.1 MN.2) (fun f ↦ k.naturality f.1 f.2)
  let tf : tensor _ ⋙ F ≅ F.prod F ⋙ tensor _ :=
    Functor.isoWhiskerLeft (tensor _) e ≪≫ kg ≪≫
      (Functor.isoWhiskerRight (NatIso.prod e e) (tensor _)).symm
  exact tensorCoherence_of_comparison F (fun X Y ↦ tf.app (X, Y))
    (fun f g ↦ tf.hom.naturality (show (_, _) ⟶ (_, _) from (f, g))) v

end CategoryTheory

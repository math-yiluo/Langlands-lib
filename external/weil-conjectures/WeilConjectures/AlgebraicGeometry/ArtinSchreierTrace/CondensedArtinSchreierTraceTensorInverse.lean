/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier

import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierTraceTensorAdd
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierProjectorFacts
import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientLinear

/-! # Tensor inverse and inverse character of condensed Artin–Schreier sheaves

Source: latest blueprint, sec-fourier-transform/sk-lem-as-properties,
lemma-artin-schreier-character-sheaf, proof Step 5, tensor inverse (blueprint:
lem-fd-as-trace-tensor-inverse).

Stated for any condensed coefficient ring in which `q = #k` is a unit and any nontrivial
character of `k`; the Qbar trace-character case gives the inverse clauses of
`qlbar_artinSchreier_trace_tensor_properties`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.ProEtale

attribute [local irreducible] ProEtale.CondensedRing.upperStar
  ProEtale.CondensedRing.upperStarComp
  ProEtale.CondensedRing.lowerStarComp ProEtale.CondensedRing.upperStarLowerStarAdjunction

namespace AlgebraicGeometry.ArtinSchreierTrace
open ProEtale ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private abbrev reg (X : Scheme.{u}) := Mod.regular (condensedRingObj Λ X)
private def unitPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    reg Λ Y ⟶ (CondensedRing.lowerStar Λ f).obj (reg Λ X) :=
  (CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).inv

private theorem unitPush_hom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (unitPush Λ f).hom = condensedPushforwardHom Λ f :=
  CondensedRing.homEquiv_εIso_inv_hom Λ f

private theorem unitPush_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    unitPush Λ (f ≫ g) = unitPush Λ g ≫
      (CondensedRing.lowerStar Λ g).map (unitPush Λ f) ≫
        (CondensedRing.lowerStarComp Λ f g).hom.app (reg Λ X) := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', lowerStar_map_hom,
    lowerStarComp_hom_app_hom, unitPush_hom]
  exact condensedPushforwardHom_comp Λ f g

private def mapOver {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
    (t : Z ⟶ Y) (h : t ≫ f = g) :
    (CondensedRing.lowerStar Λ f).obj (reg Λ Y) ⟶
      (CondensedRing.lowerStar Λ g).obj (reg Λ Z) :=
  (CondensedRing.lowerStar Λ f).map (unitPush Λ t) ≫
    (CondensedRing.lowerStarComp Λ t f).hom.app (reg Λ Z) ≫
      (CondensedRing.lowerStarCongr Λ h).hom.app (reg Λ Z)

omit [IsCommMonObj Λ] in
private theorem lowerStarCongr_app {X Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g) :
    (CondensedRing.lowerStarCongr Λ h).hom.app (reg Λ Y) =
      eqToHom (congrArg (fun t ↦ (CondensedRing.lowerStar Λ t).obj (reg Λ Y)) h) := by
  cases h
  rfl

private theorem unitPush_id (Y : Scheme.{u}) :
    unitPush Λ (𝟙 Y) = (CondensedRing.lowerStarId Λ Y).inv.app (reg Λ Y) := by
  apply Mod.hom_ext
  rw [unitPush_hom, condensedPushforwardHom_id]
  have h := congrArg Mod.Hom.hom
    ((CondensedRing.lowerStarId Λ Y).hom_inv_id_app (reg Λ Y))
  simp only [Mod.comp_hom', lowerStarId_hom_app_hom, Mod.id_hom'] at h
  rw [← cancel_epi ((ProEtale.lowerStarId Ab.{u + 1} Y).hom.app (condensedRingObj Λ Y)),
    Iso.hom_inv_id_app]
  exact h.symm

private theorem mapOver_id {X Y : Scheme.{u}} (f : Y ⟶ X) :
    mapOver Λ f f (𝟙 Y) (Category.id_comp f) = 𝟙 _ := by
  rw [mapOver, unitPush_id, CondensedRing.lowerStarComp_id_left]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.id_obj,
    Iso.symm_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  simp

private theorem mapOver_congr {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
    {t s : Z ⟶ Y} (h : t = s) (ht : t ≫ f = g) (hs : s ≫ f = g) :
    mapOver Λ f g t ht = mapOver Λ f g s hs := by
  subst s
  rfl

private theorem mapOver_comp {X Y Z W : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ X) (j : W ⟶ X)
    (t : Z ⟶ Y) (s : W ⟶ Z) (h : t ≫ f = g) (hs : s ≫ g = j) :
    mapOver Λ f j (s ≫ t) (by rw [Category.assoc, h, hs]) =
      mapOver Λ f g t h ≫ mapOver Λ g j s hs := by
  subst g
  subst j
  unfold mapOver
  rw [unitPush_comp]
  simp only [Functor.map_comp, Category.assoc]
  have hc := congrArg (fun e ↦ e.hom.app (reg Λ W))
    (lowerStarComp_assoc Λ s t f)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Category.id_comp, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] at hc
  simp only [CondensedRing.lowerStarCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id, Category.id_comp] at hc ⊢
  erw [← hc]
  rw [← NatTrans.naturality_assoc]
  rfl

private def mapOverIso {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
    (t : Z ⟶ Y) [IsIso t] (h : t ≫ f = g) :
    (CondensedRing.lowerStar Λ f).obj (reg Λ Y) ≅
      (CondensedRing.lowerStar Λ g).obj (reg Λ Z) where
  hom := mapOver Λ f g t h
  inv := mapOver Λ g f (inv t) (by rw [← h, ← Category.assoc, IsIso.inv_hom_id,
    Category.id_comp])
  hom_inv_id := by
    rw [← mapOver_comp]
    exact (mapOver_congr Λ _ _ (IsIso.inv_hom_id t) _ _).trans (mapOver_id Λ f)
  inv_hom_id := by
    rw [← mapOver_comp]
    exact (mapOver_congr Λ _ _ (IsIso.hom_inv_id t) _ _).trans (mapOver_id Λ g)

private theorem mapOver_push {X X' Y Z : Scheme.{u}} (n : X ⟶ X')
    (f : Y ⟶ X) (g : Z ⟶ X) (t : Z ⟶ Y) (h : t ≫ f = g) :
    (CondensedRing.lowerStar Λ n).map (mapOver Λ f g t h) ≫
        (CondensedRing.lowerStarComp Λ g n).hom.app (reg Λ Z) =
      (CondensedRing.lowerStarComp Λ f n).hom.app (reg Λ Y) ≫
        mapOver Λ (f ≫ n) (g ≫ n) t (by rw [← Category.assoc, h]) := by
  subst g
  unfold mapOver
  simp only [CondensedRing.lowerStarCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id, Functor.map_comp, Category.assoc]
  have hc := congrArg (fun e ↦ e.hom.app (reg Λ Z))
    (lowerStarComp_assoc Λ t f n)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Category.id_comp, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] at hc
  simp only [CondensedRing.lowerStarCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id] at hc
  erw [← hc, ← NatTrans.naturality_assoc]
  rfl

end AlgebraicGeometry.ArtinSchreierTrace

namespace AlgebraicGeometry.ArtinSchreierTrace

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private abbrev modules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

private abbrev scalars (X : Scheme.{u}) : MonObj.Γ Λ →+* MonObj.Γ (condensedRingObj Λ X) :=
  ProEtale.CondensedRing.constRingHom Λ (RingHom.id _) X

/-- The `ΓΛ`-linear structure on modules induced by the constant global sections. -/
private abbrev linearModules (X : Scheme.{u}) : Linear (MonObj.Γ Λ) (modules Λ X) :=
  ProEtale.CondensedRing.modLinear Λ (RingHom.id _) X

attribute [local instance] linearModules

/-- Module pushforward is `ΓΛ`-linear. -/
private theorem linearLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.lowerStar Λ f).Linear (MonObj.Γ Λ) :=
  ProEtale.CondensedRing.linear_lowerStar Λ (RingHom.id _) f

attribute [local instance] linearLowerStar

/-- Module pullback is `ΓΛ`-linear, being left adjoint to a linear functor. -/
private theorem linearUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ f).Linear (MonObj.Γ Λ) :=
  (CondensedRing.upperStarLowerStarAdjunction _ f).left_adjoint_linear

attribute [local instance] linearUpperStar

private theorem scalarEnd (X : Scheme.{u}) (a : MonObj.Γ Λ) :
    (Mod.regularEndRingHom (MonObj.Γ.mapFunctorMonoidHom (upperStarFromPoint X) a)).asHom =
      a • 𝟙 (Mod.regular (condensedRingObj Λ X)) := by
  rw [Mod.linearOfRingHom_smul_id (scalars Λ X)]
  apply Mod.hom_ext
  change (ρ_ _).inv ≫ _ ◁ (scalars Λ X a).hom ≫ MonObj.mul =
    (λ_ _).inv ≫ (scalars Λ X a).hom ▷ _ ≫ MonObj.mul
  exact Mod.rightUnitor_inv_whiskerLeft_mul_eq
    (S := condensedRingObj Λ X) (scalars Λ X a).hom

private theorem pullback_regular_of_factor
    {S A X : Scheme.{u}} (π : X ⟶ S) (z : S ⟶ A) (g : X ⟶ A)
    (h : g = π ≫ z) (M : modules Λ A)
    (e : (CondensedRing.upperStar Λ z).obj M ≅
      Mod.regular (condensedRingObj Λ S)) :
    Nonempty ((CondensedRing.upperStar Λ g).obj M ≅
      Mod.regular (condensedRingObj Λ X)) := by
  exact ⟨(CondensedRing.upperStarCongr Λ h).app M ≪≫
    (CondensedRing.upperStarComp Λ π z).app M ≪≫
      (CondensedRing.upperStar Λ π).mapIso e ≪≫
        (Functor.Monoidal.εIso (CondensedRing.upperStar Λ π)).symm⟩

private theorem pullback_along_composite
    {A X : Scheme.{u}} (n : A ⟶ A) (g g' : X ⟶ A) (h : g ≫ n = g')
    (M M' : modules Λ A) (e : (CondensedRing.upperStar Λ n).obj M ≅ M') :
    Nonempty ((CondensedRing.upperStar Λ g).obj M' ≅
      (CondensedRing.upperStar Λ g').obj M) := by
  exact ⟨(CondensedRing.upperStar Λ g).mapIso e.symm ≪≫
    (CondensedRing.upperStarComp Λ g n).symm.app M ≪≫
      (CondensedRing.upperStarCongr Λ h).app M⟩

variable (k : Type u) [Field k] [Fintype k]
local notation "A" => 𝔸(PUnit; Spec (CommRingCat.of k))
local notation "AS" => AffineSpace.artinSchreierMap PUnit (Spec (CommRingCat.of k)) (Fintype.card k)
local notation "N" => AffineSpace.neg PUnit (Spec (CommRingCat.of k))

private theorem projector_linear (ψ : AddChar k (MonObj.Γ Λ)) :
    condensedArtinSchreierProjector Λ k ψ =
      ∑ a : k, (Ring.inverse (Fintype.card k : MonObj.Γ Λ) * ψ (-a)) •
        condensedArtinSchreierTranslationAction Λ k a := by
  unfold condensedArtinSchreierProjector
  apply Finset.sum_congr rfl
  intro a _
  apply End.ext
  simp only [End.smul_asHom]
  rw [scalarEnd, CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id,
    Linear.comp_smul]
  change (Ring.inverse (Fintype.card k : MonObj.Γ Λ) * ψ (-a)) •
    ((condensedArtinSchreierTranslationAction Λ k a).asHom ≫
      𝟙 (condensedArtinSchreierPushforward Λ k)) = _
  rw [Category.comp_id]

private theorem neg_intertwine_image
    (ψ : AddChar k (MonObj.Γ Λ))
    (e : (CondensedRing.upperStar Λ N).obj (condensedArtinSchreierPushforward Λ k) ≅
      condensedArtinSchreierPushforward Λ k)
    (h : (CondensedRing.upperStar Λ N).map (condensedArtinSchreierProjector Λ k ψ).asHom ≫
        e.hom =
      e.hom ≫ (condensedArtinSchreierProjector Λ k ψ⁻¹).asHom) :
    Nonempty ((CondensedRing.upperStar Λ N).obj (condensedArtinSchreierSheaf Λ k ψ) ≅
      condensedArtinSchreierSheaf Λ k ψ⁻¹) := by
  let F := CondensedRing.upperStar Λ N
  let p := (condensedArtinSchreierProjector Λ k ψ).asHom
  let q := (condensedArtinSchreierProjector Λ k ψ⁻¹).asHom
  refine ⟨(PreservesImage.iso F p).symm ≪≫
    image.compIso (F.map p) e.hom ≪≫ image.eqToIso h ≪≫ ?_⟩
  exact asIso (image.preComp e.hom q)

private theorem neg_projector_conjugate
    (ψ : AddChar k (MonObj.Γ Λ))
    (e : (CondensedRing.upperStar Λ N).obj (condensedArtinSchreierPushforward Λ k) ≅
      condensedArtinSchreierPushforward Λ k)
    (h : ∀ a : k,
      (CondensedRing.upperStar Λ N).map (condensedArtinSchreierTranslationAction Λ k a).asHom ≫
          e.hom =
        e.hom ≫
          (condensedArtinSchreierTranslationAction Λ k (-a)).asHom) :
    (CondensedRing.upperStar Λ N).map (condensedArtinSchreierProjector Λ k ψ).asHom ≫
        e.hom =
      e.hom ≫ (condensedArtinSchreierProjector Λ k ψ⁻¹).asHom := by
  simp only [projector_linear, End.sum_asHom, End.smul_asHom]
  calc
    _ = ∑ a : k, (Ring.inverse (Fintype.card k : MonObj.Γ Λ) * ψ (-a)) •
        (e.hom ≫ (condensedArtinSchreierTranslationAction Λ k (-a)).asHom) := by
      rw [CategoryTheory.Functor.map_sum, Preadditive.sum_comp]
      apply Finset.sum_congr rfl
      intro a _
      rw [CategoryTheory.Functor.map_smul (R := MonObj.Γ Λ), Linear.smul_comp, h]
    _ = ∑ a : k, (Ring.inverse (Fintype.card k : MonObj.Γ Λ) * ψ⁻¹ (-a)) •
        (e.hom ≫ (condensedArtinSchreierTranslationAction Λ k a).asHom) := by
      refine Fintype.sum_equiv (Equiv.neg k)
        (fun a : k ↦ (Ring.inverse (Fintype.card k : MonObj.Γ Λ) * ψ (-a)) •
          (e.hom ≫ (condensedArtinSchreierTranslationAction Λ k (-a)).asHom))
        (fun a : k ↦ (Ring.inverse (Fintype.card k : MonObj.Γ Λ) * ψ⁻¹ (-a)) •
          (e.hom ≫ (condensedArtinSchreierTranslationAction Λ k a).asHom)) ?_
      intro a
      simp only [Equiv.neg_apply, AddChar.inv_apply, neg_neg]
    _ = _ := by
      erw [Preadditive.comp_sum]
      apply Finset.sum_congr rfl
      intro a _
      exact (Linear.comp_smul _ _ _ e.hom
        (Ring.inverse (Fintype.card k : MonObj.Γ Λ) * ψ⁻¹ (-a))
        (condensedArtinSchreierTranslationAction Λ k a).asHom).symm

private theorem zero_transport
    (ψ : AddChar k (MonObj.Γ Λ))
    (e : (CondensedRing.upperStar Λ (AffineSpace.zeroSection PUnit (Spec (CommRingCat.of k)))).obj
        (condensedArtinSchreierSheaf Λ k ψ) ≅
      Mod.regular (condensedRingObj Λ (Spec (CommRingCat.of k))))
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] :
    Nonempty (condensedArtinSchreierSheafOf Λ k X ψ 0 ≅
      Mod.regular (condensedRingObj Λ X)) := by
  let π := X ↘ Spec (CommRingCat.of k)
  have hz : AffineSpace.homOfVector π (fun _ : PUnit ↦ (0 : Γ(X, ⊤))) =
      π ≫ AffineSpace.zeroSection PUnit (Spec (CommRingCat.of k)) := by
    rw [AffineSpace.zeroSection, AffineSpace.comp_homOfVector, Category.comp_id]
    congr 1
    ext
    simp
  exact pullback_regular_of_factor Λ π
    (AffineSpace.zeroSection PUnit (Spec (CommRingCat.of k)))
    (AffineSpace.homOfVector π (fun _ : PUnit ↦ (0 : Γ(X, ⊤)))) hz
    (condensedArtinSchreierSheaf Λ k ψ) e

private theorem neg_transport
    (ψ : AddChar k (MonObj.Γ Λ))
    (e : (CondensedRing.upperStar Λ N).obj (condensedArtinSchreierSheaf Λ k ψ) ≅
      condensedArtinSchreierSheaf Λ k ψ⁻¹)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] (f : Γ(X, ⊤)) :
    Nonempty (condensedArtinSchreierSheafOf Λ k X ψ⁻¹ f ≅
      condensedArtinSchreierSheafOf Λ k X ψ (-f)) := by
  let g := AffineSpace.homOfVector (X ↘ Spec (CommRingCat.of k)) (fun _ : PUnit ↦ f)
  have hn : g ≫ N =
      AffineSpace.homOfVector (X ↘ Spec (CommRingCat.of k)) (fun _ : PUnit ↦ -f) := by
    refine AffineSpace.hom_ext (by simp [g]) fun _ ↦ ?_
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.neg_appTop_coord, map_neg, AffineSpace.homOfVector_appTop_coord, g]
  exact pullback_along_composite Λ N g
    (AffineSpace.homOfVector (X ↘ Spec (CommRingCat.of k)) (fun _ : PUnit ↦ -f)) hn
    (condensedArtinSchreierSheaf Λ k ψ) (condensedArtinSchreierSheaf Λ k ψ⁻¹) e

end AlgebraicGeometry.ArtinSchreierTrace

namespace AlgebraicGeometry.ArtinSchreierTrace
open ProEtale ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
variable (k : Type u) [Field k] [Fintype k]
local notation "A" => 𝔸(PUnit; Spec (CommRingCat.of k))
local notation "AS" => AffineSpace.artinSchreierMap PUnit (Spec (CommRingCat.of k)) (Fintype.card k)
local notation "N" => AffineSpace.neg PUnit (Spec (CommRingCat.of k))

private theorem reflection_commutes : N ≫ AS = AS ≫ N := by
  simpa only [Etale.artinSchreierScaling, map_neg, map_one, AffineSpace.smul_neg_one] using
    (Etale.artinSchreierScaling_comp_artinSchreierMap (k := k) (-1))

private theorem reflection_square : N ≫ AS ≫ N = AS := by
  rw [← Category.assoc, reflection_commutes, Category.assoc,
    AffineSpace.neg_comp_neg, Category.comp_id]

private def reflection_pull_push :
    CondensedRing.upperStar Λ N ≅ CondensedRing.lowerStar Λ N := by
  let c : CondensedRing.upperStar Λ N ⋙ CondensedRing.upperStar Λ N ≅ 𝟭 _ :=
    (CondensedRing.upperStarComp Λ N N).symm ≪≫
      upperStarCongr Λ (AffineSpace.neg_comp_neg PUnit (Spec (CommRingCat.of k))) ≪≫
        CondensedRing.upperStarId Λ A
  let E := CategoryTheory.Equivalence.mk
    (CondensedRing.upperStar Λ N) (CondensedRing.upperStar Λ N) c.symm c
  exact Adjunction.rightAdjointUniq E.toAdjunction
    (CondensedRing.upperStarLowerStarAdjunction Λ N)

private def reflection_push_iso :
    (CondensedRing.lowerStar Λ N).obj (condensedArtinSchreierPushforward Λ k) ≅
      condensedArtinSchreierPushforward Λ k := by
  have : IsIso N := ⟨N, AffineSpace.neg_comp_neg _ _, AffineSpace.neg_comp_neg _ _⟩
  exact (CondensedRing.lowerStarComp Λ AS N).app (reg Λ A) ≪≫
    mapOverIso Λ (AS ≫ N) AS N (reflection_square k)

private theorem action_mapOver (a : k) :
    (condensedArtinSchreierTranslationAction Λ k a).asHom = mapOver Λ AS AS
      (Etale.artinSchreierTranslation k a)
      (Etale.artinSchreierTranslation_comp_artinSchreierMap k a) := by
  unfold condensedArtinSchreierTranslationAction mapOver unitPush
  rw [lowerStarCongr_app]
  rfl

private theorem reflection_conjugates (a : k) :
    (CondensedRing.lowerStar Λ N).map (condensedArtinSchreierTranslationAction Λ k a).asHom ≫
        (reflection_push_iso Λ k).hom =
      (reflection_push_iso Λ k).hom ≫ (condensedArtinSchreierTranslationAction Λ k (-a)).asHom := by
  let t := Etale.artinSchreierTranslation k a
  let t' := Etale.artinSchreierTranslation k (-a)
  have ht := Etale.artinSchreierTranslation_comp_artinSchreierMap k a
  have ht' := Etale.artinSchreierTranslation_comp_artinSchreierMap k (-a)
  have hw : t ≫ (AS ≫ N) = AS ≫ N := by
    rw [← Category.assoc, ht]
  have hg : N ≫ t = t' ≫ N := by
    simpa only [Etale.artinSchreierScaling, map_neg, map_one, AffineSpace.smul_neg_one,
      neg_mul, one_mul, neg_neg] using
      (Etale.artinSchreierTranslation_comp_artinSchreierScaling (k := k) (-a) (-1)).symm
  let m := mapOver Λ (AS ≫ N) AS N (reflection_square k)
  let c := (CondensedRing.lowerStarComp Λ AS N).app (reg Λ A)
  have hm : mapOver Λ (AS ≫ N) (AS ≫ N) t hw ≫ m =
      m ≫ mapOver Λ AS AS t' ht' := by
    rw [← mapOver_comp, ← mapOver_comp]
    exact mapOver_congr Λ _ _ hg _ _
  have hp := mapOver_push Λ N AS AS t ht
  simp only [action_mapOver]
  change (CondensedRing.lowerStar Λ N).map (mapOver Λ AS AS t ht) ≫
      (c.hom ≫ m) = (c.hom ≫ m) ≫ mapOver Λ AS AS t' ht'
  calc
    _ = ((CondensedRing.lowerStar Λ N).map (mapOver Λ AS AS t ht) ≫ c.hom) ≫ m :=
      (Category.assoc _ _ _).symm
    _ = (c.hom ≫ mapOver Λ (AS ≫ N) (AS ≫ N) t hw) ≫ m :=
      congrArg (fun z ↦ z ≫ m) hp
    _ = c.hom ≫ (mapOver Λ (AS ≫ N) (AS ≫ N) t hw ≫ m) := Category.assoc _ _ _
    _ = c.hom ≫ (m ≫ mapOver Λ AS AS t' ht') := congrArg (fun z ↦ c.hom ≫ z) hm
    _ = _ := (Category.assoc _ _ _).symm

private def reflection_total_iso :
    (CondensedRing.upperStar Λ N).obj (condensedArtinSchreierPushforward Λ k) ≅
      condensedArtinSchreierPushforward Λ k :=
  (reflection_pull_push Λ k).app _ ≪≫ reflection_push_iso Λ k

private theorem reflection_total_conjugates (a : k) :
    (CondensedRing.upperStar Λ N).map (condensedArtinSchreierTranslationAction Λ k a).asHom ≫
        (reflection_total_iso Λ k).hom =
      (reflection_total_iso Λ k).hom ≫
        (condensedArtinSchreierTranslationAction Λ k (-a)).asHom := by
  change _ ≫ (reflection_pull_push Λ k).hom.app _ ≫ (reflection_push_iso Λ k).hom = _
  rw [NatTrans.naturality_assoc, reflection_conjugates]
  simp [reflection_total_iso]

end AlgebraicGeometry.ArtinSchreierTrace

namespace AlgebraicGeometry.ArtinSchreierTrace
open ProEtale ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]
local notation "A" => 𝔸(PUnit; Spec (CommRingCat.of k))
local notation "AS" => AffineSpace.artinSchreierMap PUnit (Spec (CommRingCat.of k)) (Fintype.card k)
attribute [local instance] linearModules linearLowerStar linearUpperStar

private theorem cover_trivialization
    (ψ : AddChar k (MonObj.Γ Λ)) (hq : IsUnit (Fintype.card k : MonObj.Γ Λ)) :
    Nonempty ((CondensedRing.upperStar Λ AS).obj (condensedArtinSchreierSheaf Λ k ψ) ≅
      Mod.regular (condensedRingObj Λ A)) := by
  let := hq.invertible
  have := condensedArtinSchreierProjector_evaluation Λ k ψ
  exact ⟨asIso ((CondensedRing.upperStar Λ AS).map
    (image.ι (condensedArtinSchreierProjector Λ k ψ).asHom) ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ AS).counit.app
        (Mod.regular (condensedRingObj Λ A)))⟩

private theorem origin_trivialization
    (ψ : AddChar k (MonObj.Γ Λ)) (hq : IsUnit (Fintype.card k : MonObj.Γ Λ)) :
    Nonempty ((CondensedRing.upperStar Λ (AffineSpace.zeroSection PUnit
      (Spec (CommRingCat.of k)))).obj (condensedArtinSchreierSheaf Λ k ψ) ≅
        Mod.regular (condensedRingObj Λ (Spec (CommRingCat.of k)))) := by
  obtain ⟨e⟩ := cover_trivialization Λ k ψ hq
  let z := AffineSpace.zeroSection PUnit (Spec (CommRingCat.of k))
  exact pullback_regular_of_factor Λ z AS z
    (Etale.zeroSection_comp_artinSchreierMap (k := k)).symm
    (condensedArtinSchreierSheaf Λ k ψ) e

end AlgebraicGeometry.ArtinSchreierTrace

namespace AlgebraicGeometry.ArtinSchreierTrace

/-- `L_{ψ,f} ⊗ L_{ψ,-f}` and `L_{ψ,-f} ⊗ L_{ψ,f}` are the regular module, and
`L_{ψ⁻¹,f} ≅ L_{ψ,-f}`.
Source: blueprint lemma-artin-schreier-character-sheaf, proof Step 5
(blueprint: lem-fd-as-trace-tensor-inverse).

Proof: the existing character-projector evaluation theorem identifies the pullback of
the character image to the Artin–Schreier cover with the regular module. Pulling back
along the zero section, which Artin–Schreier fixes, and then along the structural map
of `X` proves the zero-function trivialization. Tensor addition at `f, -f` gives the
first inverse; braiding gives the other order.

Negation is an involution commuting with Artin–Schreier and conjugating translation by
`a` to translation by `-a`. Functoriality of direct image and the regular-module unit maps
transport this identity to the pushforward; uniqueness of right adjoints identifies
pullback and pushforward along negation. Reindexing the projector sum by negation then
conjugates the `ψ` and `ψ⁻¹` projectors. Pullback preserves their images, and pulling back
along the morphism defined by `f` gives the last isomorphism. The argument also applies in
characteristic two and on the empty base. -/
theorem condensedArtinSchreier_tensor_inverse_generic
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]
    (ψ : AddChar k (MonObj.Γ Λ)) (hψ : ψ ≠ 1)
    (hq : IsUnit (Fintype.card k : MonObj.Γ Λ))
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) :
    Nonempty (ProEtale.condensedArtinSchreierSheafOf Λ k X ψ f ⊗
      ProEtale.condensedArtinSchreierSheafOf Λ k X ψ (-f) ≅
      Mod.regular (ProEtale.condensedRingObj Λ X)) ∧
    Nonempty (ProEtale.condensedArtinSchreierSheafOf Λ k X ψ (-f) ⊗
      ProEtale.condensedArtinSchreierSheafOf Λ k X ψ f ≅
      Mod.regular (ProEtale.condensedRingObj Λ X)) ∧
    Nonempty (ProEtale.condensedArtinSchreierSheafOf Λ k X ψ⁻¹ f ≅
      ProEtale.condensedArtinSchreierSheafOf Λ k X ψ (-f)) := by
  classical
  obtain ⟨e₀⟩ := origin_trivialization Λ k ψ hq
  obtain ⟨ez⟩ := zero_transport Λ k ψ e₀ X
  obtain ⟨ea⟩ := condensedArtinSchreier_tensor_add_generic Λ k ψ hψ hq X f (-f)
  let ei := ea ≪≫ eqToIso (congrArg
    (ProEtale.condensedArtinSchreierSheafOf Λ k X ψ) (add_neg_cancel f)) ≪≫ ez
  obtain ⟨er⟩ := neg_intertwine_image Λ k ψ (reflection_total_iso Λ k)
    (neg_projector_conjugate Λ k ψ (reflection_total_iso Λ k)
      (reflection_total_conjugates Λ k))
  obtain ⟨en⟩ := neg_transport Λ k ψ er X f
  exact ⟨⟨ei⟩, ⟨(β_ _ _) ≪≫ ei⟩, ⟨en⟩⟩

end AlgebraicGeometry.ArtinSchreierTrace

/-! ### Scaling by a unit

Scaling `[c] : x ↦ c x` of the affine line by `c ∈ kˣ` commutes with Artin–Schreier, since
`c ^ q = c`, and conjugates translation by `c⁻¹ a` to translation by `a`. As for negation, this
transports the `ψ`-projector to the `ψ(c ·)`-projector, so `[c]^* L_ψ ≅ L_{ψ(c ·)}`.
-/

namespace AlgebraicGeometry.ArtinSchreierTrace
open ProEtale ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k] (c : kˣ)
local notation "A" => 𝔸(PUnit; Spec (CommRingCat.of k))
local notation "AS" => AffineSpace.artinSchreierMap PUnit (Spec (CommRingCat.of k)) (Fintype.card k)
local notation "S" => Etale.artinSchreierScaling k (c : k)
local notation "S'" => Etale.artinSchreierScaling k ((c⁻¹ : kˣ) : k)
attribute [local instance] linearModules linearLowerStar linearUpperStar

omit [Fintype k] in
private theorem scaling_comp_inv : S ≫ S' = 𝟙 A := by
  rw [← Etale.artinSchreierScaling_mul, Units.mul_inv, Etale.artinSchreierScaling_one]

omit [Fintype k] in
private theorem scaling_inv_comp : S' ≫ S = 𝟙 A := by
  rw [← Etale.artinSchreierScaling_mul, Units.inv_mul, Etale.artinSchreierScaling_one]

private theorem scaling_square : S ≫ AS ≫ S' = AS := by
  rw [Etale.artinSchreierScaling_comp_artinSchreierMap_assoc, scaling_comp_inv,
    Category.comp_id]

private def scaling_pull_push :
    CondensedRing.upperStar Λ S ≅ CondensedRing.lowerStar Λ S' := by
  let η : CondensedRing.upperStar Λ S' ⋙ CondensedRing.upperStar Λ S ≅ 𝟭 _ :=
    (CondensedRing.upperStarComp Λ S S').symm ≪≫
      upperStarCongr Λ (scaling_comp_inv k c) ≪≫ CondensedRing.upperStarId Λ A
  let ε : CondensedRing.upperStar Λ S ⋙ CondensedRing.upperStar Λ S' ≅ 𝟭 _ :=
    (CondensedRing.upperStarComp Λ S' S).symm ≪≫
      upperStarCongr Λ (scaling_inv_comp k c) ≪≫ CondensedRing.upperStarId Λ A
  let E := CategoryTheory.Equivalence.mk
    (CondensedRing.upperStar Λ S') (CondensedRing.upperStar Λ S) η.symm ε
  exact Adjunction.rightAdjointUniq E.toAdjunction
    (CondensedRing.upperStarLowerStarAdjunction Λ S')

private def scaling_push_iso :
    (CondensedRing.lowerStar Λ S').obj (condensedArtinSchreierPushforward Λ k) ≅
      condensedArtinSchreierPushforward Λ k :=
  (CondensedRing.lowerStarComp Λ AS S').app (reg Λ A) ≪≫
    mapOverIso Λ (AS ≫ S') AS S (scaling_square k c)

private theorem scaling_conjugates (a : k) :
    (CondensedRing.lowerStar Λ S').map (condensedArtinSchreierTranslationAction Λ k a).asHom ≫
        (scaling_push_iso Λ k c).hom =
      (scaling_push_iso Λ k c).hom ≫
        (condensedArtinSchreierTranslationAction Λ k ((c⁻¹ : kˣ) * a)).asHom := by
  let t := Etale.artinSchreierTranslation k a
  let t' := Etale.artinSchreierTranslation k ((c⁻¹ : kˣ) * a)
  have ht := Etale.artinSchreierTranslation_comp_artinSchreierMap k a
  have ht' := Etale.artinSchreierTranslation_comp_artinSchreierMap k ((c⁻¹ : kˣ) * a)
  have hw : t ≫ (AS ≫ S') = AS ≫ S' := by
    rw [← Category.assoc, ht]
  have hg : S ≫ t = t' ≫ S := by
    rw [Etale.artinSchreierTranslation_comp_artinSchreierScaling, ← mul_assoc,
      Units.mul_inv, one_mul]
  let m := mapOver Λ (AS ≫ S') AS S (scaling_square k c)
  let e := (CondensedRing.lowerStarComp Λ AS S').app (reg Λ A)
  have hm : mapOver Λ (AS ≫ S') (AS ≫ S') t hw ≫ m =
      m ≫ mapOver Λ AS AS t' ht' := by
    rw [← mapOver_comp, ← mapOver_comp]
    exact mapOver_congr Λ _ _ hg _ _
  have hp := mapOver_push Λ S' AS AS t ht
  simp only [action_mapOver]
  change (CondensedRing.lowerStar Λ S').map (mapOver Λ AS AS t ht) ≫
      (e.hom ≫ m) = (e.hom ≫ m) ≫ mapOver Λ AS AS t' ht'
  calc
    _ = ((CondensedRing.lowerStar Λ S').map (mapOver Λ AS AS t ht) ≫ e.hom) ≫ m :=
      (Category.assoc _ _ _).symm
    _ = (e.hom ≫ mapOver Λ (AS ≫ S') (AS ≫ S') t hw) ≫ m :=
      congrArg (fun z ↦ z ≫ m) hp
    _ = e.hom ≫ (mapOver Λ (AS ≫ S') (AS ≫ S') t hw ≫ m) := Category.assoc _ _ _
    _ = e.hom ≫ (m ≫ mapOver Λ AS AS t' ht') := congrArg (fun z ↦ e.hom ≫ z) hm
    _ = _ := (Category.assoc _ _ _).symm

private def scaling_total_iso :
    (CondensedRing.upperStar Λ S).obj (condensedArtinSchreierPushforward Λ k) ≅
      condensedArtinSchreierPushforward Λ k :=
  (scaling_pull_push Λ k c).app _ ≪≫ scaling_push_iso Λ k c

private theorem scaling_total_conjugates (a : k) :
    (CondensedRing.upperStar Λ S).map (condensedArtinSchreierTranslationAction Λ k a).asHom ≫
        (scaling_total_iso Λ k c).hom =
      (scaling_total_iso Λ k c).hom ≫
        (condensedArtinSchreierTranslationAction Λ k ((c⁻¹ : kˣ) * a)).asHom := by
  change _ ≫ (scaling_pull_push Λ k c).hom.app _ ≫ (scaling_push_iso Λ k c).hom = _
  rw [NatTrans.naturality_assoc, scaling_conjugates]
  simp [scaling_total_iso]

private theorem scaling_projector_conjugate (ψ : AddChar k (MonObj.Γ Λ)) :
    (CondensedRing.upperStar Λ S).map (condensedArtinSchreierProjector Λ k ψ).asHom ≫
        (scaling_total_iso Λ k c).hom =
      (scaling_total_iso Λ k c).hom ≫
        (condensedArtinSchreierProjector Λ k (ψ.mulShift c)).asHom := by
  simp only [projector_linear, End.sum_asHom, End.smul_asHom]
  rw [CategoryTheory.Functor.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Fintype.sum_equiv (Units.mulLeft c⁻¹) _ _ fun a ↦ ?_
  rw [CategoryTheory.Functor.map_smul (R := MonObj.Γ Λ), Linear.smul_comp,
    scaling_total_conjugates, Linear.comp_smul, Units.mulLeft_apply, AddChar.mulShift_apply,
    mul_neg, ← mul_assoc, Units.mul_inv, one_mul]

/-- Pullback along the scaling `[c] : x ↦ c x` of the affine line by `c ∈ kˣ` carries the
condensed Artin–Schreier sheaf of `ψ` to that of the shifted character `ψ(c ·)`.
Source: blueprint lemma-artin-schreier-character-sheaf (2) (blueprint:
lemma-artin-schreier-character-sheaf--2).

Proof: the scaling `[c]` is an automorphism commuting with Artin–Schreier and conjugating
translation by `c⁻¹ a` to translation by `a`. As for negation, pullback along `[c]` is
pushforward along `[c⁻¹]`, and it carries the `ψ`-projector to the `ψ(c ·)`-projector after
reindexing the average by `a ↦ c⁻¹ a`. Pullback preserves images. -/
theorem nonempty_iso_upperStar_scaling_condensedArtinSchreierSheaf
    (ψ : AddChar k (MonObj.Γ Λ)) :
    Nonempty ((CondensedRing.upperStar Λ S).obj (condensedArtinSchreierSheaf Λ k ψ) ≅
      condensedArtinSchreierSheaf Λ k (ψ.mulShift c)) := by
  let F := CondensedRing.upperStar Λ S
  let p := (condensedArtinSchreierProjector Λ k ψ).asHom
  let e := scaling_total_iso Λ k c
  refine ⟨(PreservesImage.iso F p).symm ≪≫
    image.compIso (F.map p) e.hom ≪≫ image.eqToIso (scaling_projector_conjugate Λ k c ψ) ≪≫ ?_⟩
  exact asIso (image.preComp e.hom (condensedArtinSchreierProjector Λ k (ψ.mulShift c)).asHom)

end AlgebraicGeometry.ArtinSchreierTrace

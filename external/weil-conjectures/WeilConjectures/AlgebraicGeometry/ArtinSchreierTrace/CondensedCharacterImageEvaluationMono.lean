/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedDeckEvaluation
import all WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.DetectionAb
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import Mathlib.Tactic.LinearCombination

/-! # Recognition of condensed character images

Source: blueprint lemma-artin-schreier-character-sheaf, proof Step 5, and the finite-torsor
isotypic argument in `WeilConjectures.SixFunctors.Finite.Isotypic`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ArtinSchreierTrace

attribute [local irreducible] ProEtale.CondensedRing.upperStar
  ProEtale.CondensedRing.lowerStar ProEtale.CondensedRing.upperStarLowerStarAdjunction

open ProEtale.CondensedRing

private theorem module_map_eq_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} {I : Type*} [Finite I]
    (g : I → (U ⟶ X)) [∀ a, QuasiCompact (g a)]
    (hg : ∀ x, ∃ a, x ∈ Set.range (g a))
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)} (k : M ⟶ N)
    (hk : ∀ a, (upperStar Λ (g a)).map k = 0) : k = 0 := by
  apply (Mod.forget _).map_injective
  rw [Functor.map_zero]
  apply ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp g hg
  intro a
  apply (cancel_mono ((upperStarForgetIso Λ (g a)).hom.app N)).1
  rw [zero_comp]
  have hn := (upperStarForgetIso Λ (g a)).hom.naturality k
  simp only [Functor.comp_map] at hn
  rw [hn, hk a, Functor.map_zero, comp_zero]

private theorem eq_zero_of_adjoint_eq_zero
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {R : D ⥤ C} [F.Additive] (adj : F ⊣ R)
    {Q : C} {N : D} (k : Q ⟶ R.obj N)
    (hk : (adj.homEquiv _ _).symm k = 0) : k = 0 := by
  apply (adj.homEquiv _ _).symm.injective
  simpa only [Adjunction.homEquiv_counit, Functor.map_zero, zero_comp] using hk

private theorem map_adjoint_eq_zero
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {R : D ⥤ C} (adj : F ⊣ R) (H : D ⥤ C) (J : C ⥤ C)
    (c : J ≅ F ⋙ H) {Q : C} {N : D} (k : Q ⟶ R.obj N)
    (hk : J.map k ≫ c.hom.app (R.obj N) ≫ H.map (adj.counit.app N) = 0) :
    H.map ((adj.homEquiv _ _).symm k) = 0 := by
  apply (cancel_epi (c.hom.app Q)).1
  rw [comp_zero, Adjunction.homEquiv_counit, Functor.map_comp, ← Category.assoc]
  have hn := c.hom.naturality k
  simp only [Functor.comp_map] at hn
  rw [← hn, Category.assoc]
  exact hk

private theorem jointly_detect_adjoint
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {R : D ⥤ C} [F.Additive] (adj : F ⊣ R)
    (I : Type*) (H : I → (D ⥤ C)) (J : I → (C ⥤ C)) (c : ∀ a, J a ≅ F ⋙ H a)
    (hdetect : ∀ {M N : D} (k : M ⟶ N), (∀ a, (H a).map k = 0) → k = 0)
    {Q : C} {N : D} (k : Q ⟶ R.obj N)
    (hk : ∀ a, (J a).map k ≫ (c a).hom.app (R.obj N) ≫
      (H a).map (adj.counit.app N) = 0) : k = 0 := by
  apply eq_zero_of_adjoint_eq_zero adj k
  apply hdetect
  intro a
  exact map_adjoint_eq_zero adj (H a) (J a) (c a) k (hk a)

private theorem projection_zero_of_iso
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C]
    [HasZeroMorphisms D] {F J : C ⥤ D} (c : F ≅ J)
    {Q M : C} {N : D} (k : Q ⟶ M) (p : J.obj M ⟶ N) (q : F.obj M ⟶ N)
    (hp : c.hom.app M ≫ p = q) (hk : F.map k ≫ q = 0) : J.map k ≫ p = 0 := by
  apply (cancel_epi (c.hom.app Q)).1
  rw [comp_zero, ← Category.assoc, ← c.hom.naturality k, Category.assoc, hp]
  exact hk

private theorem projection_rfl
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z U : Scheme.{u}} (p : Z ⟶ U)
    (s : U ⟶ Z)
    (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ Z)) :
    (upperStarComp Λ s p).hom.app ((lowerStar Λ p).obj N) ≫
      (upperStar Λ s).map ((upperStarLowerStarAdjunction Λ p).counit.app N) =
      stalkLowerStarProj Λ (rfl : s ≫ p = s ≫ p) N := by
  simp only [stalkLowerStarProj, eqToHom_refl, Category.id_comp]

private theorem section_eval_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z U : Scheme.{u}} (p : Z ⟶ U)
    (s : U ⟶ Z) (hs : s ≫ p = 𝟙 U)
    (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ Z))
    {Q : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ U)} (k : Q ⟶ (lowerStar Λ p).obj N)
    (hk : (upperStar Λ (𝟙 U)).map k ≫ stalkLowerStarProj Λ hs N = 0) :
    (upperStar Λ (s ≫ p)).map k ≫
      (upperStarComp Λ s p).hom.app ((lowerStar Λ p).obj N) ≫
        (upperStar Λ s).map ((upperStarLowerStarAdjunction Λ p).counit.app N) = 0 := by
  rw [projection_rfl]
  exact projection_zero_of_iso (upperStarCongr Λ hs.symm) k _ _
    (upperStarCongr_hom_app_stalkLowerStarProj Λ hs.symm hs rfl N) hk

-- Explicit internal-module comparisons require additional elaboration heartbeats.
private theorem sections_detect
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z U : Scheme.{u}} (p : Z ⟶ U)
    {I : Type*} [Finite I] (s : I → (U ⟶ Z))
    (hs : ∀ a, s a ≫ p = 𝟙 U) [∀ a, QuasiCompact (s a)]
    (hcover : ∀ z, ∃ a, z ∈ Set.range (s a))
    (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ Z))
    {Q : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ U)}
    (k : Q ⟶ (lowerStar Λ p).obj N)
    (hk : ∀ a, (upperStar Λ (𝟙 U)).map k ≫
      stalkLowerStarProj Λ (hs a) N = 0) : k = 0 := by
  exact jointly_detect_adjoint (F := upperStar Λ p) (R := lowerStar Λ p)
    (upperStarLowerStarAdjunction Λ p) I
    (fun a ↦ upperStar Λ (s a)) (fun a ↦ upperStar Λ (s a ≫ p))
    (fun a ↦ upperStarComp Λ (s a) p)
    (fun {_ _} k hk ↦ module_map_eq_zero Λ s hcover k hk) k
    (fun a ↦ section_eval_zero Λ p (s a) (hs a) N k (hk a))

private theorem baseChange_section
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z U : Scheme.{u}}
    {f : X ⟶ Y} {g : U ⟶ Y} {p : Z ⟶ U} {q : Z ⟶ X}
    (sq : CommSq q p f g) (s : U ⟶ Z) (hs : s ≫ p = 𝟙 U)
    (ht : (s ≫ q) ≫ f = g)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)) :
    (lowerStarBaseChange Λ sq).app N ≫ (upperStarId Λ U).inv.app _ ≫
      stalkLowerStarProj Λ hs ((upperStar Λ q).obj N) =
    stalkLowerStarProj Λ ht N ≫ (upperStarComp Λ s q).hom.app N := by
  have hxy : (s ≫ q) ≫ f = (𝟙 U) ≫ g := by simpa using ht
  have h := stalkLowerStarProj_lowerStarBaseChange' Λ sq hs hxy N
  apply (cancel_epi ((upperStarCongr Λ (Category.id_comp g)).hom.app
    ((lowerStar Λ f).obj N))).1
  rw [upperStarCongr_hom_app_stalkLowerStarProj_assoc Λ (Category.id_comp g) hxy ht]
  rw [← h]
  simp only [upperStarComp_id_left, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.rightUnitor_inv_app, Category.id_comp, Category.assoc]
  have hn := (upperStarId Λ U).inv.naturality ((lowerStarBaseChange Λ sq).app N)
  simp only [Functor.id_map] at hn
  rw [reassoc_of% hn]

private theorem baseChange_detect
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z U : Scheme.{u}}
    {f : X ⟶ Y} {g : U ⟶ Y} {p : Z ⟶ U} {q : Z ⟶ X}
    (sq : CommSq q p f g) [IsIso (lowerStarBaseChange Λ sq)]
    {I : Type*} [Finite I] (s : I → (U ⟶ Z))
    (hs : ∀ a, s a ≫ p = 𝟙 U) [∀ a, QuasiCompact (s a)]
    (hcover : ∀ z, ∃ a, z ∈ Set.range (s a))
    (ht : ∀ a, (s a ≫ q) ≫ f = g)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X))
    {Q : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ U)}
    (k : Q ⟶ (upperStar Λ g).obj ((lowerStar Λ f).obj N))
    (hk : ∀ a, k ≫ stalkLowerStarProj Λ (ht a) N = 0) : k = 0 := by
  let β := (lowerStarBaseChange Λ sq).app N
  apply (cancel_mono β).1
  rw [zero_comp]
  apply sections_detect Λ p s hs hcover
  intro a
  apply (cancel_epi ((upperStarId Λ U).inv.app Q)).1
  rw [comp_zero]
  have hn := (upperStarId Λ U).inv.naturality (k ≫ β)
  simp only [Functor.id_map] at hn
  rw [← Category.assoc, ← hn, Category.assoc]
  dsimp only [β]
  rw [Category.assoc]
  erw [baseChange_section Λ sq (s a) (hs a) (ht a) N]
  rw [← Category.assoc, hk a, zero_comp]

private theorem deck_cover {X : Scheme.{u}} (Y : Over X)
    (G : Type u) [AddCommGroup G]
    (σ : Multiplicative G →* Aut Y)
    (htrans : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s t : Spec (.of Ω) ⟶ Y.left), s ≫ Y.hom = t ≫ Y.hom →
        ∃ a : G, s = t ≫ (σ (Multiplicative.ofAdd a)).asIso.hom.left) :
    ∀ z : (pullback Y.hom Y.hom : Scheme.{u}), ∃ a : G,
      z ∈ Set.range (pullback.lift (σ (Multiplicative.ofAdd a)).asIso.hom.left (𝟙 Y.left)
        (by simp)) := by
  intro z
  let t := (pullback Y.hom Y.hom : Scheme.{u}).algClosurePoint z
  obtain ⟨a, ha⟩ := htrans _ (t ≫ pullback.fst _ _) (t ≫ pullback.snd _ _)
    (by simp only [Category.assoc, pullback.condition])
  refine ⟨a, (t ≫ pullback.snd _ _) (IsLocalRing.closedPoint _), ?_⟩
  have he : t = (t ≫ pullback.snd _ _) ≫
      pullback.lift (σ (Multiplicative.ofAdd a)).asIso.hom.left (𝟙 Y.left)
        (by simp) := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using ha
    · simp
  rw [← Scheme.Hom.comp_apply, ← he]
  exact Scheme.algClosurePoint_base _ _ _

private theorem condensedPull_eq_deck
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (Y : Over X) (h : Y ⟶ Y) :
    condensedPull Λ h = (regularDeckEnd Λ Y.hom h.left (Over.w h)).asHom := by
  unfold condensedPull regularDeckEnd
  congr 2
  apply Mod.regular_hom_ext
  rw [Mod.one_comp_regularLift]
  have hh := homEquiv_εIso_inv_hom Λ h.left
  simp only [Mod.tensorUnit_eq_regular] at hh
  erw [hh]

private theorem projection_zero_congr
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y P : Scheme.{u}}
    (f : X ⟶ Y) (v : P ⟶ Y) {g h : P ⟶ X} (e : g = h)
    (hg : g ≫ f = v) (hh : h ≫ f = v)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X))
    {Q : Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ P)}
    (k : Q ⟶ (upperStar Λ v).obj ((lowerStar Λ f).obj N))
    (hk : k ≫ stalkLowerStarProj Λ hh N = 0) :
    k ≫ stalkLowerStarProj Λ hg N = 0 := by
  apply (cancel_mono ((upperStarCongr Λ e).hom.app N)).1
  rw [zero_comp, Category.assoc]
  rw [stalkLowerStarProj_upperStarCongr_hom_app Λ e hg hh N]
  exact hk

-- Graphs enter the pullback comparisons through their projection equations.
private theorem graphs_detect
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (Y : Over X)
    [IsFinite Y.hom] [Etale Y.hom] {I : Type*} [Finite I]
    (t : I → (Y ⟶ Y))
    (hcover : ∀ z : (pullback Y.hom Y.hom : Scheme.{u}), ∃ a, z ∈ Set.range
      (pullback.lift (t a).left (𝟙 Y.left) (by simp)))
    (N : Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ Y.left))
    {Q : Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ Y.left)}
    (k : Q ⟶ (upperStar Λ Y.hom).obj ((lowerStar Λ Y.hom).obj N))
    (hk : ∀ a, k ≫ stalkLowerStarProj Λ (Over.w (t a)) N = 0) : k = 0 := by
  let s : I → (Y.left ⟶ pullback Y.hom Y.hom) := fun a ↦
    pullback.lift (t a).left (𝟙 Y.left) (by simp)
  have hs (a : I) : s a ≫ pullback.snd Y.hom Y.hom = 𝟙 Y.left := by simp [s]
  let (a : I) : IsClosedImmersion (s a) := by
    have : IsClosedImmersion (s a ≫ pullback.snd Y.hom Y.hom) := by
      rw [hs]
      infer_instance
    exact IsClosedImmersion.of_comp (s a) (pullback.snd Y.hom Y.hom)
  let (a : I) : QuasiCompact (s a) := inferInstance
  let sq := (IsPullback.of_hasPullback Y.hom Y.hom).toCommSq
  have : IsIso (lowerStarBaseChange Λ sq) :=
    isIso_lowerStarBaseChange_of_isPullback Λ (IsPullback.of_hasPullback _ _)
  apply baseChange_detect Λ sq s hs hcover
    (fun a ↦ show (s a ≫ pullback.fst Y.hom Y.hom) ≫ Y.hom = Y.hom by simp [s]) N k
  intro a
  exact projection_zero_congr Λ Y.hom Y.hom (by simp [s]) _ (Over.w (t a)) N k (hk a)

private theorem deck_eval_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (Y : Over X) (τ : Y ⟶ Y)
    {Q : Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ Y.left)}
    (k : Q ⟶ (upperStar Λ Y.hom).obj
      ((lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left)))
    (hk : k ≫ (upperStar Λ Y.hom).map (condensedPull Λ τ) ≫
      (upperStarLowerStarAdjunction Λ Y.hom).counit.app (condensedUnit Λ Y.left) = 0) :
    k ≫ stalkLowerStarProj Λ (Over.w τ) (condensedUnit Λ Y.left) = 0 := by
  dsimp only [condensedUnit] at *
  have hd := deck_counit Λ Y.hom τ.left (Over.w τ)
  rw [← condensedPull_eq_deck Λ Y τ] at hd
  apply (cancel_mono (Functor.Monoidal.εIso (upperStar Λ τ.left)).inv).1
  rw [zero_comp, Category.assoc]
  exact (congrArg (fun z ↦ k ≫ z) hd.symm).trans hk

private theorem morphisms_detect
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (Y : Over X)
    [IsFinite Y.hom] [Etale Y.hom] {I : Type*} [Finite I]
    (t : I → (Y ⟶ Y))
    (hcover : ∀ z : (pullback Y.hom Y.hom : Scheme.{u}), ∃ a, z ∈ Set.range
      (pullback.lift (t a).left (𝟙 Y.left) (by simp)))
    {Q : Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ Y.left)}
    (k : Q ⟶ (upperStar Λ Y.hom).obj
      ((lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left)))
    (hk : ∀ a, k ≫ (upperStar Λ Y.hom).map (condensedPull Λ (t a)) ≫
      (upperStarLowerStarAdjunction Λ Y.hom).counit.app (condensedUnit Λ Y.left) = 0) :
    k = 0 := by
  have hp (a : I) : k ≫ stalkLowerStarProj Λ (Over.w (t a))
      (condensedUnit Λ Y.left) = 0 := deck_eval_zero Λ Y (t a) k (hk a)
  exact graphs_detect Λ Y t hcover (condensedUnit Λ Y.left) k hp

private theorem deck_detect
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (Y : Over X)
    [IsFinite Y.hom] [Etale Y.hom]
    (G : Type u) [AddCommGroup G] [Finite G]
    (σ : Multiplicative G →* Aut Y)
    (htrans : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s t : Spec (.of Ω) ⟶ Y.left), s ≫ Y.hom = t ≫ Y.hom →
        ∃ a : G, s = t ≫ (σ (Multiplicative.ofAdd a)).asIso.hom.left)
    {Q : Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ Y.left)}
    (k : Q ⟶ (upperStar Λ Y.hom).obj
      ((lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left)))
    (hk : ∀ a, k ≫ (upperStar Λ Y.hom).map
      (condensedPull Λ (σ (Multiplicative.ofAdd a)).asIso.hom) ≫
        (upperStarLowerStarAdjunction Λ Y.hom).counit.app (condensedUnit Λ Y.left) = 0) :
    k = 0 := by
  let t : G → (Y ⟶ Y) := fun a ↦ (σ (Multiplicative.ofAdd a)).asIso.hom
  have hcover : ∀ z : (pullback Y.hom Y.hom : Scheme.{u}), ∃ a,
      z ∈ Set.range (pullback.lift (t a).left (𝟙 Y.left) (by simp)) :=
    deck_cover Y G σ htrans
  exact morphisms_detect Λ Y t hcover k hk

private theorem deck_projection_congr
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {g h : X ⟶ X} (e : g = h) (hg : g ≫ f = f) (hh : h ≫ f = f) :
    stalkLowerStarProj Λ hg (Mod.regular (ProEtale.condensedRingObj Λ X)) ≫
      (Functor.Monoidal.εIso (upperStar Λ g)).inv =
    stalkLowerStarProj Λ hh (Mod.regular (ProEtale.condensedRingObj Λ X)) ≫
      (Functor.Monoidal.εIso (upperStar Λ h)).inv := by
  subst h
  rfl

-- Explicit internal-module comparisons require additional elaboration heartbeats.
private theorem deck_evaluation_add
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (Y : Over X)
    (G : Type u) [AddCommGroup G] (σ : Multiplicative G →* Aut Y) (a b : G) :
    (upperStar Λ Y.hom).map (condensedPull Λ (σ (Multiplicative.ofAdd a)).asIso.hom) ≫
      (upperStar Λ Y.hom).map (condensedPull Λ (σ (Multiplicative.ofAdd b)).asIso.hom) ≫
      (upperStarLowerStarAdjunction Λ Y.hom).counit.app (condensedUnit Λ Y.left) =
    (upperStar Λ Y.hom).map (condensedPull Λ (σ (Multiplicative.ofAdd (a + b))).asIso.hom) ≫
      (upperStarLowerStarAdjunction Λ Y.hom).counit.app (condensedUnit Λ Y.left) := by
  simp only [condensedPull_eq_deck]
  dsimp only [condensedUnit]
  rw [deck_counit Λ Y.hom (σ (Multiplicative.ofAdd b)).asIso.hom.left
    (Over.w (σ (Multiplicative.ofAdd b)).asIso.hom),
    deck_counit Λ Y.hom (σ (Multiplicative.ofAdd (a + b))).asIso.hom.left
      (Over.w (σ (Multiplicative.ofAdd (a + b))).asIso.hom)]
  rw [regularDeckEnd_evaluation Λ Y.hom (σ (Multiplicative.ofAdd a)).asIso.hom.left
    (Over.w (σ (Multiplicative.ofAdd a)).asIso.hom) Y.hom
    (σ (Multiplicative.ofAdd b)).asIso.hom.left (Over.w (σ (Multiplicative.ofAdd b)).asIso.hom)]
  have hab : (σ (Multiplicative.ofAdd b)).asIso.hom.left ≫
      (σ (Multiplicative.ofAdd a)).asIso.hom.left =
      (σ (Multiplicative.ofAdd (a + b))).asIso.hom.left := by
    change _ = (σ (Multiplicative.ofAdd a * Multiplicative.ofAdd b)).asIso.hom.left
    rw [map_mul]
    rfl
  exact deck_projection_congr Λ Y.hom hab _ _

private theorem average_evaluation_mono
    {C : Type*} [Category C] [Abelian C] (R : Type*) [CommRing R] [Linear R C]
    {G : Type*} [AddCommGroup G] [Fintype G] (χ : AddChar G R) (c : R)
    {M N : C} (T : G → (M ⟶ M)) (ε : M ⟶ N)
    (hcomp : ∀ a b, T a ≫ T b ≫ ε = T (a + b) ≫ ε)
    (hdetect : ∀ {Q : C} (k : Q ⟶ M), (∀ a, k ≫ T a ≫ ε = 0) → k = 0) :
    Mono (image.ι (∑ a : G, (c * χ (-a)) • T a) ≫ ε) := by
  classical
  let e := ∑ a : G, (c * χ (-a)) • T a
  have he (b : G) : e ≫ T b ≫ ε = χ b • (e ≫ ε) := by
    simp only [e, Preadditive.sum_comp, Linear.smul_comp, hcomp,
      Finset.smul_sum, smul_smul]
    refine Fintype.sum_equiv (Equiv.addRight b) _ _ fun a ↦ ?_
    simp only [Equiv.coe_addRight, neg_add_rev]
    congr 1
    have h : χ b * χ (-b) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [AddChar.map_add_eq_mul]
    linear_combination (-(c * χ (-a))) * h
  have hi (b : G) : image.ι e ≫ T b ≫ ε = χ b • (image.ι e ≫ ε) := by
    apply (cancel_epi (factorThruImage e)).1
    rw [Linear.comp_smul, ← Category.assoc, ← Category.assoc, image.fac,
      ← Category.assoc, image.fac]
    simpa only [Category.assoc] using he b
  change Mono (image.ι e ≫ ε)
  apply Preadditive.mono_of_cancel_zero
  intro Q k hk
  have hz : k ≫ image.ι e = 0 := by
    apply hdetect
    intro a
    rw [Category.assoc, hi, Linear.comp_smul, hk, smul_zero]
  exact (cancel_mono (image.ι e)).1 (by simpa using hz)

-- Explicit internal-module comparisons require additional elaboration heartbeats.
/-- Evaluation on a character-projector image is monic on a transitive finite cover.
Source: blueprint lemma-artin-schreier-character-sheaf Step 5, the eigenfunction calculation, and
Etale.mono_sheafFiber_map_image_ι_isotypicIdempotent_comp_stalkRestrict
(blueprint: lem-fd-as-condensed-character-image-evaluation-mono).

Proof: base change by Y identifies the pulled-back direct image with the direct
image along the second projection of Y ×_X Y. The graphs of the deck maps are
sections of that projection and jointly cover the fibre product, by geometric
transitivity. They are closed immersions, hence quasi-compact; their pullbacks
detect zero morphisms of pro-etale sheaves, and therefore of internal modules.
Adjunction and base-change compatibility identify evaluation at these sections
with the counit after the corresponding deck operator. Reindexing the character
average shows that these translated evaluations on its image are scalar multiples
of the original evaluation. Hence any morphism killed by the original evaluation
is killed by every translated evaluation and must vanish. Pullback preserves
images, so this proves the stated monicity. Empty fibres and nonfree actions
are allowed. The argument even works without invertibility of the group order.
No choice of an eigenmap or a trivialization is needed. -/
theorem condensed_character_image_evaluation_mono
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (Y : Over X)
    [IsFinite Y.hom] [Etale Y.hom]
    (G : Type u) [AddCommGroup G] [Fintype G]
    (σ : Multiplicative G →* Aut Y) (χ : AddChar G (MonObj.Γ Λ))
    (hq : IsUnit (Fintype.card G : MonObj.Γ Λ))
    (htrans : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s t : Spec (.of Ω) ⟶ Y.left), s ≫ Y.hom = t ≫ Y.hom →
        ∃ a : G, s = t ≫ (σ (Multiplicative.ofAdd a)).asIso.hom.left) :
    Mono ((ProEtale.CondensedRing.upperStar Λ Y.hom).map
        (image.ι (condensedProjector Λ G Y
          (fun a ↦ (σ (Multiplicative.ofAdd a)).asIso.hom) χ).asHom) ≫
      (ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ Y.hom).counit.app
        (condensedUnit Λ Y.left)) := by
  classical
  have _ := hq
  let := Mod.linearOfRingHom
    (MonObj.Γ.mapFunctor (ProEtale.upperStarFromPoint X) (R := Λ))
  let := Mod.linearOfRingHom
    (MonObj.Γ.mapFunctor (ProEtale.upperStarFromPoint Y.left) (R := Λ))
  let := ProEtale.linear_lowerStar Λ Y.hom
  let := ProEtale.condensedModulePullback_linear Λ Y.hom
  let F := upperStar Λ Y.hom
  let e := (condensedProjector Λ G Y
    (fun a ↦ (σ (Multiplicative.ofAdd a)).asIso.hom) χ).asHom
  let ε := (upperStarLowerStarAdjunction Λ Y.hom).counit.app (condensedUnit Λ Y.left)
  have he : F.map e = ∑ a : G,
      (Ring.inverse (Fintype.card G : MonObj.Γ Λ) * χ (-a)) •
        F.map (condensedPull Λ (σ (Multiplicative.ofAdd a)).asIso.hom) := by
    dsimp only [e]
    unfold condensedProjector
    simp only [End.sum_asHom]
    rw [Functor.map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [ProEtale.regularEnd_eq_smul, Functor.map_smul]
    have hid := (lowerStar Λ Y.hom).map_id (Mod.regular (ProEtale.condensedRingObj Λ Y.left))
    rw [hid, Linear.comp_smul]
    erw [Category.comp_id]
    exact F.map_smul _ _
  have : Mono (image.ι (F.map e) ≫ ε) := by
    rw [he]
    exact average_evaluation_mono (MonObj.Γ Λ) χ _ _ ε
      (deck_evaluation_add Λ Y G σ) (deck_detect Λ Y G σ htrans)
  change Mono (F.map (image.ι e) ≫ ε)
  rw [← PreservesImage.inv_comp_image_ι_map F e, Category.assoc]
  infer_instance

end AlgebraicGeometry.ArtinSchreierTrace

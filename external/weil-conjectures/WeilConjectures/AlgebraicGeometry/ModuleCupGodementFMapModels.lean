/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCodegeneracies
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCosimplicialInput
import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
import all WeilConjectures.AlgebraicGeometry.ModuleCupGodementBetaExists
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementIteratePairingsCanonicalCollapse
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementPairingsFromBeta

set_option linter.privateModule false

/-! # Augmented cosimplicial Godement maps across a scheme morphism

The remaining construction takes place entirely before alternating cofaces and extension by zero.
Source: Stacks Project, Tags 0FKR and 0FKU, extended by the coordinate argument below.
(auxiliary; not a blueprint node).
-/

@[expose] public section
universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

-- Transport a specified iterate pairing, retaining its degreewise formula.
-- This is the assembly argument of ModuleCupGodementCoefficientModels, localized
-- here so the cross-scheme construction does not import coefficient models.
namespace FMap

private def stalk {X Y : Scheme.{v}} (f : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (q : F ⟶ (pushforward f).obj G) (x : Y) :
    F.presheaf.stalk (f x) ⟶ G.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor Ab.{v} (f x)).map q.mapPresheaf ≫
    G.presheaf.stalkPushforward Ab.{v} f.base x

private theorem stalk_germ {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (x : Y) (U : X.Opens) (hx : f x ∈ U) (s : Γ(F, U)) :
    stalk f q x (F.presheaf.germ U (f x) hx s) =
      G.presheaf.germ (f ⁻¹ᵁ U) x hx (q.app U s) := by
  dsimp only [stalk]
  rw [ConcreteCategory.comp_apply]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change G.presheaf.stalkPushforward Ab.{v} f.base x
    (((TopCat.Presheaf.pushforward Ab.{v} f.base).obj G.presheaf).germ U (f x) hx
      (q.app U s)) = _
  erw [TopCat.Presheaf.stalkPushforward_germ_apply]

private def proj (X : Scheme.{v}) (F : X.Modules) (x : X) :
    moduleCup_godementObject X F ⟶ skyscraper x (F.presheaf.stalk x) :=
  Pi.π (fun y : X ↦ skyscraper y (F.presheaf.stalk y)) x

private def coord {X Y : Scheme.{v}} (f : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (q : F ⟶ (pushforward f).obj G) (x : Y) :
    skyscraper (f x) (F.presheaf.stalk (f x)) ⟶
      (pushforward f).obj (skyscraper x (G.presheaf.stalk x)) := by
  algebraize [(f.stalkMap x).hom]
  letI : Module (X.presheaf.stalk (f x)) (G.presheaf.stalk x) :=
    Module.compHom (G.presheaf.stalk x) (f.stalkMap x).hom
  letI : IsScalarTower (X.presheaf.stalk (f x)) (Y.presheaf.stalk x)
      (G.presheaf.stalk x) :=
    ⟨fun r s m ↦ smul_assoc ((f.stalkMap x).hom r) s m⟩
  let l : F.presheaf.stalk (f x) →ₗ[X.presheaf.stalk (f x)] G.presheaf.stalk x :=
    stalkLinearMapMk (stalk f q x).hom fun U hx r s ↦ by
      rw [stalk_germ, stalk_germ]
      rw [Hom.app_smul]
      change G.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U r • (show Γ(G, f ⁻¹ᵁ U) from q.app U s)) = _
      rw [germ_smul]
      rw [germ_smul_eq_germ_app_smul f x (G.presheaf.stalk x) rfl hx r]
  exact toSkyscraper (l ∘ₗ skyscraperStalkEval (f x) (F.presheaf.stalk (f x))) ≫
    (pushforwardSkyscraperIso f x (G.presheaf.stalk x) rfl).inv

private theorem coord_apply {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (x : Y) (U : X.Opens) (hx : f x ∈ U)
    (s : Γ(skyscraper (f x) (F.presheaf.stalk (f x)), U)) :
    (coord f q x).app U s ⟨hx⟩ = stalk f q x (s ⟨hx⟩) := by
  change stalk f q x (skyscraperStalkEval (f x) (F.presheaf.stalk (f x))
    ((skyscraper (f x) (F.presheaf.stalk (f x))).presheaf.germ U (f x) hx s)) = _
  rw [skyscraperStalkEval_germ]

private def lift {X Y : Scheme.{v}} (f : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (q : F ⟶ (pushforward f).obj G) :
    moduleCup_godementObject X F ⟶ (pushforward f).obj (moduleCup_godementObject Y G) :=
  Pi.lift (fun x : Y ↦ proj X F (f x) ≫ coord f q x) ≫
    inv (piComparison (pushforward f) (fun x : Y ↦ skyscraper x (G.presheaf.stalk x)))

private theorem lift_proj {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G) (x : Y) :
    lift f q ≫ (pushforward f).map (proj Y G x) =
      proj X F (f x) ≫ coord f q x := by
  simp only [lift, proj, Category.assoc, inv_piComparison_comp_map_π, Pi.lift_comp_π]

private theorem lift_apply {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (x : Y) (U : X.Opens) (hx : f x ∈ U) (s : Γ(moduleCup_godementObject X F, U)) :
    (proj Y G x).app (f ⁻¹ᵁ U) ((lift f q).app U s) ⟨hx⟩ =
      stalk f q x ((proj X F (f x)).app U s ⟨hx⟩) := by
  change ((lift f q ≫ (pushforward f).map (proj Y G x)).app U s) ⟨hx⟩ = _
  rw [lift_proj, Hom.comp_app, ConcreteCategory.comp_apply, coord_apply]

private theorem target_ext {X Y : Scheme.{v}} (f : Y ⟶ X) (G : Y.Modules)
    {P : X.Modules} (r s : P ⟶ (pushforward f).obj (moduleCup_godementObject Y G))
    (h : ∀ x : Y, r ≫ (pushforward f).map (proj Y G x) =
      s ≫ (pushforward f).map (proj Y G x)) : r = s := by
  apply (cancel_mono (piComparison (pushforward f)
    (fun x : Y ↦ skyscraper x (G.presheaf.stalk x)))).1
  apply Pi.hom_ext
  intro x
  simpa only [Category.assoc, piComparison_comp_π, proj] using h x

private theorem unit_apply (X : Scheme.{v}) (F : X.Modules) (x : X)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(F, U)) :
    (proj X F x).app U ((moduleCup_godementUnit X F).app U s) ⟨hx⟩ =
      F.presheaf.germ U x hx s := by
  change ((moduleCup_godementUnit X F ≫ proj X F x).app U s) ⟨hx⟩ = _
  simp only [moduleCup_godementUnit, proj, Pi.lift_comp_π]
  erw [toSkyscraper_app_apply]
  rfl

private theorem lift_unit {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G) :
    moduleCup_godementUnit X F ≫ lift f q =
      q ≫ (pushforward f).map (moduleCup_godementUnit Y G) := by
  apply target_ext f G
  intro x
  apply hom_ext
  intro U
  ext s
  apply SkyscraperSections.ext
  intro hx
  change (proj Y G x).app (f ⁻¹ᵁ U)
    ((lift f q).app U ((moduleCup_godementUnit X F).app U s)) ⟨hx⟩ =
    (proj Y G x).app (f ⁻¹ᵁ U)
      ((moduleCup_godementUnit Y G).app (f ⁻¹ᵁ U) (q.app U s)) ⟨hx⟩
  rw [lift_apply, unit_apply, unit_apply, stalk_germ]

private theorem stalk_precomp {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F H : X.Modules} {G : Y.Modules} (a : F ⟶ H)
    (q : H ⟶ (pushforward f).obj G) (x : Y) (s : F.presheaf.stalk (f x)) :
    stalk f (a ≫ q) x s = stalk f q x (a.stalkLinearMap (f x) s) := by
  obtain ⟨U, hx, s, rfl⟩ := F.presheaf.exists_germ_eq s
  rw [stalk_germ, Hom.stalkLinearMap_germ, stalk_germ]
  rfl

private theorem stalk_postcomp {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G H : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (b : G ⟶ H) (x : Y) (s : F.presheaf.stalk (f x)) :
    stalk f (q ≫ (pushforward f).map b) x s =
      b.stalkLinearMap x (stalk f q x s) := by
  obtain ⟨U, hx, s, rfl⟩ := F.presheaf.exists_germ_eq s
  rw [stalk_germ, stalk_germ, Hom.stalkLinearMap_germ]
  rfl

private theorem map_apply (X : Scheme.{v}) {F G : X.Modules} (q : F ⟶ G)
    (x : X) (U : X.Opens) (hx : x ∈ U)
    (s : Γ(moduleCup_godementObject X F, U)) :
    (proj X G x).app U ((moduleCup_godementMap X q).app U s) ⟨hx⟩ =
      q.stalkLinearMap x ((proj X F x).app U s ⟨hx⟩) := by
  change ((moduleCup_godementMap X q ≫ proj X G x).app U s) ⟨hx⟩ = _
  simp only [moduleCup_godementMap, proj, Pi.lift_comp_π, Hom.comp_app,
    ConcreteCategory.comp_apply]
  erw [toSkyscraper_app_apply]
  rw [LinearMap.comp_apply, skyscraperStalkEval_germ]

private theorem lift_precomp {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F H : X.Modules} {G : Y.Modules} (a : F ⟶ H)
    (q : H ⟶ (pushforward f).obj G) :
    lift f (a ≫ q) = moduleCup_godementMap X a ≫ lift f q := by
  apply target_ext f G
  intro x
  apply hom_ext
  intro U
  ext s
  apply SkyscraperSections.ext
  intro hx
  change (proj Y G x).app (f ⁻¹ᵁ U) ((lift f (a ≫ q)).app U s) ⟨hx⟩ =
    (proj Y G x).app (f ⁻¹ᵁ U)
      ((lift f q).app U ((moduleCup_godementMap X a).app U s)) ⟨hx⟩
  rw [lift_apply, lift_apply, map_apply, stalk_precomp]

private theorem lift_postcomp {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G H : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (b : G ⟶ H) :
    lift f (q ≫ (pushforward f).map b) =
      lift f q ≫ (pushforward f).map (moduleCup_godementMap Y b) := by
  apply target_ext f H
  intro x
  apply hom_ext
  intro U
  ext s
  apply SkyscraperSections.ext
  intro hx
  change (proj Y H x).app (f ⁻¹ᵁ U)
      ((lift f (q ≫ (pushforward f).map b)).app U s) ⟨hx⟩ =
    (proj Y H x).app (f ⁻¹ᵁ U)
      ((moduleCup_godementMap Y b).app (f ⁻¹ᵁ U) ((lift f q).app U s)) ⟨hx⟩
  rw [lift_apply, map_apply, lift_apply, stalk_postcomp]

private def eval (X : Scheme.{v}) (F : X.Modules) (x : X) :
    (moduleCup_godementObject X F).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      F.presheaf.stalk x :=
  skyscraperStalkEval x (F.presheaf.stalk x) ∘ₗ (proj X F x).stalkLinearMap x

private theorem eval_germ (X : Scheme.{v}) (F : X.Modules) (x : X)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(moduleCup_godementObject X F, U)) :
    eval X F x ((moduleCup_godementObject X F).presheaf.germ U x hx s) =
      (proj X F x).app U s ⟨hx⟩ := by
  rw [eval, LinearMap.comp_apply, Hom.stalkLinearMap_germ, skyscraperStalkEval_germ]

private theorem multiply_apply (X : Scheme.{v}) (F : X.Modules) (x : X)
    (U : X.Opens) (hx : x ∈ U)
    (s : Γ(moduleCup_godementObject X (moduleCup_godementObject X F), U)) :
    (proj X F x).app U ((moduleCup_godementMultiply X F).app U s) ⟨hx⟩ =
      eval X F x ((proj X (moduleCup_godementObject X F) x).app U s ⟨hx⟩) := by
  change ((moduleCup_godementMultiply X F ≫ proj X F x).app U s) ⟨hx⟩ = _
  simp only [moduleCup_godementMultiply, proj, Pi.lift_comp_π, Hom.comp_app,
    ConcreteCategory.comp_apply]
  erw [toSkyscraper_app_apply]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  erw [skyscraperStalkEval_germ]
  rfl

private theorem eval_stalk_lift {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (x : Y) (s : (moduleCup_godementObject X F).presheaf.stalk (f x)) :
    eval Y G x (stalk f (lift f q) x s) = stalk f q x (eval X F (f x) s) := by
  obtain ⟨U, hx, s, rfl⟩ := (moduleCup_godementObject X F).presheaf.exists_germ_eq s
  rw [stalk_germ, eval_germ, eval_germ, lift_apply]

private theorem lift_multiply {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G) :
    moduleCup_godementMultiply X F ≫ lift f q =
      lift f (lift f q) ≫ (pushforward f).map (moduleCup_godementMultiply Y G) := by
  apply target_ext f G
  intro x
  apply hom_ext
  intro U
  ext s
  apply SkyscraperSections.ext
  intro hx
  change (proj Y G x).app (f ⁻¹ᵁ U)
    ((lift f q).app U ((moduleCup_godementMultiply X F).app U s)) ⟨hx⟩ =
    (proj Y G x).app (f ⁻¹ᵁ U)
      ((moduleCup_godementMultiply Y G).app (f ⁻¹ᵁ U)
        ((lift f (lift f q)).app U s)) ⟨hx⟩
  rw [lift_apply, multiply_apply, multiply_apply, lift_apply, eval_stalk_lift]

private def iterate {X Y : Scheme.{v}} (f : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (q : F ⟶ (pushforward f).obj G) : (n : ℕ) →
      (moduleCup_godementIterate X F n ⟶
        (pushforward f).obj (moduleCup_godementIterate Y G n))
  | 0 => q
  | n + 1 => lift f (iterate f q n)

private theorem iterate_insert {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (n : ℕ) (i : Fin (n + 1)) :
    moduleCup_godementInsert X F n i ≫ iterate f q (n + 1) =
      iterate f q n ≫ (pushforward f).map (moduleCup_godementInsert Y G n i) := by
  induction n with
  | zero => exact lift_unit f q
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [moduleCup_godementInsert, Fin.val_zero, ↓reduceDIte]
      exact lift_unit f (iterate f q (n + 1))
    · have hs (Z : Scheme.{v}) (H : Z.Modules) :
          moduleCup_godementInsert Z H (n + 1) j.succ =
            moduleCup_godementMap Z (moduleCup_godementInsert Z H n j) := by
        simp [moduleCup_godementInsert, Fin.val_succ]
      rw [hs, hs]
      change moduleCup_godementMap X (moduleCup_godementInsert X F n j) ≫
          lift f (iterate f q (n + 1)) =
        lift f (iterate f q n) ≫
          (pushforward f).map (moduleCup_godementMap Y (moduleCup_godementInsert Y G n j))
      rw [← lift_precomp, ih, lift_postcomp]

private theorem iterate_collapse {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (n : ℕ) (i : Fin (n + 1)) :
    moduleCup_godementCollapse X F n i ≫ iterate f q (n + 1) =
      iterate f q (n + 2) ≫ (pushforward f).map (moduleCup_godementCollapse Y G n i) := by
  induction n with
  | zero => exact lift_multiply f q
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [moduleCup_godementCollapse, Fin.val_zero, ↓reduceDIte]
      exact lift_multiply f (iterate f q (n + 1))
    · have hs (Z : Scheme.{v}) (H : Z.Modules) :
          moduleCup_godementCollapse Z H (n + 1) j.succ =
            moduleCup_godementMap Z (moduleCup_godementCollapse Z H n j) := by
        simp [moduleCup_godementCollapse, Fin.val_succ]
      rw [hs, hs]
      change moduleCup_godementMap X (moduleCup_godementCollapse X F n j) ≫
          lift f (iterate f q (n + 1)) =
        lift f (iterate f q (n + 2)) ≫
          (pushforward f).map (moduleCup_godementMap Y (moduleCup_godementCollapse Y G n j))
      rw [← lift_precomp, ih, lift_postcomp]

private theorem modelMap {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (A : CosimplicialObject X.Modules) (B : CosimplicialObject Y.Modules)
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
      moduleCup_cosimplicialComplex X A)
    (b : (CochainComplex.singleFunctor Y.Modules 0).obj G ⟶
      moduleCup_cosimplicialComplex Y B)
    (hA : ModuleCupGodementModel X F A a) (hB : ModuleCupGodementModel Y G B b)
    (sA : ModuleCupGodementCodegeneracies X F A)
    (sB : ModuleCupGodementCodegeneracies Y G B) :
    ∃ g : A ⟶ B ⋙ pushforward f, ∀ n : SimplexCategory,
      g.app n = eqToHom (hA.choose n.len) ≫ iterate f q (n.len + 1) ≫
        (pushforward f).map (eqToHom (hB.choose n.len).symm) := by
  let eA := hA.choose
  let eB := hB.choose
  have hAδ := hA.choose_spec.1
  have hBδ := hB.choose_spec.1
  have hAσ := (show sA.choose = eA from Subsingleton.elim _ _) ▸ sA.choose_spec
  have hBσ := (show sB.choose = eB from Subsingleton.elim _ _) ▸ sB.choose_spec
  let app : ∀ n : SimplexCategory, A.obj n ⟶ (B ⋙ pushforward f).obj n :=
    fun n ↦ eqToHom (eA n.len) ≫ iterate f q (n.len + 1) ≫
      (pushforward f).map (eqToHom (eB n.len).symm)
  have hδ (n : ℕ) (i : Fin (n + 2)) :
      (MorphismProperty.naturalityProperty app) (SimplexCategory.δ i) := by
    dsimp [MorphismProperty.naturalityProperty, app]
    apply (cancel_mono ((pushforward f).map (eqToHom (eB (n + 1))))).1
    simp only [Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl]
    erw [CategoryTheory.Functor.map_id]
    simp only [Category.comp_id]
    erw [← hBδ n i]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    erw [← hAδ n i]
    simp only [Category.assoc]
    simpa only [Category.assoc] using congrArg (fun z ↦ eqToHom (eA n) ≫ z)
      (iterate_insert f q (n + 1) i)
  have hσ (n : ℕ) (i : Fin (n + 1)) :
      (MorphismProperty.naturalityProperty app) (SimplexCategory.σ i) := by
    dsimp [MorphismProperty.naturalityProperty, app]
    apply (cancel_mono ((pushforward f).map (eqToHom (eB n)))).1
    simp only [Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl]
    erw [CategoryTheory.Functor.map_id]
    simp only [Category.comp_id]
    erw [← hBσ n i]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    erw [← hAσ n i]
    simp only [Category.assoc]
    simpa only [Category.assoc] using congrArg (fun z ↦ eqToHom (eA (n + 1)) ≫ z)
      (iterate_collapse f q n i)
  have hnat := SimplexCategory.morphismProperty_eq_top
    (MorphismProperty.naturalityProperty app) (fun {_} ↦ hδ _) (fun {_} ↦ hσ _)
  exact ⟨{ app := app
           naturality := fun _ _ g ↦ by
             have h : (MorphismProperty.naturalityProperty app) g := by rw [hnat]; trivial
             exact h }, fun _ ↦ rfl⟩

private theorem modelMap_augmentation {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (A : CosimplicialObject X.Modules) (B : CosimplicialObject Y.Modules)
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
      moduleCup_cosimplicialComplex X A)
    (b : (CochainComplex.singleFunctor Y.Modules 0).obj G ⟶
      moduleCup_cosimplicialComplex Y B)
    (hA : ModuleCupGodementModel X F A a) (hB : ModuleCupGodementModel Y G B b)
    (g : A ⟶ B ⋙ pushforward f)
    (hg : ∀ n : SimplexCategory,
      g.app n = eqToHom (hA.choose n.len) ≫ iterate f q (n.len + 1) ≫
        (pushforward f).map (eqToHom (hB.choose n.len).symm)) :
    a.f 0 ≫ (moduleCup_cosimplicialZeroIso X A).hom ≫ g.app ⦋0⦌ =
      q ≫ (pushforward f).map (b.f 0 ≫ (moduleCup_cosimplicialZeroIso Y B).hom) := by
  apply (cancel_mono ((pushforward f).map (eqToHom (hB.choose 0)))).1
  rw [hg]
  simp only [Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.comp_id]
  have ha := hA.choose_spec.2
  have hb := hB.choose_spec.2
  change a.f 0 ≫ (moduleCup_cosimplicialZeroIso X A).hom ≫
    eqToHom (hA.choose 0) ≫ iterate f q 1 =
    q ≫ (pushforward f).map
      (b.f 0 ≫ (moduleCup_cosimplicialZeroIso Y B).hom ≫ eqToHom (hB.choose 0))
  erw [hb]
  rw [← Category.assoc, ← Category.assoc]
  erw [ha]
  change (𝟙 F ≫ moduleCup_godementUnit X F) ≫ lift f q =
    q ≫ (pushforward f).map (𝟙 G ≫ moduleCup_godementUnit Y G)
  simpa using lift_unit f q

end FMap

end
end AlgebraicGeometry.Scheme.Modules

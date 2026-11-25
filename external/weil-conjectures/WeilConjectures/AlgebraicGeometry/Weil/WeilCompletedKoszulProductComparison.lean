/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulRoosComparison
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Transporting the finite Koszul comparison through products and signed fibers

Source: Stacks Project, Tag 0A0E and sites-cohomology.tex Tag 0941.
(blueprint: lem-weil-pbc-completed-koszul-product-comparison).

All product preservation, cone signs and the precise zero-homotopy unit are proved here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
universe u v c z
namespace AlgebraicGeometry.Scheme
section FiberTransport
set_option backward.defeqAttrib.useBackward true
variable {B : Type u} [Category.{v} B] [Abelian B]
variable {K L M : CochainComplex B ℤ}

private def signIso (f : K ⟶ L) : mappingCocone (-f) ≅ mappingCocone f := by
  let a : K ≅ K := ⟨𝟙 _, 𝟙 _, by simp, by simp⟩
  let b : L ≅ L := ⟨-𝟙 _, -𝟙 _, by simp, by simp⟩
  let e : mappingCone (-f) ≅ mappingCone f :=
    { hom := mappingCone.map (-f) f a.hom b.hom (by simp [a, b])
      inv := mappingCone.map f (-f) a.inv b.inv (by simp [a, b])
      hom_inv_id := by
        rw [← mappingCone.map_comp]
        simp only [a, b, Category.id_comp, Preadditive.neg_comp, Preadditive.comp_neg,
          neg_neg]
        exact mappingCone.map_id _
      inv_hom_id := by
        rw [← mappingCone.map_comp]
        simp only [a, b, Category.id_comp, Preadditive.neg_comp, Preadditive.comp_neg,
          neg_neg]
        exact mappingCone.map_id _ }
  exact (CategoryTheory.shiftFunctor _ (-1 : ℤ)).mapIso e

private theorem signIso_lift (f : K ⟶ L) (α : M ⟶ K) (h : α ≫ f = 0) :
    mappingCocone.lift (-f) α 0 (by simp [h]) ≫ (signIso f).hom =
      mappingCocone.lift f α 0 (by simp [h]) := by
  ext p
  apply mappingCone.ext_to f (p + -1) p (by omega)
  · simp [signIso, mappingCocone.lift, mappingCocone.liftCocycle,
      mappingCocone.liftCochain, HomComplex.Cochain.rightShift_v,
      mappingCone.map, mappingCone.desc,
      mappingCone.liftCochain, mappingCone.descCochain,
      HomComplex.Cochain.comp_v, Category.assoc]
  · simp [signIso, mappingCocone.lift, mappingCocone.liftCocycle,
      mappingCocone.liftCochain, HomComplex.Cochain.rightShift_v,
      mappingCone.map, mappingCone.desc,
      mappingCone.liftCochain, mappingCone.descCochain,
      HomComplex.Cochain.comp_v, Category.assoc]

variable {K' L' : CochainComplex B ℤ}

private def arrowFiberIso (f : K ⟶ L) (g : K' ⟶ L') (a : K ≅ K') (b : L ≅ L')
    (h : f ≫ b.hom = a.hom ≫ g) : mappingCocone f ≅ mappingCocone g := by
  have hi : g ≫ b.inv = a.inv ≫ f := by
    apply (cancel_mono b.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h, Iso.inv_hom_id_assoc]
  let e : mappingCone f ≅ mappingCone g :=
    { hom := mappingCone.map f g a.hom b.hom h
      inv := mappingCone.map g f a.inv b.inv hi
      hom_inv_id := by
        rw [← mappingCone.map_comp]
        simp only [Iso.hom_inv_id]
        exact mappingCone.map_id _
      inv_hom_id := by
        rw [← mappingCone.map_comp]
        simp only [Iso.inv_hom_id]
        exact mappingCone.map_id _ }
  exact (CategoryTheory.shiftFunctor _ (-1 : ℤ)).mapIso e

private theorem arrowFiberIso_lift (f : K ⟶ L) (g : K' ⟶ L') (a : K ≅ K') (b : L ≅ L')
    (hc : f ≫ b.hom = a.hom ≫ g) (α : M ⟶ K) (h : α ≫ f = 0)
    (hg : (α ≫ a.hom) ≫ g = 0) :
    mappingCocone.lift f α 0 (by simp [h]) ≫ (arrowFiberIso f g a b hc).hom =
      mappingCocone.lift g (α ≫ a.hom) 0 (by simp [hg]) := by
  ext p
  apply mappingCone.ext_to g (p + -1) p (by omega)
  · simp [arrowFiberIso, mappingCocone.lift, mappingCocone.liftCocycle,
      mappingCocone.liftCochain, HomComplex.Cochain.rightShift_v,
      mappingCone.map, mappingCone.desc, mappingCone.liftCochain,
      mappingCone.descCochain, HomComplex.Cochain.comp_v, Category.assoc]
  · simp [arrowFiberIso, mappingCocone.lift, mappingCocone.liftCocycle,
      mappingCocone.liftCochain, HomComplex.Cochain.rightShift_v,
      mappingCone.map, mappingCone.desc, mappingCone.liftCochain,
      mappingCone.descCochain, HomComplex.Cochain.comp_v, Category.assoc]

universe u' v'
variable {B' : Type u'} [Category.{v'} B'] [Abelian B']

private def mapFiberIso (f : K ⟶ L) (G : B ⥤ B') [G.Additive] :
    (G.mapHomologicalComplex (.up ℤ)).obj (mappingCocone f) ≅
      mappingCocone ((G.mapHomologicalComplex (.up ℤ)).map f) :=
  ((G.mapHomologicalComplex (.up ℤ)).commShiftIso (-1)).app (mappingCone f) ≪≫
    (CategoryTheory.shiftFunctor _ (-1 : ℤ)).mapIso
      (mappingCone.mapHomologicalComplexIso f G)

private theorem mapFiberIso_lift (f : K ⟶ L) (G : B ⥤ B') [G.Additive] (α : M ⟶ K) (h : α ≫ f = 0) :
    (G.mapHomologicalComplex (.up ℤ)).map (mappingCocone.lift f α 0 (by simp [h])) ≫
      (mapFiberIso f G).hom =
      mappingCocone.lift ((G.mapHomologicalComplex (.up ℤ)).map f)
        ((G.mapHomologicalComplex (.up ℤ)).map α) 0
        (by simp [← Functor.map_comp, h]) := by
  have hcomp (p : ℤ) : (mapFiberIso f G).hom.f p =
      (mappingCone.mapHomologicalComplexXIso' f G (p + -1) p (by omega)).hom := by
    change 𝟙 _ ≫ (mappingCone.mapHomologicalComplexXIso f G (p + -1)).hom = _
    rw [Category.id_comp, mappingCone.mapHomologicalComplexXIso_eq f G (p + -1) p (by omega)]
  apply HomologicalComplex.hom_ext
  intro p
  change G.map ((mappingCocone.lift f α 0 (by simp [h])).f p) ≫
    (mapFiberIso f G).hom.f p = _
  rw [hcomp]
  apply mappingCone.ext_to ((G.mapHomologicalComplex (.up ℤ)).map f)
    (p + -1) p (by omega)
  · simp [mappingCocone.lift, mappingCocone.liftCocycle,
      mappingCocone.liftCochain, HomComplex.Cochain.rightShift_v,
      mappingCone.mapHomologicalComplexXIso', mappingCone.liftCochain,
      -Functor.map_comp, ← G.map_comp, Category.assoc]
  · simp [mappingCocone.lift, mappingCocone.liftCocycle,
      mappingCocone.liftCochain, HomComplex.Cochain.rightShift_v,
      mappingCone.mapHomologicalComplexXIso', mappingCone.liftCochain,
      -Functor.map_comp, ← G.map_comp, Category.assoc]

variable [HasCountableProducts B] [HasCountableProducts B']

private def productTransportIso (G : B ⥤ B') [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G]
    (K : ℕ → CochainComplex B ℤ) (T : CochainComplex (ℕᵒᵖ ⥤ B') ℤ)
    (e : ∀ n, (G.mapHomologicalComplex (.up ℤ)).obj (K n) ≅ T.asFunctor.obj (op n)) :
    (G.mapHomologicalComplex (.up ℤ)).obj (∏ᶜ K) ≅ roosP T :=
  asIso (piComparison (G.mapHomologicalComplex (.up ℤ)) K) ≪≫ Pi.mapIso e

private theorem productTransportIso_hom_π (G : B ⥤ B') [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G]
    (K : ℕ → CochainComplex B ℤ) (T : CochainComplex (ℕᵒᵖ ⥤ B') ℤ)
    (e : ∀ n, (G.mapHomologicalComplex (.up ℤ)).obj (K n) ≅ T.asFunctor.obj (op n))
    (n : ℕ) :
    (productTransportIso G K T e).hom ≫ Pi.π _ n =
      (G.mapHomologicalComplex (.up ℤ)).map (Pi.π K n) ≫ (e n).hom := by
  simp [productTransportIso, Category.assoc]

private theorem productTransportIso_square (G : B ⥤ B') [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G]
    (K : ℕ → CochainComplex B ℤ) (f : ∀ n, K (n + 1) ⟶ K n)
    (T : CochainComplex (ℕᵒᵖ ⥤ B') ℤ)
    (e : ∀ n, (G.mapHomologicalComplex (.up ℤ)).obj (K n) ≅ T.asFunctor.obj (op n))
    (he : ∀ n, (G.mapHomologicalComplex (.up ℤ)).map (f n) ≫ (e n).hom =
      (e (n + 1)).hom ≫ T.asFunctor.map (homOfLE (Nat.le_succ n)).op) :
    (G.mapHomologicalComplex (.up ℤ)).map (towerTransitionEndomorphism f) ≫
      (productTransportIso G K T e).hom =
    (productTransportIso G K T e).hom ≫ roosU T := by
  let H := G.mapHomologicalComplex (.up ℤ)
  let p := productTransportIso G K T e
  apply Pi.hom_ext
  intro n
  have h₁ := (towerTransitionEndomorphism_eq_iff f
    (towerTransitionEndomorphism f)).mp rfl n
  have h₂ := (towerTransitionEndomorphism_eq_iff
    (fun n ↦ T.asFunctor.map (homOfLE (Nat.le_succ n)).op) (roosU T)).mp rfl n
  simp only [Category.assoc]
  rw [productTransportIso_hom_π, ← H.map_comp_assoc, h₁]
  rw [H.map_sub, Preadditive.sub_comp, H.map_comp]
  rw [h₂]
  simp only [Preadditive.comp_sub, ← Category.assoc, productTransportIso_hom_π]
  rw [Category.assoc, he]
  simp only [Category.assoc]
  rfl

variable {M' : CochainComplex B ℤ}

omit [HasCountableProducts B] in
private theorem lift_precomp (f : K ⟶ L) (α : M ⟶ K) (h : α ≫ f = 0) (δ : M' ⟶ M) :
    δ ≫ mappingCocone.lift f α 0 (by simp [h]) =
      mappingCocone.lift f (δ ≫ α) 0 (by simp [Category.assoc, h]) := by
  ext p
  apply mappingCone.ext_to f (p + -1) p (by omega)
  · simp [mappingCocone.lift, mappingCocone.liftCocycle,
      mappingCocone.liftCochain, HomComplex.Cochain.rightShift_v,
      mappingCone.liftCochain, Category.assoc]
  · simp [mappingCocone.lift, mappingCocone.liftCocycle,
      mappingCocone.liftCochain, HomComplex.Cochain.rightShift_v,
      mappingCone.liftCochain, Category.assoc]

private def fiberTransportIso (G : B ⥤ B') [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G]
    (K : ℕ → CochainComplex B ℤ) (f : ∀ n, K (n + 1) ⟶ K n)
    (T : CochainComplex (ℕᵒᵖ ⥤ B') ℤ)
    (e : ∀ n, (G.mapHomologicalComplex (.up ℤ)).obj (K n) ≅ T.asFunctor.obj (op n))
    (he : ∀ n, (G.mapHomologicalComplex (.up ℤ)).map (f n) ≫ (e n).hom =
      (e (n + 1)).hom ≫ T.asFunctor.map (homOfLE (Nat.le_succ n)).op) :
    (G.mapHomologicalComplex (.up ℤ)).obj
      (mappingCocone (-towerTransitionEndomorphism f)) ≅ roosF.obj T :=
  let H := G.mapHomologicalComplex (.up ℤ)
  let p := productTransportIso G K T e
  mapFiberIso (-towerTransitionEndomorphism f) G ≪≫
    arrowFiberIso (H.map (-towerTransitionEndomorphism f)) (-roosU T) p p (by
      simpa only [Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg]
        using congrArg Neg.neg (productTransportIso_square G K f T e he)) ≪≫
      signIso (roosU T)

private theorem fiberTransportIso_lift (G : B ⥤ B') [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G]
    (K : ℕ → CochainComplex B ℤ) (f : ∀ n, K (n + 1) ⟶ K n)
    (T : CochainComplex (ℕᵒᵖ ⥤ B') ℤ)
    (e : ∀ n, (G.mapHomologicalComplex (.up ℤ)).obj (K n) ≅ T.asFunctor.obj (op n))
    (he : ∀ n, (G.mapHomologicalComplex (.up ℤ)).map (f n) ≫ (e n).hom =
      (e (n + 1)).hom ≫ T.asFunctor.map (homOfLE (Nat.le_succ n)).op)
    (P : CochainComplex B ℤ) (α : P ⟶ ∏ᶜ K)
    (h : α ≫ towerTransitionEndomorphism f = 0) :
    let H := G.mapHomologicalComplex (.up ℤ)
    let β := H.map α ≫ (productTransportIso G K T e).hom
    ∃ hβ : β ≫ roosU T = 0,
      H.map (mappingCocone.lift (-towerTransitionEndomorphism f) α 0 (by simp [h])) ≫
        (fiberTransportIso G K f T e he).hom = roosLift β hβ := by
  let H := G.mapHomologicalComplex (.up ℤ)
  let p := productTransportIso G K T e
  have hβ : (H.map α ≫ p.hom) ≫ roosU T = 0 := by
    rw [Category.assoc, ← productTransportIso_square G K f T e he]
    rw [← Category.assoc, ← H.map_comp, h, H.map_zero, zero_comp]
  refine ⟨hβ, ?_⟩
  dsimp only [fiberTransportIso, Iso.trans_hom]
  rw [← Category.assoc, ← Category.assoc, mapFiberIso_lift _ _ _ (by simp [h])]
  have hs : H.map α ≫ H.map (-towerTransitionEndomorphism f) = 0 := by
    rw [← H.map_comp]
    simp [h]
  have ht : (H.map α ≫ p.hom) ≫ (-roosU T) = 0 := by simp [hβ]
  erw [arrowFiberIso_lift _ _ _ _ _ _ hs ht]
  exact signIso_lift _ _ hβ

end FiberTransport
set_option backward.defeqAttrib.useBackward false

private theorem restriction_preserves_limits
    {S : Type c} [Category.{v} S] {J : GrothendieckTopology S}
    {R R' : Sheaf J RingCat.{z}} (φ : R ⟶ R')
    [HasSheafify J AddCommGrpCat.{z}] [J.WEqualsLocallyBijective AddCommGrpCat.{z}] :
    PreservesLimitsOfSize.{z, z} (SheafOfModules.restrictScalars.{z} φ) := by
  have h (A : Sheaf J RingCat.{z}) :
      PreservesLimitsOfSize.{z, z} (SheafOfModules.toSheaf.{z} A) := by
    constructor
    intro K _
    exact ((moduleSheaves_colimits_forgetful A).2.2.2.2.2 K).1
  have := h R
  have := h R'
  have : ReflectsLimitsOfSize.{z, z} (SheafOfModules.toSheaf.{z} R) :=
    reflectsLimits_of_reflectsIsomorphisms
  have : PreservesLimitsOfSize.{z, z}
      (SheafOfModules.restrictScalars.{z} φ ⋙ SheafOfModules.toSheaf.{z} R) :=
    inferInstanceAs (PreservesLimitsOfSize.{z, z} (SheafOfModules.toSheaf.{z} R'))
  exact preservesLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{z} R)

private theorem zeroLift_congr {B : Type*} [Category* B] [Abelian B]
    {K L M : CochainComplex B ℤ} (f : K ⟶ L) (α β : M ⟶ K)
    (hα : α ≫ f = 0) (hβ : β ≫ f = 0) (h : α = β) :
    mappingCocone.lift f α 0
      (by rw [HomComplex.δ_zero, zero_add, hα, HomComplex.Cochain.ofHom_zero]) =
    mappingCocone.lift f β 0
      (by rw [HomComplex.δ_zero, zero_add, hβ, HomComplex.Cochain.ofHom_zero]) := by
  subst β
  rfl

private theorem termwiseIso_inv_π {B : Type*} [Category* B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ B] (T : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (m : ℕᵒᵖ) :
    (completedKoszulTermwiseLimitIso.app T).inv ≫ limit.π T.asFunctor m =
      (HomologicalComplex.coneOfHasLimitEval T.asFunctor).π.app m :=
  limit.isoLimitCone_inv_π
    ⟨HomologicalComplex.coneOfHasLimitEval T.asFunctor,
      HomologicalComplex.isLimitConeOfHasLimitEval T.asFunctor⟩ m

private theorem koszul_roos_augment_unit {S : Type v} [SmallCategory S]
    {J : GrothendieckTopology S} (O : Sheaf J CommRingCat.{v})
    (r : ℕ) (b : Fin r → (O.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (N : ringedSiteComplex O)
    (γ : ∀ m : ℕ, N ⟶ (ringedKoszulTensorTowerComplex O r b N).asFunctor.obj (op m))
    (hγ : ∀ m, γ (m + 1) ≫ (ringedKoszulTensorTowerComplex O r b N).asFunctor.map
      (homOfLE (Nat.le_succ m)).op = γ m)
    (hγf : ∀ m q, (γ m).f q = (ringedKoszulTensorUnitComponent O r b N (op m)).f q) :
    roosAugment γ hγ = ringedKoszulLimitUnit O r b N ≫
      (completedKoszulTermwiseLimitIso.app (ringedKoszulTensorTowerComplex O r b N)).inv ≫
        roosι (ringedKoszulTensorTowerComplex O r b N) := by
  let T := ringedKoszulTensorTowerComplex O r b N
  rw [roosAugment_eq γ hγ, ← Category.assoc]
  apply congrArg (fun t : N ⟶ limit T.asFunctor ↦ t ≫ roosι T)
  apply limit.hom_ext (F := T.asFunctor)
  intro m
  rw [Category.assoc, termwiseIso_inv_π T m]
  have hleft := roosAugmentLimit_π γ hγ m.unop
  apply HomologicalComplex.hom_ext
  intro q
  have hh := congrArg (fun g ↦ g.f q) hleft
  change (roosAugmentLimit γ hγ ≫ limit.π T.asFunctor m).f q = _ at hh
  rw [hh, hγf]
  change (ringedKoszulTensorUnitComponent O r b N m).f q =
    ringedKoszulLimitUnitF O r b N q ≫ limit.π (T.X q) m
  exact (limit.lift_π (ringedKoszulTensorUnitCone O r b N q) m).symm

universe u₀ v₀ u₁ v₁ u₂ v₂

private theorem composedFiberComparison
    {B₀ : Type u₀} [Category.{v₀} B₀] [Abelian B₀] [HasCountableProducts B₀]
    {B₁ : Type u₁} [Category.{v₁} B₁] [Abelian B₁]
    {B₂ : Type u₂} [Category.{v₂} B₂] [Abelian B₂] [HasCountableProducts B₂]
    (F : B₀ ⥤ B₁) [F.Additive] (G : B₁ ⥤ B₂) [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) (F ⋙ G)]
    (P : CochainComplex B₀ ℤ) (C : CochainComplex B₁ ℤ)
    (K : ℕ → CochainComplex B₀ ℤ) (f : ∀ n, K (n + 1) ⟶ K n)
    (α : P ⟶ ∏ᶜ K) (h : α ≫ towerTransitionEndomorphism f = 0)
    (δ₀ : C ⟶ (F.mapHomologicalComplex (.up ℤ)).obj P)
    (T : CochainComplex (ℕᵒᵖ ⥤ B₂) ℤ)
    (e : ∀ n, ((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj (K n) ≅
      T.asFunctor.obj (op n))
    (he : ∀ n, ((F ⋙ G).mapHomologicalComplex (.up ℤ)).map (f n) ≫ (e n).hom =
      (e (n + 1)).hom ≫ T.asFunctor.map (homOfLE (Nat.le_succ n)).op)
    (γ : ∀ n, (G.mapHomologicalComplex (.up ℤ)).obj C ⟶ T.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ T.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (hu : ∀ n q, G.map (δ₀.f q ≫ F.map ((α ≫ Pi.π K n).f q)) ≫
      (e n).hom.f q = (γ n).f q) :
    let V := mappingCocone (-towerTransitionEndomorphism f)
    ∃ ei : (G.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj V) ≅ roosF.obj T,
      (G.mapHomologicalComplex (.up ℤ)).map
        (δ₀ ≫ (F.mapHomologicalComplex (.up ℤ)).map
          (mappingCocone.lift (-towerTransitionEndomorphism f) α 0 (by simp [h]))) ≫
            ei.hom = roosAugment γ hγ := by
  let FC := F.mapHomologicalComplex (.up ℤ)
  let GC := G.mapHomologicalComplex (.up ℤ)
  let HC := (F ⋙ G).mapHomologicalComplex (.up ℤ)
  let μ : FC ⋙ GC ≅ HC :=
    Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)
  let δ := GC.map δ₀ ≫ μ.hom.app P
  let V := mappingCocone (-towerTransitionEndomorphism f)
  let u := mappingCocone.lift (-towerTransitionEndomorphism f) α 0 (by simp [h])
  let ei := fiberTransportIso (F ⋙ G) K f T e he
  refine ⟨μ.app V ≪≫ ei, ?_⟩
  obtain ⟨hβ, hunit⟩ := fiberTransportIso_lift (F ⋙ G) K f T e he P α h
  have hc : GC.map (δ₀ ≫ FC.map u) ≫ μ.hom.app V = δ ≫ HC.map u := by
    rw [GC.map_comp, Category.assoc]
    exact (congrArg (fun t ↦ GC.map δ₀ ≫ t) (μ.hom.naturality u)).trans
      (Category.assoc _ _ _).symm
  change GC.map (δ₀ ≫ FC.map u) ≫ (μ.hom.app V ≫ ei.hom) = _
  rw [← Category.assoc, hc, Category.assoc, hunit]
  have hβeq : δ ≫ (HC.map α ≫ (productTransportIso (F ⋙ G) K T e).hom) =
      Pi.lift γ := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, productTransportIso_hom_π]
    rw [← HC.map_comp_assoc α (Pi.π K n), Pi.lift_comp_π]
    apply HomologicalComplex.hom_ext
    intro q
    change (G.map (δ₀.f q) ≫ 𝟙 _) ≫ (G.map (F.map ((α ≫ Pi.π K n).f q)) ≫
      (e n).hom.f q) = _
    rw [Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t ↦ t ≫ (e n).hom.f q)
        (G.map_comp (δ₀.f q) (F.map ((α ≫ Pi.π K n).f q)))).symm.trans (hu n q))
  change δ ≫ mappingCocone.lift (roosU T) _ 0 _ = _
  rw [lift_precomp _ _ hβ δ]
  have hγ0 : Pi.lift γ ≫ roosU T = 0 := by
    rw [← hβeq, Category.assoc, hβ, comp_zero]
  have hα0 : (δ ≫ (HC.map α ≫ (productTransportIso (F ⋙ G) K T e).hom)) ≫ roosU T = 0 := by
    rw [Category.assoc, hβ, comp_zero]
  exact zeroLift_congr (roosU T) _ _ hα0 hγ0 hβeq

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] pbcCompletedComparison intrinsicPresentationRoundTrip
attribute [local irreducible] completedCechModulesEquiv

-- Checking the fixed coefficient and site presentations needs extra elaboration steps.
/-- The published exterior product fiber is the tensor-dual Roos fiber, with its unit.

Source: Stacks Tag 0A0E and sites-cohomology.tex Tag 0941.
(blueprint: lem-weil-pbc-completed-koszul-product-comparison).

Proof: the finite tower comparison commutes with transitions and augmentation. Backward
coefficient restriction preserves limits because the module-to-sheaf functor preserves
and reflects them; the site equivalence preserves products. Compare product projections
to conjugate 1-shift. Additive functors preserve cones and shifts. Identity on the source
and negation on the target identify the two signed cones. The zero second coordinate
of the unit survives these comparisons. Its projections are the finite augmentations,
so the ordinary-limit universal property identifies it with the asserted unit. -/
theorem completed_fiber_roos_comparison_on_complex
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
    let O := completedCechRing X d
    let G := (completedCechModulesEquiv X d).functor.mapHomologicalComplex (.up ℤ)
    let b := fun i ↦ completedCechScalar X d (a i)
    let N := G.obj C
    let T := ringedKoszulTensorTowerComplex O r b N
    ∃ e : G.obj (intrinsicCompletionComplex X d r a C) ≅ roosF.obj T,
      G.map (intrinsicCompletionComplexUnit X d r a C) ≫ e.hom =
        ringedKoszulLimitUnit O r b N ≫
          (completedKoszulTermwiseLimitIso.app T).inv ≫ roosι T := by
  classical
  let G := (completedCechModulesEquiv X d).functor
  let H := intrinsicPresentationModulesBack X d ⋙ G
  let GC := G.mapHomologicalComplex (.up ℤ)
  let BC := (intrinsicPresentationModulesBack X d).mapHomologicalComplex (.up ℤ)
  let P := (intrinsicPresentationComplex X d).obj C
  let O := completedCechRing X d
  let b := fun i ↦ completedCechScalar X d (a i)
  let N := GC.obj C
  let T := ringedKoszulTensorTowerComplex O r b N
  let K := completedKoszulTensor X (intrinsicPresentationDatum d) r a P
  let f := completedKoszulTensorTransition X (intrinsicPresentationDatum d) r a P
  let α := completedKoszulProductUnit X (intrinsicPresentationDatum d) r a P
  have : PreservesLimitsOfSize.{u + 1, u + 1} (intrinsicPresentationModulesBack X d) :=
    restriction_preserves_limits
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (pbcCompletedComparison X d).inv)
  have : PreservesLimitsOfSize.{0, 0} (intrinsicPresentationModulesBack X d) :=
    preservesSmallestLimits_of_preservesLimits _
  have : PreservesLimitsOfShape (Discrete ℕ) G := inferInstanceAs
    (PreservesLimitsOfShape (Discrete ℕ) (completedCechModulesEquiv X d).functor)
  have : PreservesLimitsOfShape (Discrete ℕ) H := inferInstanceAs
    (PreservesLimitsOfShape (Discrete ℕ) (intrinsicPresentationModulesBack X d ⋙ G))
  obtain ⟨e, he, hu⟩ := completedKoszulFiniteComparison X d r a C
  let δ₀ : C ⟶ BC.obj P :=
    { f := fun q ↦ (intrinsicPresentationRoundTrip X d).hom.app (C.X q)
      comm' := fun i j _ ↦ ((intrinsicPresentationRoundTrip X d).hom.naturality
        (C.d i j)).symm }
  have h : α ≫ towerTransitionEndomorphism f = 0 := by
    set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        have hh := completedKoszulLift_relation X (intrinsicPresentationDatum d) r a P
        have hU : completedKoszulOneSubShift X (intrinsicPresentationDatum d) r a P =
            towerTransitionEndomorphism f := rfl
        rw [hU] at hh
        have hn : α ≫ (-towerTransitionEndomorphism f) = 0 := by
          apply HomComplex.Cochain.ofHom_injective
          simpa only [HomComplex.δ_zero, zero_add,
            HomComplex.Cochain.ofHom_zero] using hh
        simpa only [Preadditive.comp_neg, neg_eq_zero] using hn
  let γ (m : ℕ) : N ⟶ T.asFunctor.obj (op m) :=
    { f := (ringedKoszulTensorUnitComponent O r b N (op m)).f
      comm' := by
        intro i j hij
        have hj : i + 1 = j := hij
        subst j
        change _ ≫ (T.d i (i + 1)).app (op m) = _
        dsimp only [T, ringedKoszulTensorTowerComplex]
        rw [CochainComplex.of_d]
        exact (ringedKoszulTensorUnitComponent O r b N (op m)).comm i (i + 1) }
  have hγ (m : ℕ) : γ (m + 1) ≫ T.asFunctor.map (homOfLE (Nat.le_succ m)).op = γ m := by
    apply HomologicalComplex.hom_ext
    intro q
    change (ringedKoszulTensorUnitComponent O r b N (op (m + 1))).f q ≫
      (T.X q).map (homOfLE (Nat.le_succ m)).op =
        (ringedKoszulTensorUnitComponent O r b N (op m)).f q
    exact (ringedKoszulTensorUnitComponent_naturality O r b N q
      (homOfLE (Nat.le_succ m)).op).symm.trans (Category.id_comp _)
  have hproj (m : ℕ) (q : ℤ) :
      G.map (δ₀.f q ≫ (intrinsicPresentationModulesBack X d).map
        ((α ≫ Pi.π K m).f q)) ≫ (e m).hom.f q = (γ m).f q := by
    rw [show α ≫ Pi.π K m =
      completedKoszulTensorUnit X (intrinsicPresentationDatum d) r a P m from Pi.lift_comp_π _ m]
    exact hu m q
  obtain ⟨ei, hei⟩ := composedFiberComparison (intrinsicPresentationModulesBack X d) G
    P C K f α h δ₀ T e he γ hγ hproj
  refine ⟨ei, ?_⟩
  change GC.map (δ₀ ≫ BC.map
    (mappingCocone.lift (-towerTransitionEndomorphism f) α 0 (by simp [h]))) ≫
      ei.hom = _
  exact hei.trans (koszul_roos_augment_unit O r b N γ hγ (fun _ _ ↦ rfl))

end AlgebraicGeometry.Scheme

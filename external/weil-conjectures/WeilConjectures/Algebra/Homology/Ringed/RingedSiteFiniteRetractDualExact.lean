/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

import all WeilConjectures.Algebra.Homology.SmoothPurity.PullbackDualFreeChart
import all WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Internal dual and exact Hom of a finite-free retract

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ, final finite-free/direct-summand
calculation, expanded in the node into dual-basis and kernel/epimorphism calculations
(blueprint: lem-sfb-ringed-site-finite-retract-dual-exact).

The coefficient universe contains both site universes, without equating them. All maps
below use the existing internal Hom. The bidual isomorphism is specified by evaluation
on every object of every slice, and its inverse by the finite dual-basis formula.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxErrors 1
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true

universe c v w

open CategoryTheory CategoryTheory.Limits Opposite

@[irreducible]
private def finiteHom_iso {D E : Type*} [Category* D] [Category* E]
    [Preadditive D] [Preadditive E] [HasFiniteBiproducts D] [HasFiniteBiproducts E]
    (H : Dᵒᵖ ⥤ E) [H.Additive] (A : D) (B : E) (e : H.obj (op A) ≅ B)
    (κ : Type*) [Fintype κ] : H.obj (op (∐ fun _ : κ ↦ A)) ≅ ⨁ fun _ : κ ↦ B :=
  H.mapIso (biproduct.isoCoproduct (fun _ : κ ↦ A)).op ≪≫
    H.opMapBiproductIso (fun _ : κ ↦ A) ≪≫ biproduct.mapIso (fun _ : κ ↦ e)

private lemma finiteHom_iso_projection {D E : Type*} [Category* D] [Category* E]
    [Preadditive D] [Preadditive E] [HasFiniteBiproducts D] [HasFiniteBiproducts E]
    (H : Dᵒᵖ ⥤ E) [H.Additive] (A : D) (B : E) (e : H.obj (op A) ≅ B)
    (κ : Type*) [Fintype κ] (j : κ) :
    (finiteHom_iso H A B e κ).hom ≫ biproduct.π (fun _ : κ ↦ B) j =
      H.map (Sigma.ι (fun _ : κ ↦ A) j).op ≫ e.hom := by
  have h : H.map (biproduct.desc (Sigma.ι (fun _ : κ ↦ A))).op ≫
      H.map (biproduct.ι (fun _ : κ ↦ A) j).op ≫ e.hom =
      H.map (Sigma.ι (fun _ : κ ↦ A) j).op ≫ e.hom := by
    rw [← Category.assoc, ← H.map_comp, ← op_comp, biproduct.ι_desc]
  simpa [finiteHom_iso, Functor.opMapBiproductIso, biproduct.uniqueUpToIso,
    Functor.opMapBicone, Category.assoc] using h

@[irreducible]
private def finiteHom_sum_iso {D E : Type*} [Category* D] [Category* E]
    [Preadditive D] [Preadditive E] [HasFiniteBiproducts D] [HasFiniteBiproducts E]
    (H : Dᵒᵖ ⥤ E) [H.Additive] (A : D) (B : E) (e : H.obj (op A) ≅ B)
    (κ : Type*) [Fintype κ] : H.obj (op (∐ fun _ : κ ↦ A)) ≅ ∐ fun _ : κ ↦ B :=
  finiteHom_iso H A B e κ ≪≫ biproduct.isoCoproduct _

set_option linter.unusedFintypeInType false in
private lemma finiteHom_coproduct_projection {E : Type*} [Category* E]
    [Preadditive E] [HasFiniteBiproducts E]
    (B : E) (κ : Type*) [Fintype κ] [DecidableEq κ] (j : κ) :
    (biproduct.isoCoproduct (fun _ : κ ↦ B)).hom ≫
      Sigma.desc (fun k : κ ↦ if k = j then 𝟙 B else 0) =
        biproduct.π (fun _ : κ ↦ B) j := by
  apply biproduct.hom_ext'
  intro k
  simp [biproduct.isoCoproduct_hom, biproduct.ι_π]

private lemma finiteHom_sum_iso_projection {D E : Type*} [Category* D] [Category* E]
    [Preadditive D] [Preadditive E] [HasFiniteBiproducts D] [HasFiniteBiproducts E]
    (H : Dᵒᵖ ⥤ E) [H.Additive] (A : D) (B : E) (e : H.obj (op A) ≅ B)
    (κ : Type*) [Fintype κ] [DecidableEq κ] (j : κ) :
    (finiteHom_sum_iso H A B e κ).hom ≫
      Sigma.desc (fun k : κ ↦ if k = j then 𝟙 B else 0) =
        H.map (Sigma.ι (fun _ : κ ↦ A) j).op ≫ e.hom := by
  unfold finiteHom_sum_iso
  dsimp only [Iso.trans_hom]
  rw [Category.assoc, finiteHom_coproduct_projection, finiteHom_iso_projection]

private lemma finiteSum_iso_natural {E : Type*} [Category* E]
    [Preadditive E] [HasFiniteBiproducts E] {X X' B B' : E}
    (κ : Type*) [Finite κ] [DecidableEq κ]
    (e : X ≅ ∐ fun _ : κ ↦ B) (e' : X' ≅ ∐ fun _ : κ ↦ B')
    (a : X ⟶ X') (f : B ⟶ B')
    (h : ∀ j : κ,
      a ≫ (e'.hom ≫ Sigma.desc (fun k : κ ↦ if k = j then 𝟙 B' else 0)) =
        (e.hom ≫ Sigma.desc (fun k : κ ↦ if k = j then 𝟙 B else 0)) ≫ f) :
    a ≫ e'.hom = e.hom ≫ Limits.Sigma.map (fun _ : κ ↦ f) := by
  apply (cancel_mono (biproduct.isoCoproduct (fun _ : κ ↦ B')).inv).1
  apply biproduct.hom_ext
  intro j
  have hp : (biproduct.isoCoproduct (fun _ : κ ↦ B')).inv ≫
      biproduct.π (fun _ : κ ↦ B') j =
      Sigma.desc (fun k : κ ↦ if k = j then 𝟙 B' else 0) := by
    apply Sigma.hom_ext
    intro k
    simp [biproduct.isoCoproduct_inv, biproduct.ι_π]
  have hm : Limits.Sigma.map (fun _ : κ ↦ f) ≫
      Sigma.desc (fun k : κ ↦ if k = j then 𝟙 B' else 0) =
      Sigma.desc (fun k : κ ↦ if k = j then 𝟙 B else 0) ≫ f := by
    apply Sigma.hom_ext
    intro k
    simp only [Sigma.ι_map_assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
    split_ifs <;> simp
  simp only [Category.assoc, hp]
  rw [hm]
  simpa only [Category.assoc] using h j

private lemma moduleSheaf_comp_apply {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {A : Sheaf J RingCat} {M N P : SheafOfModules A}
    (f : M ⟶ N) (g : N ⟶ P) (U : Cᵒᵖ) (x : M.val.obj U) :
    (f ≫ g).val.app U x = g.val.app U (f.val.app U x) := rfl

private lemma moduleSheaf_iso_inv_hom_apply {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {A : Sheaf J RingCat} {M N : SheafOfModules A}
    (e : M ≅ N) (U : Cᵒᵖ) (x : N.val.obj U) :
    e.hom.val.app U (e.inv.val.app U x) = x :=
  congrArg (fun f : N ⟶ N ↦ f.val.app U x) e.inv_hom_id

private lemma iso_conjugated_split {D : Type*} [Category* D] {A B B' : D}
    (s : A ⟶ B) (r : B ⟶ A) (h : s ≫ r = 𝟙 A) (e : B ≅ B') :
    (s ≫ e.hom) ≫ (e.inv ≫ r) = 𝟙 A := by
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h

private theorem finiteSumShortExact {D : Type*} [Category D] [Abelian D]
    [HasFiniteBiproducts D] (I : Type*) [Finite I]
    (S : ShortComplex D) (hS : S.ShortExact) :
    ∃ hz : Limits.Sigma.map (fun _ : I ↦ S.f) ≫
        Limits.Sigma.map (fun _ : I ↦ S.g) = 0,
      (ShortComplex.mk (Limits.Sigma.map (fun _ : I ↦ S.f))
        (Limits.Sigma.map (fun _ : I ↦ S.g)) hz).ShortExact := by
  have : PreservesFiniteLimits (colim (J := Discrete I) (C := D)) :=
    preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm
  let F : D ⥤ D := Functor.const (Discrete I) ⋙ colim
  have : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits F := comp_preservesFiniteColimits _ _
  have : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_initial_object (F := F)
  have ht := hS.map_of_exact F
  let e (M : D) : ∐ (fun _ : I ↦ M) ≅ F.obj M :=
    Sigma.isoColimit ((Functor.const (Discrete I)).obj M)
  have hf (M N : D) (f : M ⟶ N) :
      Limits.Sigma.map (fun _ : I ↦ f) ≫ (e N).hom = (e M).hom ≫ F.map f := by
    apply Sigma.hom_ext
    intro j
    have hM : Sigma.ι (fun _ : I ↦ M) j ≫ (e M).hom =
        colimit.ι ((Functor.const (Discrete I)).obj M) (Discrete.mk j) :=
      Sigma.ι_isoColimit_hom ((Functor.const (Discrete I)).obj M) j
    have hN : Sigma.ι (fun _ : I ↦ N) j ≫ (e N).hom =
        colimit.ι ((Functor.const (Discrete I)).obj N) (Discrete.mk j) :=
      Sigma.ι_isoColimit_hom ((Functor.const (Discrete I)).obj N) j
    rw [Sigma.ι_map_assoc,
      ← Category.assoc (Sigma.ι (fun _ : I ↦ M) j) (e M).hom, hM, hN]
    exact (colimit.ι_map ((Functor.const (Discrete I)).map f) (Discrete.mk j)).symm
  have hz : Limits.Sigma.map (fun _ : I ↦ S.f) ≫
      Limits.Sigma.map (fun _ : I ↦ S.g) = 0 := by
    apply (cancel_mono (e S.X₃).hom).1
    rw [Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
    have hzF := (S.map F).zero
    change F.map S.f ≫ F.map S.g = 0 at hzF
    simpa only [zero_comp, comp_zero] using congrArg ((e S.X₁).hom ≫ ·) hzF
  refine ⟨hz, ?_⟩
  let T := ShortComplex.mk (Limits.Sigma.map (fun _ : I ↦ S.f))
    (Limits.Sigma.map (fun _ : I ↦ S.g)) hz
  let eT : T ≅ S.map F :=
    ShortComplex.isoMk (e S.X₁) (e S.X₂) (e S.X₃)
      (hf S.X₁ S.X₂ S.f).symm (hf S.X₂ S.X₃ S.g).symm
  exact ShortComplex.shortExact_of_iso eT.symm ht

private lemma shortExact_retract {D : Type*} [Category D] [Abelian D]
    {A B : ShortComplex D} (s : A ⟶ B) (r : B ⟶ A) (hsr : s ≫ r = 𝟙 A)
    (hB : B.ShortExact) : A.ShortExact := by
  have h₁ : s.τ₁ ≫ r.τ₁ = 𝟙 _ := congrArg (fun f ↦ f.τ₁) hsr
  have h₃ : s.τ₃ ≫ r.τ₃ = 𝟙 _ := congrArg (fun f ↦ f.τ₃) hsr
  have : Mono s.τ₁ := mono_of_mono_fac h₁
  have : Epi r.τ₃ := epi_of_epi_fac h₃
  have := hB.mono_f
  have := hB.epi_g
  have : Mono A.f := mono_of_mono_fac s.comm₁₂.symm
  have : Epi A.g := epi_of_epi_fac r.comm₂₃
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  rw [A.exact_iff_isZero_homology]
  have hm : ShortComplex.homologyMap s ≫ ShortComplex.homologyMap r = 𝟙 _ := by
    rw [← ShortComplex.homologyMap_comp, hsr, ShortComplex.homologyMap_id]
  have : Mono (ShortComplex.homologyMap s) := mono_of_mono_fac hm
  exact IsZero.of_mono (ShortComplex.homologyMap s)
    (B.exact_iff_isZero_homology.mp hB.exact)

private theorem bifunctor_retract_shortExact {D E : Type*}
    [Category D] [HasZeroMorphisms D] [Category E] [Abelian E]
    (H : Dᵒᵖ ⥤ D ⥤ E) {M P : D} (i : M ⟶ P) (p : P ⟶ M)
    (hip : i ≫ p = 𝟙 M)
    [(H.obj (op M)).PreservesZeroMorphisms] [(H.obj (op P)).PreservesZeroMorphisms]
    (S : ShortComplex D)
    (hP : (S.map (H.obj (op P))).ShortExact) :
    (S.map (H.obj (op M))).ShortExact := by
  have hsr : H.map p.op ≫ H.map i.op = 𝟙 (H.obj (op M)) := by
    rw [← H.map_comp, ← op_comp, hip, op_id, H.map_id]
  have hs : S.mapNatTrans (H.map p.op) ≫ S.mapNatTrans (H.map i.op) =
      𝟙 (S.map (H.obj (op M))) :=
    ShortComplex.hom_ext _ _
      (congrArg (fun τ : H.obj (op M) ⟶ H.obj (op M) ↦ τ.app S.X₁) hsr)
      (congrArg (fun τ : H.obj (op M) ⟶ H.obj (op M) ↦ τ.app S.X₂) hsr)
      (congrArg (fun τ : H.obj (op M) ⟶ H.obj (op M) ↦ τ.app S.X₃) hsr)
  exact shortExact_retract (S.mapNatTrans (H.map p.op))
    (S.mapNatTrans (H.map i.op)) hs hP

private theorem bifunctor_finiteSum_shortExact {D : Type*} [Category D] [Abelian D]
    [HasFiniteBiproducts D] (H : Dᵒᵖ ⥤ D ⥤ D) {M P : D}
    (i : M ⟶ P) (p : P ⟶ M) (hip : i ≫ p = 𝟙 M)
    [(H.obj (op M)).PreservesZeroMorphisms] [(H.obj (op P)).PreservesZeroMorphisms]
    (I : Type*) [Finite I]
    (e : ∀ X : D, (H.obj (op P)).obj X ≅ ∐ fun _ : I ↦ X)
    (he : ∀ {X Y : D} (f : X ⟶ Y),
      (H.obj (op P)).map f ≫ (e Y).hom =
        (e X).hom ≫ Limits.Sigma.map (fun _ : I ↦ f))
    (S : ShortComplex D) (hS : S.ShortExact) :
    ∃ hz : (H.obj (op M)).map S.f ≫ (H.obj (op M)).map S.g = 0,
      (ShortComplex.mk ((H.obj (op M)).map S.f)
        ((H.obj (op M)).map S.g) hz).ShortExact := by
  obtain ⟨hz, hsum⟩ := finiteSumShortExact I S hS
  let eS : S.map (H.obj (op P)) ≅
      ShortComplex.mk (Limits.Sigma.map (fun _ : I ↦ S.f))
        (Limits.Sigma.map (fun _ : I ↦ S.g)) hz :=
    ShortComplex.isoMk (e S.X₁) (e S.X₂) (e S.X₃) (he S.f).symm (he S.g).symm
  refine ⟨(S.map (H.obj (op M))).zero, ?_⟩
  exact bifunctor_retract_shortExact H i p hip S
    (ShortComplex.shortExact_of_iso eS.symm hsum)

private theorem moduleSheaf_isIso_of_bijective {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {A : Sheaf J RingCat}
    {M N : SheafOfModules A} (f : M ⟶ N)
    (hf : ∀ U, Function.Bijective (f.val.app U)) : IsIso f := by
  have : IsIso ((PresheafOfModules.toPresheaf A.obj).map f.val) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).2
    exact hf U
  have : IsIso ((SheafOfModules.forget A).map f) := by
    change IsIso f.val
    exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf A.obj)
  exact isIso_of_reflects_iso f (SheafOfModules.forget A)

namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v w}]
  {R : Sheaf J CommRingCat.{max c v w}}

/-- The standard coordinate projection from the existing finite free sheaf.
Source: Stacks 08JJ, coordinate calculation
(blueprint: lem-sfb-ringed-site-finite-retract-dual-exact). -/
def finiteRetractCoordinate (n : ℕ) (j : ULift.{max c v w} (Fin n)) :
    free (R := (sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj R)
      (ULift.{max c v w} (Fin n)) ⟶
      unit ((sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj R) :=
  Sigma.desc (fun k : ULift.{max c v w} (Fin n) ↦ if k = j then 𝟙 _ else 0)

/-- The section `t_j = p(u_j)`, evaluated on any object of the site.
Source: Stacks 08JJ, dual-basis calculation
(blueprint: lem-sfb-ringed-site-finite-retract-dual-exact). -/
def finiteRetractVector {n : ℕ}
    {T : ringedSiteModules.{max c v w} ((sheafCompose J (forget₂ CommRingCat.{max c v w}
      RingCat.{max c v w})).obj R)}
    (p : free (R := (sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj R)
      (ULift.{max c v w} (Fin n)) ⟶ T)
    (j : ULift.{max c v w} (Fin n)) (U : Cᵒᵖ) : T.val.obj U :=
  (ιFree j ≫ p).val.app U (1 : R.obj.obj U)

/-- The section `λ_j = u_j^* i` of the existing internal dual, as a map on the slice.
Source: Stacks 08JJ, dual-basis calculation
(blueprint: lem-sfb-ringed-site-finite-retract-dual-exact). -/
def finiteRetractCovector {n : ℕ}
    {T : ringedSiteModules.{max c v w} ((sheafCompose J (forget₂ CommRingCat.{max c v w}
      RingCat.{max c v w})).obj R)}
    (i : T ⟶ free (R := (sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj
      R) (ULift.{max c v w} (Fin n)))
    (j : ULift.{max c v w} (Fin n)) (U : Cᵒᵖ) :
    (homObj.{max c v w, v, c, max c v w} (R := R) T (unit ((sheafCompose J (forget₂ CommRingCat.{max
      c v w} RingCat.{max c v
      w})).obj R))).val.obj U :=
  (PresheafOfModules.restrictOver R.obj U.unop).map
    (i ≫ finiteRetractCoordinate (R := R) n j).val

attribute [local instance 2000] ModuleCat.isAddCommGroup ModuleCat.isModule
  CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize SheafOfModules.instPreadditive

namespace FiniteRetractProof

variable (R)

set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat RingCat.{max c v w})).obj R

private instance (priority := 1300) proofSectionModule
    (T : SheafOfModules.{max c v w} 𝓡) (U : Cᵒᵖ) :
    Module (R.obj.obj U) (T.val.obj U) := ModuleCat.isModule (T.val.obj U)

@[irreducible]
private def unit_iso (N : SheafOfModules.{max c v w} 𝓡) :
    homObj (R := R) (unit 𝓡) N ≅ N :=
  chart_unitHomIso.{c, v, w} (R := R) N

omit [HasSheafify J AddCommGrpCat.{max c v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v w}] in
private lemma unit_iso_apply (N : SheafOfModules.{max c v w} 𝓡)
    (U : Cᵒᵖ) (φ : (homObj (R := R) (unit 𝓡) N).val.obj U) :
    (unit_iso R N).hom.val.app U φ =
      φ.app (op (Over.mk (𝟙 U.unop))) (1 : R.obj.obj U) := by
  unfold unit_iso
  exact chart_unitHomIso_hom_eval N U.unop φ

omit [HasSheafify J AddCommGrpCat.{max c v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v w}] in
private lemma homObjMap_eval {M P N : SheafOfModules.{max c v w} 𝓡}
    (a : P ⟶ M) (U : Cᵒᵖ) (φ : (homObj (R := R) M N).val.obj U) (x : P.val.obj U) :
    ((homObjMap (R := R) a (𝟙 N)).val.app U φ).app (op (Over.mk (𝟙 U.unop))) x =
      φ.app (op (Over.mk (𝟙 U.unop))) (a.val.app U x) := rfl

private noncomputable instance proofAbelian :
    Abelian (SheafOfModules.{max c v w} 𝓡) :=
  { (inferInstance : Abelian (SheafOfModules.{max c v w} 𝓡)) with
    toPreadditive := SheafOfModules.instPreadditive 𝓡 }

private def hom_contra (N : SheafOfModules.{max c v w} 𝓡) :
    (SheafOfModules.{max c v w} 𝓡)ᵒᵖ ⥤ SheafOfModules.{max c v w} 𝓡 :=
  (homFunctor R).flip.obj N

private instance proofHomContraAdditive (N : SheafOfModules.{max c v w} 𝓡) :
    (hom_contra R N).Additive where
  map_add {M M' f f'} := by
    apply hom_ext
    exact PresheafOfModules.homObjMap_add_left f.unop.val f'.unop.val (𝟙 N.val)

private noncomputable instance proofHasFiniteBiproducts :
    HasFiniteBiproducts (SheafOfModules.{max c v w} 𝓡) := by
  let : HasFiniteLimits (SheafOfModules.{max c v w} 𝓡) :=
    SheafOfModules.Finite.hasFiniteLimits 𝓡
  let : HasFiniteProducts (SheafOfModules.{max c v w} 𝓡) :=
    hasFiniteProducts_of_hasFiniteLimits _
  exact HasFiniteBiproducts.of_hasFiniteProducts

omit [HasSheafify J AddCommGrpCat.{max c v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v w}] in
private theorem unit_iso_natural {N N' : SheafOfModules.{max c v w} 𝓡} (f : N ⟶ N') :
    homObjMap (R := R) (𝟙 (unit 𝓡)) f ≫ (unit_iso R N').hom =
      (unit_iso R N).hom ≫ f := by
  apply hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext φ
  change (unit_iso R N').hom.val.app U
      ((homObjMap (R := R) (𝟙 (unit 𝓡)) f).val.app U φ) =
    f.val.app U ((unit_iso R N).hom.val.app U φ)
  rw [unit_iso_apply, unit_iso_apply]
  rfl

@[irreducible]
private def free_sum_iso (N : SheafOfModules.{max c v w} 𝓡)
    (κ : Type (max c v w)) [Fintype κ] :
    homObj (R := R) (free (R := 𝓡) κ) N ≅ ∐ fun _ : κ ↦ N :=
  finiteHom_sum_iso (hom_contra R N) (unit 𝓡) N (unit_iso R N) κ

private lemma free_sum_iso_projection (N : SheafOfModules.{max c v w} 𝓡)
    (κ : Type (max c v w)) [Fintype κ] [DecidableEq κ] (j : κ) :
    (free_sum_iso R N κ).hom ≫ Sigma.desc (fun k : κ ↦ if k = j then 𝟙 N else 0) =
      homObjMap (R := R) (ιFree j) (𝟙 N) ≫ (unit_iso R N).hom := by
  unfold free_sum_iso
  exact finiteHom_sum_iso_projection (hom_contra R N) (unit 𝓡) N (unit_iso R N) κ j

private lemma free_sum_iso_natural (κ : Type (max c v w)) [Fintype κ]
    {N N' : SheafOfModules.{max c v w} 𝓡} (f : N ⟶ N') :
    homObjMap (R := R) (𝟙 (free (R := 𝓡) κ)) f ≫ (free_sum_iso R N' κ).hom =
      (free_sum_iso R N κ).hom ≫ Limits.Sigma.map (fun _ : κ ↦ f) := by
  classical
  apply finiteSum_iso_natural κ (free_sum_iso R N κ) (free_sum_iso R N' κ)
    (homObjMap (R := R) (𝟙 (free (R := 𝓡) κ)) f) f
  intro j
  rw [free_sum_iso_projection, free_sum_iso_projection]
  rw [Category.assoc, ← unit_iso_natural R f]
  simp only [← Category.assoc, homObjMap_comp_homObjMap, Category.id_comp,
    Category.comp_id]

private lemma free_sum_iso_apply (N : SheafOfModules.{max c v w} 𝓡)
    (κ : Type (max c v w)) [Fintype κ] [DecidableEq κ]
    (U : Cᵒᵖ) (φ : (homObj (R := R) (free (R := 𝓡) κ) N).val.obj U) (j : κ) :
    ((free_sum_iso R N κ).hom ≫
      Sigma.desc (fun k : κ ↦ if k = j then 𝟙 N else 0)).val.app U φ =
      φ.app (op (Over.mk (𝟙 U.unop)))
        ((ιFree (R := 𝓡) j).val.app U (1 : R.obj.obj U)) := by
  calc
    _ = (homObjMap (R := R) (ιFree j) (𝟙 N) ≫ (unit_iso R N).hom).val.app U φ :=
      congrArg (fun f ↦ f.val.app U φ) (free_sum_iso_projection R N κ j)
    _ = (unit_iso R N).hom.val.app U
        ((homObjMap (R := R) (ιFree j) (𝟙 N)).val.app U φ) :=
      moduleSheaf_comp_apply _ _ U φ
    _ = _ := by rw [unit_iso_apply, homObjMap_eval]

private lemma coordinate_total (n : ℕ) :
    ∑ j : ULift.{max c v w} (Fin n),
      finiteRetractCoordinate (R := R) n j ≫ ιFree j = 𝟙 _ := by
  classical
  dsimp only [finiteRetractCoordinate, free, ιFree]
  apply Sigma.hom_ext
  intro k
  simp only [Preadditive.comp_sum, ← Category.assoc, Sigma.ι_comp_desc]
  simp only [ite_comp, Category.id_comp, zero_comp]
  rw [Finset.sum_ite_eq]
  simp

variable {R}

private lemma vector_natural {n : ℕ} {T : SheafOfModules.{max c v w} 𝓡}
    (p : free (R := 𝓡) (ULift.{max c v w} (Fin n)) ⟶ T)
    (j : ULift.{max c v w} (Fin n)) {U V : Cᵒᵖ} (a : U ⟶ V) :
    T.val.map a (finiteRetractVector (R := R) p j U) =
      finiteRetractVector (R := R) p j V := by
  dsimp only [finiteRetractVector]
  rw [← PresheafOfModules.naturality_apply]
  congr 1
  exact PresheafOfModules.unit_map_one
    (R := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj) a

private lemma covector_natural {n : ℕ} {T : SheafOfModules.{max c v w} 𝓡}
    (i : T ⟶ free (R := 𝓡) (ULift.{max c v w} (Fin n)))
    (j : ULift.{max c v w} (Fin n)) {U V : Cᵒᵖ} (a : U ⟶ V) :
    (homObj (R := R) T (unit 𝓡)).val.map a (finiteRetractCovector (R := R) i j U) =
      finiteRetractCovector (R := R) i j V := rfl

private lemma dual_basis {n : ℕ} {T : SheafOfModules.{max c v w} 𝓡}
    (i : T ⟶ free (R := 𝓡) (ULift.{max c v w} (Fin n)))
    (p : free (R := 𝓡) (ULift.{max c v w} (Fin n)) ⟶ T) (hip : i ≫ p = 𝟙 T)
    (U : Cᵒᵖ) (t : T.val.obj U) :
    ∑ j : ULift.{max c v w} (Fin n),
      (show R.obj.obj U from
        (finiteRetractCovector (R := R) i j U).app (op (Over.mk (𝟙 U.unop))) t) •
      finiteRetractVector (R := R) p j U = t := by
  have ht : ∑ j : ULift.{max c v w} (Fin n),
      i ≫ finiteRetractCoordinate (R := R) n j ≫ ιFree j ≫ p = 𝟙 T := by
    have hc := congrArg (fun f ↦ i ≫ f ≫ p) (coordinate_total R n)
    have hs : (∑ j : ULift.{max c v w} (Fin n),
        i ≫ finiteRetractCoordinate (R := R) n j ≫ ιFree j ≫ p) =
      i ≫ (∑ j : ULift.{max c v w} (Fin n),
        finiteRetractCoordinate (R := R) n j ≫ ιFree j) ≫ p := by
      erw [Preadditive.sum_comp, Preadditive.comp_sum]
      simp only [Category.assoc]
    exact hs.trans (hc.trans (by simpa using hip))
  let ev : (T ⟶ T) →+ T.val.obj U :=
    { toFun f := f.val.app U t, map_zero' := rfl, map_add' _ _ := rfl }
  have he : ∑ j : ULift.{max c v w} (Fin n),
      (i ≫ finiteRetractCoordinate (R := R) n j ≫ ιFree j ≫ p).val.app U t = t :=
    (map_sum ev _ _).symm.trans (congrArg ev ht)
  refine (Finset.sum_congr rfl fun j _ ↦ ?_).trans he
  dsimp only [finiteRetractCovector, finiteRetractVector]
  change (show R.obj.obj U from (i ≫ finiteRetractCoordinate (R := R) n j).val.app U t) •
      (ιFree j ≫ p).val.app U (1 : R.obj.obj U) =
    (ιFree j ≫ p).val.app U ((i ≫ finiteRetractCoordinate (R := R) n j).val.app U t)
  exact (((ιFree j ≫ p).val.app U).hom.map_smul _ (1 : R.obj.obj U)).symm.trans
    (congrArg ((ιFree j ≫ p).val.app U)
      (mul_one (show R.obj.obj U from
        (i ≫ finiteRetractCoordinate (R := R) n j).val.app U t)))

omit [HasSheafify J AddCommGrpCat.{max c v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v w}] in
private lemma local_sum_apply {M N : PresheafOfModules.{max c v w}
      (R.obj ⋙ forget₂ CommRingCat RingCat)}
    {U : C} {κ : Type*} (s : Finset κ)
    (f : κ → ((PresheafOfModules.restrictOver R.obj U).obj M ⟶
      (PresheafOfModules.restrictOver R.obj U).obj N))
    (W : (Over U)ᵒᵖ) (x : M.obj (op W.unop.left)) :
    (∑ j ∈ s, f j).app W x = ∑ j ∈ s, (f j).app W x :=
  map_sum ({ toFun f := f.app W x, map_zero' := rfl, map_add' _ _ := rfl } :
    ((PresheafOfModules.restrictOver R.obj U).obj M ⟶
      (PresheafOfModules.restrictOver R.obj U).obj N) →+ N.obj (op W.unop.left)) _ _

private lemma dual_expansion {n : ℕ} {T : SheafOfModules.{max c v w} 𝓡}
    (i : T ⟶ free (R := 𝓡) (ULift.{max c v w} (Fin n)))
    (p : free (R := 𝓡) (ULift.{max c v w} (Fin n)) ⟶ T) (hip : i ≫ p = 𝟙 T)
    (U : Cᵒᵖ) (φ : (homObj (R := R) T (unit 𝓡)).val.obj U) :
    φ = ∑ j : ULift.{max c v w} (Fin n),
      (show R.obj.obj U from φ.app (op (Over.mk (𝟙 U.unop)))
        (finiteRetractVector (R := R) p j U)) • finiteRetractCovector (R := R) i j U := by
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  rw [local_sum_apply]
  have hb := congrArg (φ.app W) (dual_basis i p hip (op W.unop.left) x).symm
  refine hb.trans ?_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, PresheafOfModules.restrictOver_smul_app_apply]
  have hn := PresheafOfModules.naturality_apply φ
    (Over.homMk W.unop.hom (Category.comp_id _) :
      W.unop ⟶ Over.mk (𝟙 U.unop)).op (finiteRetractVector (R := R) p j U)
  change φ.app W (T.val.map W.unop.hom.op (finiteRetractVector (R := R) p j U)) =
    R.obj.map W.unop.hom.op
      (φ.app (op (Over.mk (𝟙 U.unop))) (finiteRetractVector (R := R) p j U)) at hn
  rw [vector_natural] at hn
  change (show R.obj.obj (op W.unop.left) from
      (finiteRetractCovector (R := R) i j (op W.unop.left)).app
        (op (Over.mk (𝟙 W.unop.left))) x) *
      (show R.obj.obj (op W.unop.left) from
        φ.app W (finiteRetractVector (R := R) p j (op W.unop.left))) = _
  rw [hn, mul_comm]
  rfl

omit [HasSheafify J AddCommGrpCat.{max c v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v w}] in
private lemma hom_split {M P : SheafOfModules.{max c v w} 𝓡}
    (i : M ⟶ P) (p : P ⟶ M) (hip : i ≫ p = 𝟙 M)
    (F : SheafOfModules.{max c v w} 𝓡) :
    homObjMap (R := R) p (𝟙 F) ≫ homObjMap (R := R) i (𝟙 F) = 𝟙 _ := by
  simp only [homObjMap_comp_homObjMap, hip, Category.id_comp, homObjMap_id]

private lemma free_retract_split (κ : Type (max c v w)) [Fintype κ]
    {T : SheafOfModules.{max c v w} 𝓡}
    (i : T ⟶ free (R := 𝓡) κ) (p : free (R := 𝓡) κ ⟶ T) (hip : i ≫ p = 𝟙 T)
    (F : SheafOfModules.{max c v w} 𝓡) :
    (homObjMap (R := R) p (𝟙 F) ≫ (free_sum_iso R F κ).hom) ≫
      ((free_sum_iso R F κ).inv ≫ homObjMap (R := R) i (𝟙 F)) = 𝟙 _ :=
  iso_conjugated_split (homObjMap (R := R) p (𝟙 F))
    (homObjMap (R := R) i (𝟙 F)) (hom_split (R := R) i p hip F) (free_sum_iso R F κ)

omit [HasSheafify J AddCommGrpCat.{max c v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v w}] in
private instance proofHomPreservesZero (M : SheafOfModules.{max c v w} 𝓡) :
    ((homFunctor R).obj (op M)).PreservesZeroMorphisms where
  map_zero N N' := by
    apply hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext φ
    rfl

private lemma hom_exact {n : ℕ} {T : SheafOfModules.{max c v w} 𝓡}
    (i : T ⟶ free (R := 𝓡) (ULift.{max c v w} (Fin n)))
    (p : free (R := 𝓡) (ULift.{max c v w} (Fin n)) ⟶ T) (hip : i ≫ p = 𝟙 T)
    (S : ShortComplex (SheafOfModules.{max c v w} 𝓡)) (hS : S.ShortExact) :
    ∃ hz : homObjMap (R := R) (𝟙 T) S.f ≫ homObjMap (R := R) (𝟙 T) S.g = 0,
      (ShortComplex.mk (homObjMap (R := R) (𝟙 T) S.f)
        (homObjMap (R := R) (𝟙 T) S.g) hz).ShortExact := by
  classical
  let κ := ULift.{max c v w} (Fin n)
  exact bifunctor_finiteSum_shortExact (homFunctor R)
    (M := T) (P := free (R := 𝓡) κ) i p hip κ
    (fun N ↦ free_sum_iso R N κ)
    (fun {M N} f ↦ free_sum_iso_natural R κ f) S hS

private abbrev localDualSections (T : SheafOfModules.{max c v w} 𝓡) (U : Cᵒᵖ) :=
  (PresheafOfModules.restrictOver R.obj U.unop).obj T.val ⟶
      (PresheafOfModules.restrictOver R.obj U.unop).obj
        (PresheafOfModules.unit (R.obj ⋙ forget₂ CommRingCat RingCat))

@[irreducible]
private def evaluation_map (T : SheafOfModules.{max c v w} 𝓡) :
    T ⟶ homObj (R := R) (homObj (R := R) T (unit 𝓡)) (unit 𝓡) :=
  CategoryTheory.ringedSiteSheafBidual J R T (unit 𝓡)

@[irreducible]
private def evaluation_section (T : SheafOfModules.{max c v w} 𝓡)
    (U : Cᵒᵖ) (t : T.val.obj U) : localDualSections (homObj (R := R) T (unit 𝓡)) U :=
  (evaluation_map T).val.app U t

omit [HasSheafify J AddCommGrpCat.{max c v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v w}] in
private lemma evaluation_section_apply (T : SheafOfModules.{max c v w} 𝓡)
    (U : Cᵒᵖ) (t : T.val.obj U) (W : (Over U.unop)ᵒᵖ)
    (φ : (homObj (R := R) T (unit 𝓡)).val.obj (op W.unop.left)) :
    (evaluation_section T U t).app W φ =
      φ.app (op (Over.mk (𝟙 W.unop.left))) (T.val.map W.unop.hom.op t) := by
  unfold evaluation_section evaluation_map
  rfl

private lemma evaluation_inverse {n : ℕ} {T : SheafOfModules.{max c v w} 𝓡}
    (i : T ⟶ free (R := 𝓡) (ULift.{max c v w} (Fin n)))
    (p : free (R := 𝓡) (ULift.{max c v w} (Fin n)) ⟶ T) (hip : i ≫ p = 𝟙 T)
    (U : Cᵒᵖ)
    (α : localDualSections (homObj (R := R) T (unit 𝓡)) U) :
    evaluation_section T U
      (∑ j : ULift.{max c v w} (Fin n),
        (show R.obj.obj U from α.app (op (Over.mk (𝟙 U.unop)))
          (finiteRetractCovector (R := R) i j U)) • finiteRetractVector (R := R) p j U) = α := by
  apply PresheafOfModules.hom_ext
  intro W
  ext φ
  let a (j : ULift.{max c v w} (Fin n)) : R.obj.obj U :=
    α.app (op (Over.mk (𝟙 U.unop))) (finiteRetractCovector (R := R) i j U)
  let b (j : ULift.{max c v w} (Fin n)) : R.obj.obj (op W.unop.left) :=
    φ.app (op (Over.mk (𝟙 W.unop.left)))
      (finiteRetractVector (R := R) p j (op W.unop.left))
  rw [evaluation_section_apply]
  change φ.app (op (Over.mk (𝟙 W.unop.left)))
    (T.val.map W.unop.hom.op (∑ j, a j • finiteRetractVector (R := R) p j U)) = α.app W φ
  have hL : φ.app (op (Over.mk (𝟙 W.unop.left)))
      (T.val.map W.unop.hom.op (∑ j, a j • finiteRetractVector (R := R) p j U)) =
        ∑ j, R.obj.map W.unop.hom.op (a j) * b j := by
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [T.val.map_smul, map_smul, vector_natural]
    rfl
  have hR : α.app W φ = ∑ j, b j * R.obj.map W.unop.hom.op (a j) := by
    rw [dual_expansion i p hip (op W.unop.left) φ, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul]
    have hn := PresheafOfModules.naturality_apply α
      (Over.homMk W.unop.hom (Category.comp_id _) :
        W.unop ⟶ Over.mk (𝟙 U.unop)).op (finiteRetractCovector (R := R) i j U)
    change α.app W ((homObj (R := R) T (unit 𝓡)).val.map W.unop.hom.op
      (finiteRetractCovector (R := R) i j U)) = R.obj.map W.unop.hom.op (a j) at hn
    rw [covector_natural] at hn
    exact congrArg (b j * ·) hn
  rw [hL, hR]
  exact Finset.sum_congr rfl fun j _ ↦
    mul_comm (show R.obj.obj (op W.unop.left) from R.obj.map W.unop.hom.op (a j)) (b j)

private lemma evaluation_injective {n : ℕ} {T : SheafOfModules.{max c v w} 𝓡}
    (i : T ⟶ free (R := 𝓡) (ULift.{max c v w} (Fin n)))
    (p : free (R := 𝓡) (ULift.{max c v w} (Fin n)) ⟶ T) (hip : i ≫ p = 𝟙 T)
    (U : Cᵒᵖ) : Function.Injective (evaluation_section (R := R) T U) := by
  intro t t' h
  have hc (j : ULift.{max c v w} (Fin n)) :=
    congrArg (fun α : localDualSections (homObj (R := R) T (unit 𝓡)) U ↦
      α.app (op (Over.mk (𝟙 U.unop)))
      (finiteRetractCovector (R := R) i j U)) h
  have ht (x : T.val.obj U) : T.val.map (𝟙 U) x = x := by
    rw [PresheafOfModules.map_id]
    rfl
  have hc' (j : ULift.{max c v w} (Fin n)) :
      (finiteRetractCovector (R := R) i j U).app (op (Over.mk (𝟙 U.unop))) t =
      (finiteRetractCovector (R := R) i j U).app (op (Over.mk (𝟙 U.unop))) t' := by
    have h := hc j
    simp only [evaluation_section_apply] at h
    change (finiteRetractCovector (R := R) i j U).app (op (Over.mk (𝟙 U.unop)))
        (T.val.map (𝟙 U.unop).op t) =
      (finiteRetractCovector (R := R) i j U).app (op (Over.mk (𝟙 U.unop)))
        (T.val.map (𝟙 U.unop).op t') at h
    simpa only [op_id, ht] using h
  rw [← dual_basis i p hip U t, ← dual_basis i p hip U t']
  exact Finset.sum_congr rfl fun j _ ↦ congrArg (· • finiteRetractVector (R := R) p j U) (hc' j)

private lemma evaluation_bijective {n : ℕ} {T : SheafOfModules.{max c v w} 𝓡}
    (i : T ⟶ free (R := 𝓡) (ULift.{max c v w} (Fin n)))
    (p : free (R := 𝓡) (ULift.{max c v w} (Fin n)) ⟶ T) (hip : i ≫ p = 𝟙 T)
    (U : Cᵒᵖ) : Function.Bijective (evaluation_section (R := R) T U) :=
  ⟨evaluation_injective i p hip U, fun α ↦ ⟨_, evaluation_inverse i p hip U α⟩⟩

@[irreducible]
private def bidual_iso {n : ℕ} {T : SheafOfModules.{max c v w} 𝓡}
    (i : T ⟶ free (R := 𝓡) (ULift.{max c v w} (Fin n)))
    (p : free (R := 𝓡) (ULift.{max c v w} (Fin n)) ⟶ T) (hip : i ≫ p = 𝟙 T) :
    T ≅ homObj (R := R) (homObj (R := R) T (unit 𝓡)) (unit 𝓡) := by
  have : IsIso (evaluation_map T) := moduleSheaf_isIso_of_bijective _ (by
    intro U
    have h := evaluation_bijective i p hip U
    unfold evaluation_section at h
    exact h)
  exact asIso (evaluation_map T)

private lemma bidual_iso_hom_apply {n : ℕ} {T : SheafOfModules.{max c v w} 𝓡}
    (i : T ⟶ free (R := 𝓡) (ULift.{max c v w} (Fin n)))
    (p : free (R := 𝓡) (ULift.{max c v w} (Fin n)) ⟶ T) (hip : i ≫ p = 𝟙 T)
    (U : Cᵒᵖ) (t : T.val.obj U) :
    (bidual_iso i p hip).hom.val.app U t = evaluation_section T U t := by
  unfold bidual_iso evaluation_section
  rfl

private lemma bidual_iso_hom_eval {n : ℕ} {T : SheafOfModules.{max c v w} 𝓡}
    (i : T ⟶ free (R := 𝓡) (ULift.{max c v w} (Fin n)))
    (p : free (R := 𝓡) (ULift.{max c v w} (Fin n)) ⟶ T) (hip : i ≫ p = 𝟙 T)
    (U : Cᵒᵖ) (t : T.val.obj U) (W : (Over U.unop)ᵒᵖ)
    (φ : (homObj (R := R) T (unit 𝓡)).val.obj (op W.unop.left)) :
    ((bidual_iso i p hip).hom.val.app U t).app W φ =
      φ.app (op (Over.mk (𝟙 W.unop.left))) (T.val.map W.unop.hom.op t) := by
  unfold bidual_iso
  change ((evaluation_map T).val.app U t).app W φ = _
  unfold evaluation_map
  rfl

local instance restrictedUnitSectionSMul
    (T : SheafOfModules.{max c v w} 𝓡) (U : Cᵒᵖ) :
    SMul (((PresheafOfModules.restrictOver R.obj U.unop).obj (unit 𝓡).val).obj
      (op (Over.mk (𝟙 U.unop)))) (T.val.obj U) :=
  (T.val.obj U).isModule.toSMul

private lemma bidual_iso_inv_apply {n : ℕ} {T : SheafOfModules.{max c v w} 𝓡}
    (i : T ⟶ free (R := 𝓡) (ULift.{max c v w} (Fin n)))
    (p : free (R := 𝓡) (ULift.{max c v w} (Fin n)) ⟶ T) (hip : i ≫ p = 𝟙 T)
    (U : Cᵒᵖ) (α : (homObj (R := R) (homObj (R := R) T (unit 𝓡))
      (unit 𝓡)).val.obj U) :
    (bidual_iso i p hip).inv.val.app U α =
      ∑ j : ULift.{max c v w} (Fin n),
        α.app (op (Over.mk (𝟙 U.unop))) (finiteRetractCovector (R := R) i j U) •
          finiteRetractVector (R := R) p j U := by
  apply evaluation_injective (R := R) i p hip U
  have h := moduleSheaf_iso_inv_hom_apply (bidual_iso (R := R) i p hip) U α
  rw [bidual_iso_hom_apply] at h
  exact h.trans (evaluation_inverse (R := R) i p hip U α).symm

end FiniteRetractProof

open FiniteRetractProof

-- Keep coordinate constructions folded when elaborating the public interface.
attribute [local irreducible] finiteRetractCoordinate finiteRetractVector finiteRetractCovector

-- The public statement uses the library's original instances.
attribute [-instance] proofAbelian proofHomContraAdditive
  proofHasFiniteBiproducts proofSectionModule proofHomPreservesZero

/-- Internal duality, dual bases, biduality, and exact internal Hom for a finite-free retract.

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ, final two paragraphs;
sites-modules.tex, Tags 03EM and 03DA supply internal Hom and the abelian category
(blueprint: lem-sfb-ringed-site-finite-retract-dual-exact).

Proof: (1) Coordinate inclusions and projections identify the finite product of copies
of the coefficient sheaf with its coproduct. On each slice, evaluation on the standard
vectors identifies Hom from this free sheaf to F with the finite power of F. Its inverse
sends a tuple to the linear map given by its finite linear combination. These formulas
commute with restriction and postcomposition. (2) Precompose with p and i; their composite
is the identity because i followed by p is the identity. Specializing the coordinate
identification to F = R exhibits the dual as a finite-free retract. (3) Expand i(t) in
coordinates and apply p to get the dual-basis identity. Apply an arbitrary local linear
functional to this identity to expand that functional in the covectors λ_j. (4) Evaluation
is a sheaf map. The displayed sum defines its inverse: one composite is the dual-basis
identity, and the other follows from the functional expansion and commutativity of R.
(5) Associativity of composition makes the precomposition splittings natural in F.
(6) Finite powers are the constant-diagram colimit over a finite discrete category.
The finite biproduct comparison identifies this colimit functor with the limit functor,
so finite powers preserve finite limits and colimits and hence short exact sequences.
Transport this through the natural coordinate isomorphisms; epimorphisms here are
categorical, with no assertion of surjectivity on sections. (7) The natural splitting
displays the Hom(T,-) short complex as a retract of the finite-power short complex.
Its left map is monic and its right map epic by cancellation against the split maps.
(8) Applying functorial homology makes its homology a retract of the zero homology of
the finite-power complex. It is therefore zero, proving exactness of the retract.
(9) Every operation is
restriction, evaluation, composition, a finite sum or scalar multiplication. The formulas
therefore commute with passing to every localized site and with relocalization. For n=0
the splitting forces T=0, and the same proof uses empty sums. -/
theorem ringedSite_finite_retract_dual_exact
    (n : ℕ)
    (T : ringedSiteModules.{max c v w} ((sheafCompose J (forget₂ CommRingCat.{max c v w}
      RingCat.{max c v w})).obj R))
    (i : T ⟶ free (R := (sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj
      R) (ULift.{max c v w} (Fin n)))
    (p : free (R := (sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj R)
      (ULift.{max c v w} (Fin n)) ⟶ T)
    (hip : i ≫ p = 𝟙 T) :
    (∀ F : ringedSiteModules.{max c v w}
        ((sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj R),
      homObjMap.{max c v w, v, c, max c v w} (R := R) p (𝟙 F) ≫ homObjMap.{max c v w, v, c, max c v
        w} (R := R) i (𝟙 F) =
        𝟙 (homObj.{max c v w, v, c, max c v w} (R := R) T F)) ∧
    (∃ e : ∀ F : ringedSiteModules.{max c v w}
        ((sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj R),
        homObj.{max c v w, v, c, max c v w} (R := R) (free (R := (sheafCompose J (forget₂
          CommRingCat.{max c v w} RingCat.{max c
          v w})).obj R) (ULift.{max c v w} (Fin n))) F ≅
          ∐ (fun _ : ULift.{max c v w} (Fin n) ↦ F),
      (∀ (F : ringedSiteModules.{max c v w} ((sheafCompose J (forget₂ CommRingCat.{max c v w}
        RingCat.{max c v w})).obj R))
        (U : Cᵒᵖ)
        (φ : (homObj.{max c v w, v, c, max c v w} (R := R)
          (free (R := (sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj R)
            (ULift.{max c v w} (Fin n))) F).val.obj U)
        (j : ULift.{max c v w} (Fin n)),
        ((e F).hom ≫ Sigma.desc (fun k : ULift.{max c v w} (Fin n) ↦ if k = j then 𝟙 F else
          0)).val.app U φ =
          φ.app (op (Over.mk (𝟙 U.unop)))
            ((ιFree (R := (sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj
              R) j).val.app U
              (1 : R.obj.obj U))) ∧
      (∀ (F G : ringedSiteModules.{max c v w} ((sheafCompose J (forget₂ CommRingCat.{max c v w}
        RingCat.{max c v w})).obj R))
        (f : F ⟶ G),
        homObjMap.{max c v w, v, c, max c v w} (R := R) (𝟙 _) f ≫ (e G).hom =
          (e F).hom ≫ Limits.Sigma.map (fun _ : ULift.{max c v w} (Fin n) ↦ f)) ∧
      (homObjMap.{max c v w, v, c, max c v w} (R := R) p (𝟙 (unit ((sheafCompose J (forget₂
        CommRingCat.{max c v w} RingCat.{max
        c v w})).obj R))) ≫
          (e (unit ((sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj
            R))).hom) ≫
        ((e (unit ((sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj
          R))).inv ≫
          homObjMap.{max c v w, v, c, max c v w} (R := R) i (𝟙 _)) = 𝟙 _ ) ∧
    (∀ (U : Cᵒᵖ) (t : T.val.obj U),
      ∑ j : ULift.{max c v w} (Fin n),
        (@id (R.obj.obj U)
          ((finiteRetractCovector (R := R) (T := T) (n := n) i j U).app (op (Over.mk (𝟙 U.unop)))
            t)) •
          finiteRetractVector (R := R) (T := T) (n := n) p j U = t) ∧
    (∀ (U : Cᵒᵖ)
      (φ : (homObj.{max c v w, v, c, max c v w} (R := R) T (unit ((sheafCompose J (forget₂
        CommRingCat.{max c v w} RingCat.{max c
        v w})).obj R))).val.obj U),
      φ = ∑ j : ULift.{max c v w} (Fin n),
        (@id (R.obj.obj U)
          (φ.app (op (Over.mk (𝟙 U.unop))) (finiteRetractVector (R := R) (T := T) (n := n) p j U)))
            •
          finiteRetractCovector (R := R) (T := T) (n := n) i j U) ∧
    (∃ d : T ≅ homObj.{max c v w, v, c, max c v w} (R := R)
        (homObj.{max c v w, v, c, max c v w} (R := R) T (unit ((sheafCompose J (forget₂
          CommRingCat.{max c v w} RingCat.{max c v
          w})).obj R)))
        (unit ((sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj R)),
      (∀ (U : Cᵒᵖ) (t : T.val.obj U) (W : (Over U.unop)ᵒᵖ)
        (φ : (homObj.{max c v w, v, c, max c v w} (R := R) T (unit ((sheafCompose J (forget₂
          CommRingCat.{max c v w} RingCat.{max
          c v w})).obj R))).val.obj
          (op W.unop.left)),
        ((d.hom.val.app U t).app W) φ =
          φ.app (op (Over.mk (𝟙 W.unop.left))) (T.val.map W.unop.hom.op t)) ∧
      (∀ (U : Cᵒᵖ)
        (α : (homObj.{max c v w, v, c, max c v w} (R := R)
          (homObj.{max c v w, v, c, max c v w} (R := R) T (unit ((sheafCompose J (forget₂
            CommRingCat.{max c v w} RingCat.{max c
            v w})).obj R)))
          (unit ((sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj
            R))).val.obj U),
        d.inv.val.app U α = ∑ j : ULift.{max c v w} (Fin n),
          (@id (R.obj.obj U)
            (α.app (op (Over.mk (𝟙 U.unop))) (finiteRetractCovector (R := R) (T := T) (n := n) i j
              U))) •
            finiteRetractVector (R := R) (T := T) (n := n) p j U)) ∧
    (∀ S : ShortComplex
        (ringedSiteModules.{max c v w} ((sheafCompose J (forget₂ CommRingCat.{max c v w}
          RingCat.{max c v w})).obj R)),
      S.ShortExact → ∃ hzero : homObjMap.{max c v w, v, c, max c v w} (R := R) (𝟙 T) S.f ≫
        homObjMap.{max c v w, v, c, max c v w} (R := R) (𝟙 T) S.g = 0,
        (ShortComplex.mk (homObjMap.{max c v w, v, c, max c v w} (R := R) (𝟙 T) S.f) (homObjMap.{max
          c v w, v, c, max c v w} (R := R) (𝟙 T) S.g)
          hzero).ShortExact) ∧
    (∀ (U V : Cᵒᵖ) (a : U ⟶ V) (j : ULift.{max c v w} (Fin n)),
      T.val.map a (finiteRetractVector (R := R) (T := T) (n := n) p j U) = finiteRetractVector (R :=
        R) (T := T) (n := n) p j V ∧
      (homObj.{max c v w, v, c, max c v w} (R := R) T (unit ((sheafCompose J (forget₂
        CommRingCat.{max c v w} RingCat.{max c v
        w})).obj R))).val.map a
        (finiteRetractCovector (R := R) (T := T) (n := n) i j U) = finiteRetractCovector (R := R) (T
          := T) (n := n) i j V) := by
  classical
  let κ := ULift.{max c v w} (Fin n)
  have hs (F : ringedSiteModules.{max c v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
      homObjMap (R := R) p (𝟙 F) ≫ homObjMap (R := R) i (𝟙 F) = 𝟙 _ :=
    hom_split (R := R) i p hip F
  refine ⟨hs, ?_, dual_basis (R := R) i p hip, dual_expansion (R := R) i p hip, ?_, ?_, ?_⟩
  · refine ⟨fun F ↦ free_sum_iso R F κ, ?_, ?_, ?_⟩
    · intro F U φ j
      exact free_sum_iso_apply R F κ U φ j
    · intro F G f
      exact free_sum_iso_natural R κ f
    · exact free_retract_split (R := R) κ i p hip _
  · refine ⟨bidual_iso (R := R) i p hip, ?_, ?_⟩
    · intro U t W φ
      exact bidual_iso_hom_eval (R := R) i p hip U t W φ
    · intro U α
      exact bidual_iso_inv_apply (R := R) i p hip U α
  · intro S hS
    obtain ⟨hz, h⟩ := hom_exact (R := R) i p hip S hS
    exact ⟨hz, h⟩
  · intro U V a j
    exact ⟨vector_natural (R := R) p j a, covector_natural (R := R) i j a⟩

end SheafOfModules

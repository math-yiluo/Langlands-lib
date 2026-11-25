/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealizationExact
import WeilConjectures.AlgebraicGeometry.CompactAdicContinuousIdentification
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing
import all WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis

/-! # Flatness and the first quotient in the internal integral presentation

Source: Stacks Tags 093M and 099L.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

attribute [local irreducible] upperStarFromPoint

private theorem iso_hom_inv {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{u}}
    (e : R ≅ S) (U : Cᵒᵖ) (a : R.obj.obj U) :
    e.inv.hom.app U (e.hom.hom.app U a) = a :=
  ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app U) e.hom_inv_id) a

private theorem iso_inv_hom {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{u}}
    (e : R ≅ S) (U : Cᵒᵖ) (a : S.obj.obj U) :
    e.hom.hom.app U (e.inv.hom.app U a) = a :=
  iso_hom_inv e.symm U a

private theorem iso_inv_surjective {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{u}}
    (e : R ≅ S) (U : Cᵒᵖ) : Function.Surjective (e.inv.hom.app U) :=
  fun a ↦ ⟨e.hom.hom.app U a, iso_hom_inv e U a⟩

private theorem iso_hom_injective {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{u}}
    (e : R ≅ S) (U : Cᵒᵖ) : Function.Injective (e.hom.hom.app U) := by
  intro a b h
  simpa only [iso_hom_inv] using congrArg (e.inv.hom.app U) h

private theorem flat_transport {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R B R₀ B₀ : Sheaf J CommRingCat.{u}}
    (φ : R ⟶ B) (φ₀ : R₀ ⟶ B₀) (α : R ≅ R₀) (β : B ≅ B₀)
    (hc : φ ≫ β.hom = α.hom ≫ φ₀)
    (hflat : SheafOfModules.IsFlat
      ((ConstantCompletion.res φ₀).obj (SheafOfModules.unit (siteModuleRings B₀)))) :
    SheafOfModules.IsFlat
      ((ConstantCompletion.res φ).obj (SheafOfModules.unit (siteModuleRings B))) := by
  classical
  let M₀ := (ConstantCompletion.res φ₀).obj (SheafOfModules.unit (siteModuleRings B₀))
  let M := (ConstantCompletion.res φ).obj (SheafOfModules.unit (siteModuleRings B))
  have hm : SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := R₀) M₀ := by
    let := SheafOfModules.monoidalCategory R₀
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R₀ M₀).symm hflat
  have hscalar (U : Cᵒᵖ) (a : R.obj.obj U) :
      β.hom.hom.app U (φ.hom.app U a) = φ₀.hom.app U (α.hom.hom.app U a) :=
    congrArg (fun f ↦ f.hom.app U a) hc
  have hinvscalar (U : Cᵒᵖ) (a : R₀.obj.obj U) :
      β.inv.hom.app U (φ₀.hom.app U a) = φ.hom.app U (α.inv.hom.app U a) := by
    apply iso_hom_injective β U
    rw [iso_inv_hom, hscalar, iso_inv_hom]
  have hf : SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := R) M := by
    apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion.{u, u, u, u} R M
    intro U n a s hs
    let a₀ : Fin n → R₀.obj.obj (op U) := fun i ↦ α.hom.hom.app (op U) (a i)
    let s₀ : Fin n → M₀.val.obj (op U) := fun i ↦ β.hom.hom.app (op U) (s i)
    have h₀ : (∑ i, a₀ i • s₀ i) = 0 := by
      have hh := congrArg (β.hom.hom.app (op U)) hs
      rw [map_sum, map_zero] at hh
      change (∑ i, φ₀.hom.app (op U) (a₀ i) * (show B₀.obj.obj (op U) from s₀ i)) = 0
      change (∑ i, β.hom.hom.app (op U)
        (φ.hom.app (op U) (a i) * (show B.obj.obj (op U) from s i))) = 0 at hh
      simpa only [map_mul, hscalar, a₀, s₀] using hh
    obtain ⟨S, hS, hrel⟩ :=
      SheafOfModules.local_equationalCriterion_of_isFlatOnSite.{u, u, u, u} R₀ M₀ hm U n a₀ s₀ h₀
    refine ⟨S, hS, ?_⟩
    intro V f hf
    obtain ⟨k, b, t, hb, ht⟩ := hrel V f hf
    refine ⟨k, (fun i j ↦ α.inv.hom.app (op V) (b i j)),
      (fun j ↦ β.inv.hom.app (op V) (t j)), ?_, ?_⟩
    · intro i
      have hh := congrArg (β.inv.hom.app (op V)) (hb i)
      change β.inv.hom.app (op V) (B₀.obj.map f.op (s₀ i)) =
        β.inv.hom.app (op V) (∑ j, φ₀.hom.app (op V) (b i j) *
          (show B₀.obj.obj (op V) from t j)) at hh
      rw [map_sum] at hh
      have hn := ConcreteCategory.congr_hom (β.inv.hom.naturality f.op) (s₀ i)
      change β.inv.hom.app (op V) (B₀.obj.map f.op (s₀ i)) =
        B.obj.map f.op (β.inv.hom.app (op U) (s₀ i)) at hn
      rw [show β.inv.hom.app (op U) (s₀ i) = s i from iso_hom_inv β _ _] at hn
      rw [hn] at hh
      change B.obj.map f.op (s i) =
        ∑ j, φ.hom.app (op V) (α.inv.hom.app (op V) (b i j)) *
          β.inv.hom.app (op V) (t j)
      simpa only [map_mul, hinvscalar] using hh
    · intro j
      have hh := congrArg (α.inv.hom.app (op V)) (ht j)
      rw [map_sum, map_zero] at hh
      change (∑ i, R.obj.map f.op (a i) * α.inv.hom.app (op V) (b i j)) = 0
      rw [← hh]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul]
      congr 1
      have hn := ConcreteCategory.congr_hom (α.inv.hom.naturality f.op) (a₀ i)
      change α.inv.hom.app (op V) (R₀.obj.map f.op (a₀ i)) =
        R.obj.map f.op (α.inv.hom.app (op U) (a₀ i)) at hn
      rw [show α.inv.hom.app (op U) (a₀ i) = a i from iso_hom_inv α _ _] at hn
      exact hn.symm
  let := SheafOfModules.monoidalCategory R
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R M) hf

private theorem kernel_sections {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{u}}
    (q : R ⟶ S) (U : C) :
    (ConstantCompletion.kernelIdeal q).sections U = RingHom.ker (q.hom.app (op U)).hom :=
  (ConstantCompletion.kernelIdeal_existsUnique q).exists.choose_spec U

private theorem kernel_mem_transport {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S R₀ S₀ : Sheaf J CommRingCat.{u}}
    (q : R ⟶ S) (q₀ : R₀ ⟶ S₀) (α : R ≅ R₀) (γ : S ≅ S₀)
    (hq : q ≫ γ.hom = α.hom ≫ q₀) (U : C) (a : R.obj.obj (op U)) :
    a ∈ (ConstantCompletion.kernelIdeal q).sections U ↔
      α.hom.hom.app (op U) a ∈ (ConstantCompletion.kernelIdeal q₀).sections U := by
  rw [kernel_sections, kernel_sections]
  change q.hom.app (op U) a = 0 ↔ q₀.hom.app (op U) (α.hom.hom.app (op U) a) = 0
  have hc := congrArg (fun f ↦ f.hom.app (op U) a) hq
  change γ.hom.hom.app (op U) (q.hom.app (op U) a) =
    q₀.hom.app (op U) (α.hom.hom.app (op U) a) at hc
  rw [← hc, ← map_zero (γ.hom.hom.app (op U)).hom]
  exact (iso_hom_injective γ (op U)).eq_iff.symm

private theorem kernel_map_transport {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S R₀ S₀ : Sheaf J CommRingCat.{u}}
    (q : R ⟶ S) (q₀ : R₀ ⟶ S₀) (α : R ≅ R₀) (γ : S ≅ S₀)
    (hq : q ≫ γ.hom = α.hom ≫ q₀) (U : C) :
    (ConstantCompletion.kernelIdeal q).sections U =
      Ideal.map (α.inv.hom.app (op U)).hom
        ((ConstantCompletion.kernelIdeal q₀).sections U) := by
  ext a
  rw [Ideal.mem_map_iff_of_surjective _ (iso_inv_surjective α _)]
  constructor
  · intro ha
    exact ⟨α.hom.hom.app (op U) a,
      (kernel_mem_transport q q₀ α γ hq U a).mp ha, iso_hom_inv α _ a⟩
  · rintro ⟨b, hb, rfl⟩
    apply (kernel_mem_transport q q₀ α γ hq U _).mpr
    rwa [iso_inv_hom]

private theorem kernel_finiteType_transport {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {R S : Sheaf J CommRingCat.{u}} (q : R ⟶ S)
    (α : R ≅ ConstantCompletion.constant J A)
    (γ : S ≅ ConstantCompletion.finite J A I 0)
    (hq : q ≫ γ.hom = α.hom ≫ ConstantCompletion.quotient J A I 0) :
    SheafOfModules.IsFiniteType.{u, u, u} (ConstantCompletion.kernelIdeal q).module := by
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    I.fg_of_isNoetherianRing
  let b (i : Fin r) : (R.obj ⋙ forget CommRingCat).sections :=
    { val := fun U ↦ α.inv.hom.app U ((ConstantCompletion.constantSection (J := J) (a i)).val U)
      property := by
        intro U V f
        exact (ConcreteCategory.congr_hom (α.inv.hom.naturality f)
          ((ConstantCompletion.constantSection (J := J) (a i)).val U)).symm.trans
            (congrArg (α.inv.hom.app V)
              ((ConstantCompletion.constantSection (J := J) (a i)).property f)) }
  apply ConstantCompletion.ideal_finiteType_of_span
    (ConstantCompletion.kernelIdeal q) r b
  intro U
  rw [kernel_map_transport q _ α γ hq, kernel_sections,
    ((ConstantCompletion.flat_and_quotients J A I).2.2 0 U).2]
  dsimp only [ConstantCompletion.constantSection]
  erw [ConstantCompletion.span_subtype_images
    (A := A) (B := (ConstantCompletion.constant J A).obj.obj (op U))
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app (op U)).hom
    (I ^ (0 + 1)) a (by simpa only [Nat.zero_add, pow_one] using ha)]
  rw [Ideal.map_span]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, rfl⟩

private theorem kernel_extension_span {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (U : C) :
    (ConstantCompletion.kernelIdeal (ConstantCompletion.projection J A I 0)).sections U =
      Ideal.span (Set.range
        (fun a : (ConstantCompletion.kernelIdeal
          (ConstantCompletion.quotient J A I 0)).sections U ↦
            (ConstantCompletion.coefficientMap J A I).hom.app (op U) a)) := by
  rw [kernel_sections, ((ConstantCompletion.flat_and_quotients J A I).2.1 0 U).2]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    apply Ideal.subset_span
    refine ⟨⟨(ConstantCompletion.constantSection (J := J) a.val).val (op U), ?_⟩, rfl⟩
    rw [kernel_sections, ((ConstantCompletion.flat_and_quotients J A I).2.2 0 U).2]
    exact Ideal.subset_span ⟨a, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have ha := a.property
    simp only [kernel_sections,
      ((ConstantCompletion.flat_and_quotients J A I).2.2 0 U).2] at ha
    have hle : Ideal.span (Set.range (fun b : ↥(I ^ (0 + 1)) ↦
        (ConstantCompletion.constantSection (J := J) (b : A)).val (op U))) ≤
      Ideal.comap ((ConstantCompletion.coefficientMap J A I).hom.app (op U)).hom
        (Ideal.span (Set.range (fun b : ↥(I ^ (0 + 1)) ↦
          (ConstantCompletion.algebraSection (ConstantCompletion.coefficientMap J A I)
            b).val (op U)))) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨b, rfl⟩
      exact Ideal.subset_span ⟨b, rfl⟩
    exact hle ha

private def transportIdeal {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {B B₀ : Sheaf J CommRingCat.{u}}
    (β : B ≅ B₀) (K : RingedSiteIdeal B₀) : RingedSiteIdeal B where
  sections U := Ideal.comap (β.hom.hom.app (op U)).hom (K.sections U)
  restriction {U V} f a ha := by
    change β.hom.hom.app (op V) (B.obj.map f.op a) ∈ K.sections V
    have hn : B₀.obj.map f.op (β.hom.hom.app (op U) a) =
        β.hom.hom.app (op V) (B.obj.map f.op a) :=
      (ConcreteCategory.congr_hom (β.hom.hom.naturality f.op) a).symm
    rw [← hn]
    exact K.restriction f _ ha
  local_mem U a S hS ha := by
    apply K.local_mem U (β.hom.hom.app (op U) a) S hS
    intro V f hf
    have hn : B₀.obj.map f.op (β.hom.hom.app (op U) a) =
        β.hom.hom.app (op V) (B.obj.map f.op a) :=
      (ConcreteCategory.congr_hom (β.hom.hom.naturality f.op) a).symm
    erw [hn]
    exact ha V f hf

private theorem extension_span_transport {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {R B S : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (q : R ⟶ S)
    (α : R ≅ ConstantCompletion.constant J A)
    (β : B ≅ ConstantCompletion.completed J A I)
    (γ : S ≅ ConstantCompletion.finite J A I 0)
    (hc : φ ≫ β.hom = α.hom ≫ ConstantCompletion.coefficientMap J A I)
    (hq : q ≫ γ.hom = α.hom ≫ ConstantCompletion.quotient J A I 0)
    (U : C) :
    (transportIdeal β (ConstantCompletion.kernelIdeal
      (ConstantCompletion.projection J A I 0))).sections U =
      Ideal.span (Set.range (fun a : (ConstantCompletion.kernelIdeal q).sections U ↦
        φ.hom.app (op U) a)) := by
  let K := ConstantCompletion.kernelIdeal q
  let K₀ := ConstantCompletion.kernelIdeal (ConstantCompletion.quotient J A I 0)
  let p := (ConstantCompletion.projection J A I 0).hom.app (op U)
  let c := (ConstantCompletion.coefficientMap J A I).hom.app (op U)
  have hscalar (a : R.obj.obj (op U)) :
      β.hom.hom.app (op U) (φ.hom.app (op U) a) = c (α.hom.hom.app (op U) a) :=
    congrArg (fun f ↦ f.hom.app (op U) a) hc
  have hspan : Ideal.span (Set.range (fun a : K.sections U ↦
      β.hom.hom.app (op U) (φ.hom.app (op U) a))) =
      Ideal.span (Set.range (fun a : K₀.sections U ↦ c a)) := by
    congr 1
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨⟨α.hom.hom.app (op U) a,
        (kernel_mem_transport q _ α γ hq U a).mp a.property⟩, ?_⟩
      exact (hscalar a).symm
    · rintro ⟨a, rfl⟩
      refine ⟨⟨α.inv.hom.app (op U) a, ?_⟩, ?_⟩
      · apply (kernel_mem_transport q _ α γ hq U _).mpr
        simpa only [iso_inv_hom] using a.property
      · change β.hom.hom.app (op U) (φ.hom.app (op U)
          (α.inv.hom.app (op U) a.val)) = c a.val
        rw [hscalar, iso_inv_hom]
  have hspan' := kernel_extension_span (J := J) A I U
  change _ = Ideal.span (Set.range (fun a : K₀.sections U ↦ c a)) at hspan'
  have ht : Ideal.map (β.hom.hom.app (op U)).hom
      (Ideal.span (Set.range (fun a : K.sections U ↦ φ.hom.app (op U) a))) =
      (ConstantCompletion.kernelIdeal (ConstantCompletion.projection J A I 0)).sections U := by
    rw [Ideal.map_span, ← Set.range_comp', hspan, ← hspan']
  ext b
  change β.hom.hom.app (op U) b ∈
    (ConstantCompletion.kernelIdeal (ConstantCompletion.projection J A I 0)).sections U ↔
      b ∈ Ideal.span (Set.range (fun a : K.sections U ↦ φ.hom.app (op U) a))
  rw [← ht, Ideal.mem_map_iff_of_surjective _ (show Function.Surjective
    (β.hom.hom.app (op U)).hom from iso_inv_surjective β.symm _)]
  constructor
  · rintro ⟨a, ha, he⟩
    exact (iso_hom_injective β (op U) he) ▸ ha
  · intro hb
    exact ⟨b, hb, rfl⟩

private theorem quotient_transport {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {R B S : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (q : R ⟶ S)
    (α : R ≅ ConstantCompletion.constant J A)
    (β : B ≅ ConstantCompletion.completed J A I)
    (γ : S ≅ ConstantCompletion.finite J A I 0)
    (hc : φ ≫ β.hom = α.hom ≫ ConstantCompletion.coefficientMap J A I)
    (hq : q ≫ γ.hom = α.hom ≫ ConstantCompletion.quotient J A I 0) :
    (ConstantCompletion.kernelIdeal q).IsQuotientIso φ := by
  let K := ConstantCompletion.kernelIdeal q
  let p := ConstantCompletion.projection J A I 0
  let c := ConstantCompletion.coefficientMap J A I
  let q₀ := ConstantCompletion.quotient J A I 0
  let L := transportIdeal β (ConstantCompletion.kernelIdeal p)
  have he : K.extension φ = L :=
    ConstantCompletion.extension_eq_of_span φ K L
      (extension_span_transport A I φ q α β γ hc hq)
  have hscalar (U : C) (a : R.obj.obj (op U)) :
      β.hom.hom.app (op U) (φ.hom.app (op U) a) = c.hom.app (op U)
        (α.hom.hom.app (op U) a) := congrArg (fun f ↦ f.hom.app (op U) a) hc
  have hproj (U : C) (a : R.obj.obj (op U)) :
      p.hom.app (op U) (β.hom.hom.app (op U) (φ.hom.app (op U) a)) =
        q₀.hom.app (op U) (α.hom.hom.app (op U) a) := by
    rw [hscalar]
    exact congrArg (fun f ↦ f.hom.app (op U) (α.hom.hom.app (op U) a))
      (limit.lift_π (ConstantCompletion.quotientCone J A I) (op 0))
  constructor
  · intro U a
    rw [he]
    change β.hom.hom.app (op U) (φ.hom.app (op U) a) ∈
      (ConstantCompletion.kernelIdeal p).sections U ↔ a ∈ K.sections U
    rw [kernel_sections]
    change p.hom.app (op U) (β.hom.hom.app (op U) (φ.hom.app (op U) a)) = 0 ↔ _
    rw [hproj]
    have hk := (kernel_mem_transport q q₀ α γ hq U a).symm
    rw [kernel_sections] at hk
    exact hk
  · intro U b
    refine ⟨⊤, J.top_mem _, ?_⟩
    intro V f _
    obtain ⟨a₀, ha₀⟩ := ((ConstantCompletion.flat_and_quotients J A I).2.2 0 V).1
      (p.hom.app (op V) (β.hom.hom.app (op V) (B.obj.map f.op b)))
    refine ⟨α.inv.hom.app (op V) a₀, ?_⟩
    rw [he]
    change β.hom.hom.app (op V)
      (B.obj.map f.op b - φ.hom.app (op V) (α.inv.hom.app (op V) a₀)) ∈
        (ConstantCompletion.kernelIdeal p).sections V
    rw [kernel_sections]
    change p.hom.app (op V) (β.hom.hom.app (op V)
      (B.obj.map f.op b - φ.hom.app (op V) (α.inv.hom.app (op V) a₀))) = 0
    rw [map_sub, map_sub, hproj, iso_inv_hom, ha₀, sub_self]

private def pointConstantAbIso (A : Type u) [CommRing A] :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ≅ discreteObj A := by
  have : (coherentTopology Profinite.{u}).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  exact ((constantCommuteCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).app
        (CommRingCat.of (ULift.{u + 1} A))).symm

private theorem pointConstantAbIso_monoidal (A : Type u) [CommRing A] :
    IsMonHom (pointConstantAbIso A).hom := by
  let J := coherentTopology Profinite.{u}
  let B := ULift.{u + 1} A
  have : J.PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  let P := (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of B)
  let S := discreteSheaf A
  let g : P ⟶ S.obj := Functor.whiskerRight
    (toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of B)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let h : (constantSheaf J Ab.{u + 1}).obj (AddCommGrpCat.of B) ⟶ discreteObj A :=
    (presheafToSheaf J Ab.{u + 1}).map
      (Functor.whiskerRight g (forget₂ RingCat.{u + 1} Ab.{u + 1})) ≫
        (Sheaf.sheafifyRingPresheafIso J S).hom
  have hm : @IsMonHom _ _ _ _ _
      (Sheaf.monObj_presheafToSheaf_obj J
        (P ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) inferInstance h := by
    infer_instance
  have hm' : IsMonHom h := IsMonHom.of_eq h
    (constantSheafRingMonObj J B).symm rfl (hf := hm)
  have he : (pointConstantAbIso A).hom = h := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ (discreteObj A).property
    change _ ≫ (pointConstantAbIso A).hom.hom = _ ≫ h.hom
    have hleft : toSheafify J
        ((Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of B)) ≫
        (pointConstantAbIso A).hom.hom =
      Functor.whiskerRight
        (toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of B)))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
            forget₂ RingCat.{u + 1} Ab.{u + 1}) := by
      change _ ≫ (sheafifyMap J (Functor.constComp Profinite.{u}ᵒᵖ
        (CommRingCat.of B)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
            forget₂ RingCat.{u + 1} Ab.{u + 1})).inv ≫
          (sheafifyComposeIso J
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
              forget₂ RingCat.{u + 1} Ab.{u + 1}) _).hom) = _
      rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
        sheafComposeIso_hom_fac]
      ext U a
      rfl
    rw [hleft]
    let wg := Functor.whiskerRight g (forget₂ RingCat.{u + 1} Ab.{u + 1})
    have ht := (sheafificationAdjunction J Ab.{u + 1}).right_triangle_components
      ((sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj S)
    change toSheafify J (S.obj ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) ≫
      (Sheaf.sheafifyRingPresheafIso J S).hom.hom = 𝟙 _ at ht
    change wg = toSheafify J (P ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) ≫
      ((presheafToSheaf J Ab.{u + 1}).map wg).hom ≫
        (Sheaf.sheafifyRingPresheafIso J S).hom.hom
    erw [← Category.assoc, ← toSheafify_naturality, Category.assoc, ht,
      Category.comp_id]
  rw [he]
  exact hm'

private def discreteAbIso (A : Type u) [CommRing A] (X : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ≅ condensedRingObj (discreteObj A) X :=
  (constantSchemeIso X).app _ ≪≫ (upperStarFromPoint X).mapIso (pointConstantAbIso A)

private theorem discreteAbIso_mon (A : Type u) [CommRing A] (X : Scheme.{u}) :
    IsMonHom (discreteAbIso A X).hom := by
  let B := AddCommGrpCat.of (ULift.{u + 1} A)
  let P := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let F := upperStarFromPoint X
  let Q := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let transfer (m : MonObj (P.obj B)) : MonObj (F.obj (P.obj B)) :=
    @Functor.monObjObj _ _ _ _ _ _ F _ _ m
  have hi : @IsMonHom _ _ _ _ _ (transfer (P.monObjObj B)) (Q.monObjObj B)
      ((constantSchemeIso X).inv.app B) :=
    Functor.isMonHom_compAlgHom P F (constantSchemeIso X).inv B
  have hh := monHomInvExplicit (transfer (P.monObjObj B)) (Q.monObjObj B)
    ((constantSchemeIso X).app B).symm hi
  let := pointConstantAbIso_monoidal A
  have hmap : IsMonHom (F.map (pointConstantAbIso A).hom) := inferInstance
  dsimp only [discreteAbIso, Iso.trans_hom, Functor.mapIso_hom]
  exact FiniteDiscreteOrdinary.monHomCompExplicit _ _ _ _ _ hh hmap

private def discreteRingIso (A : Type u) [CommRing A] (X : Scheme.{u}) :
    Scheme.adicLisseConstantRing X (ULift.{u + 1} A) ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (condensedRingObj (discreteObj A) X) := by
  let := discreteAbIso_mon A X
  let := AdmissibleScalarRealization.constantRingMap_isIso A X _ (discreteAbIso A X).hom
  exact asIso (AdmissibleScalarRealization.constantRingMap A X _ (discreteAbIso A X).hom)

private theorem discreteRingIso_unit (A : Type u) [CommRing A] (X : Scheme.{u})
    (U : X.ProEtᵒᵖ) (a : ULift.{u + 1} A) :
    (discreteRingIso A X).hom.hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U a) =
      (discreteAbIso A X).hom.hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a) := by
  let := discreteAbIso_mon A X
  exact AdmissibleScalarRealization.constantRingMap_normalization A X _
    (discreteAbIso A X).hom U a

attribute [local irreducible] discreteRingIso

private theorem discreteAbIso_naturality {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (X : Scheme.{u}) :
    (discreteAbIso A X).hom ≫ (upperStarFromPoint X).map (discreteMap f) =
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        (AddCommGrpCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          (f.comp ULift.ringEquiv.toRingHom)).toAddMonoidHom) ≫
            (discreteAbIso B X).hom := by
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  have : (coherentTopology Profinite.{u}).PreservesSheafification V :=
    GrothendieckTopology.instPreservesSheafification _ _
  let g : CommRingCat.of (ULift.{u + 1} A) ⟶
      CommRingCat.of (ULift.{u + 1} B) := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    (f.comp ULift.ringEquiv.toRingHom))
  have hp := (constantCommuteCompose (coherentTopology Profinite.{u}) V).inv.naturality g
  have hs := (constantSchemeIso X).hom.naturality (V.map g)
  dsimp only [discreteAbIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp]
  change _ ≫ (upperStarFromPoint X).map
    (((constantCommuteCompose (coherentTopology Profinite.{u}) V).inv.app
      (CommRingCat.of (ULift.{u + 1} A))) ≫
        (constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} ⋙
          sheafCompose _ V).map g) = _
  rw [← hp, Functor.map_comp, ← Category.assoc]
  exact congrArg (fun h ↦ h ≫ (upperStarFromPoint X).map (pointConstantAbIso B).hom) hs.symm

private theorem discreteRingIso_naturality {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (X : Scheme.{u}) :
    (discreteRingIso A X).hom ≫ sectionMap X ((upperStarFromPoint X).map (discreteMap f)) =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          (f.comp ULift.ringEquiv.toRingHom))) ≫ (discreteRingIso B X).hom := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology X) _ _
    (InternalAbelianSheafModule.sectionRingSheaf (Scheme.ProEt.topology X)
      (condensedRingObj (discreteObj B) X)).property
  ext U a
  change ((upperStarFromPoint X).map (discreteMap f)).hom.app U
    ((discreteRingIso A X).hom.hom.app U
      ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} A)))).app U a)) = _
  rw [discreteRingIso_unit]
  have hn := congrArg (fun h ↦ h.hom.app U
    ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)) (discreteAbIso_naturality f X)
  change ((upperStarFromPoint X).map (discreteMap f)).hom.app U
    ((discreteAbIso A X).hom.hom.app U
      ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)) =
    (discreteAbIso B X).hom.hom.app U
    (((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      (AddCommGrpCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        (f.comp ULift.ringEquiv.toRingHom)).toAddMonoidHom)).hom.app U
          ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)) at hn
  erw [hn]
  have : (sheafToPresheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).IsRightAdjoint :=
    (sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).isRightAdjoint
  let g : ULift.{u + 1} A →+* ULift.{u + 1} B :=
    ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom)
  have hc := congr_app (toSheafify_naturality (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom g))) U
  have ha := congr_app (toSheafify_naturality (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).map (AddCommGrpCat.ofHom g.toAddMonoidHom))) U
  have hc' := ConcreteCategory.congr_hom hc a
  have ha' := ConcreteCategory.congr_hom ha a
  change (toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} B)))).app U (g a) =
    ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom g)).hom.app U
        ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} A)))).app U a) at hc'
  change (toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} B)))).app U (g a) =
    ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      (AddCommGrpCat.ofHom g.toAddMonoidHom)).hom.app U
        ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a) at ha'
  change (discreteAbIso B X).hom.hom.app U
    (((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      (AddCommGrpCat.ofHom g.toAddMonoidHom)).hom.app U
        ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)) =
    (discreteRingIso B X).hom.hom.app U
      (((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom g)).hom.app U
          ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1} A)))).app U a))
  erw [← hc', ← ha', discreteRingIso_unit]

private theorem pointConstantAbIso_scalar (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    (pointConstantAbIso A).hom ≫
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (constantToContinuous A) = FiniteConstantModel.scalarToContinuous A := by
  let J := coherentTopology Profinite.{u}
  have : J.PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (Profinite.continuousCoefficientRingObj A).property
  ext U a
  let he := (sheafificationAdjunction J Ab.{u + 1}).homEquiv
    ((Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))
      (Profinite.continuousCoefficientRingObj A)
  have hs := he.apply_symm_apply (FiniteConstantModel.constantFunctions A)
  dsimp only [he] at hs
  rw [Adjunction.homEquiv_unit] at hs
  have hc := ((sheafificationAdjunction J RingCat.{u + 1}).homEquiv
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A)))
    (Profinite.continuousMapRingSheafOfUniverse A)).apply_symm_apply
    (show (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A)) ⟶
      (Profinite.continuousMapRingSheafOfUniverse A).obj from
      { app S := RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ContinuousMap.C (α := S.unop)).comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ RingCat.hom_ext (by ext x; rfl) })
  have hu : toSheafify J
      ((Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
      (pointConstantAbIso A).hom.hom =
    Functor.whiskerRight
      (toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} A))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1}) := by
    change _ ≫ (sheafifyMap J (Functor.constComp Profinite.{u}ᵒᵖ _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).inv ≫
        (sheafifyComposeIso J _ _).hom) = _
    rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
      sheafComposeIso_hom_fac]
    ext S x
    rfl
  have hunit := congr_app hu U
  have hscalar := ConcreteCategory.congr_hom (congr_app hs U) a
  change (FiniteConstantModel.scalarToContinuous A).hom.app U
    ((toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a) =
      (FiniteConstantModel.constantFunctions A).app U a at hscalar
  erw [hscalar]
  change (constantToContinuous A).hom.app U
    ((pointConstantAbIso A).hom.hom.app U
      ((toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)) = _
  erw [ConcreteCategory.congr_hom hunit a]
  dsimp only [constantToContinuous, NatTrans.comp_app]
  have huRing : Functor.whiskerRight (toSheafify J
      ((Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫
      (((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
        (CommRingCat.of (ULift.{u + 1} A))).hom.hom) =
    (Functor.constComp Profinite.{u}ᵒᵖ (CommRingCat.of (ULift.{u + 1} A))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom ≫
        toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
          (RingCat.of (ULift.{u + 1} A))) := by
    change _ ≫ ((sheafifyComposeIso J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).inv ≫
        sheafifyMap J (Functor.constComp Profinite.{u}ᵒᵖ
          (CommRingCat.of (ULift.{u + 1} A))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom) = _
    erw [← Category.assoc, sheafComposeIso_inv_fac, toSheafify_naturality]
  have hr := ConcreteCategory.congr_hom (congr_app huRing U) a
  change (((constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
      (CommRingCat.of (ULift.{u + 1} A))).hom.hom.app U)
    (((toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} A)))).app U) a) =
      ((toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} A)))).app U) a at hr
  change (((sheafificationAdjunction J RingCat.{u + 1}).homEquiv _ _).symm
    { app S := RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((ContinuousMap.C (α := S.unop)).comp ULift.ringEquiv.toRingHom))
      naturality := fun _ _ _ ↦ RingCat.hom_ext (by ext x; rfl) }).hom.app U
      ((((constantCommuteCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
          (CommRingCat.of (ULift.{u + 1} A))).hom.hom.app U)
        (((toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} A)))).app U) a)) =
            (FiniteConstantModel.constantFunctions A).app U a
  erw [hr]
  rw [Adjunction.homEquiv_unit] at hc
  exact ConcreteCategory.congr_hom (congr_app hc U) a

private theorem discreteAbIso_scalar (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (X : Scheme.{u}) :
    (discreteAbIso A X).hom ≫ (upperStarFromPoint X).map
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (constantToContinuous A)) = FiniteDiscreteOrdinary.canonicalAbelianMap A X := by
  dsimp only [discreteAbIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp, pointConstantAbIso_scalar]
  rfl

private instance continuousPoint_comm (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : IsCommMonObj
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (Profinite.continuousMapRingSheafOfUniverse A)) :=
  Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafOfUniverse A) (fun S a b ↦
    @mul_comm (ULift.{u + 1} C(S.unop, A)) _ a b)

private theorem discreteRingIso_scalar (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (X : Scheme.{u}) :
    (discreteRingIso A X).hom ≫ sectionMap X ((upperStarFromPoint X).map
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (constantToContinuous A))) = FiniteDiscreteOrdinary.canonicalRingMap A X := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology X) _ _
    (InternalAbelianSheafModule.sectionRingSheaf (Scheme.ProEt.topology X)
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) X)).property
  ext U a
  change ((upperStarFromPoint X).map
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (constantToContinuous A))).hom.app U
    ((discreteRingIso A X).hom.hom.app U
      ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} A)))).app U a)) = _
  rw [discreteRingIso_unit]
  exact (congrArg (fun h ↦ h.hom.app U
    ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)) (discreteAbIso_scalar A X)).trans
        (FiniteDiscreteOrdinary.canonicalRingMap_normalization A X U a).symm

private theorem continuousIntegers_identification (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    let := spectralNorm.normedField (Padic l) E
    AdmissibleScalarRealization.CompletedIdentification
      (Padic.coefficientExtensionIntegers l E) X
      (Padic.coefficientExtensionUniformizer l E) := by
  let := spectralNorm.normedField (Padic l) E
  let A := Padic.coefficientExtensionIntegers l E
  let p := Padic.coefficientExtensionUniformizer l E
  have hd := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span ({p} : Set A) = Padic.coefficientExtensionMaximalIdeal l E :=
    hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hp : p ≠ 0 := by
    intro hz
    rw [hz, Ideal.span_singleton_zero] at hgen
    exact hd.2.2.2.2.2.2.2.2.2.1 hgen.symm
  have : CompactSpace A := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).2.1
  exact compact_adic_continuous_identification A p hp
    (fun n ↦ Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n))
    (Padic.coefficientExtension_integers_coset_basis l E) X

private theorem completedScalar_projection (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ∃ e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (condensedRingObj (integersObj l E) X) ≅
        Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E),
      ∀ n : ℕ,
        (discreteRingIso (Padic.coefficientExtensionIntegers l E) X).hom ≫
          sectionMap X (scalarMap l E X) ≫ e.hom ≫
            limit.π (Scheme.adicLisseRingSystem X (IntegralConstantCompletion.ideal l E))
              (op n) =
          (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom (Ideal.Quotient.mk
              (IntegralConstantCompletion.ideal l E ^ (n + 1)))) := by
  let := spectralNorm.normedField (Padic l) E
  obtain ⟨e, he, _⟩ := continuousIntegers_identification l E X
  refine ⟨e, ?_⟩
  intro n
  rw [← Category.assoc, ← Category.assoc]
  have hc := discreteRingIso_scalar (Padic.coefficientExtensionIntegers l E) X
  change (discreteRingIso (Padic.coefficientExtensionIntegers l E) X).hom ≫
    sectionMap X (scalarMap l E X) = _ at hc
  erw [hc]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology X) _ _
    ((Scheme.adicLisseRingSystem X (IntegralConstantCompletion.ideal l E)).obj
      (op n)).property
  ext U a
  cases a with
  | up a =>
    have hn := he U a n
    rw [← FiniteDiscreteOrdinary.canonicalRingMap_normalization _ X U (ULift.up a)] at hn
    exact hn.trans (ConcreteCategory.congr_hom
      (congr_app (toSheafify_naturality (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IntegralConstantCompletion.ideal l E ^ (n + 1)))))) U) (ULift.up a))

private def residueLiftIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    CommRingCat.of (IntegralConstantCompletion.integers l E ⧸
      IntegralConstantCompletion.ideal l E ^ (0 + 1)) ≅
        CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)) := by
  let e : IntegralConstantCompletion.integers l E ≃+*
      Padic.coefficientExtensionIntegers l E := ULift.ringEquiv
  have hI : Padic.coefficientExtensionIdeal l E 1 =
      Ideal.map e.toRingHom (IntegralConstantCompletion.ideal l E ^ (0 + 1)) := by
    rw [Ideal.map_pow, IntegralConstantCompletion.ideal, Ideal.map_span,
      Set.image_singleton]
    rfl
  exact ((Ideal.quotientEquiv _ _ e hI).trans ULift.ringEquiv.symm).toCommRingCatIso

private theorem residueLiftIso_mk (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    CommRingCat.ofHom (Ideal.Quotient.mk
      (IntegralConstantCompletion.ideal l E ^ (0 + 1))) ≫ (residueLiftIso l E).hom =
        CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)).comp
            ULift.ringEquiv.toRingHom)) := by
  let e : IntegralConstantCompletion.integers l E ≃+*
      Padic.coefficientExtensionIntegers l E := ULift.ringEquiv
  have hI : Padic.coefficientExtensionIdeal l E 1 =
      Ideal.map e.toRingHom (IntegralConstantCompletion.ideal l E ^ (0 + 1)) := by
    rw [Ideal.map_pow, IntegralConstantCompletion.ideal, Ideal.map_span,
      Set.image_singleton]
    rfl
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change ULift.up ((Ideal.quotientEquiv
    (IntegralConstantCompletion.ideal l E ^ (0 + 1))
      (Padic.coefficientExtensionIdeal l E 1) e hI)
        (Ideal.Quotient.mk _ a)) = ULift.up (Ideal.Quotient.mk _ a.down)
  rw [Ideal.quotientEquiv_mk]
  rfl

attribute [local irreducible] discreteAbIso pointConstantAbIso residueLiftIso

/-- The ordinary constant-to-continuous scalar map is flat, and is an isomorphism
modulo the finite type ideal given by its first residue kernel. This statement concerns
ordinary module sheaves only; no derived completeness or derived equivalence is asserted.

Source: Stacks Tags 093M and 099L; blueprint integral-models, proof (1).
(auxiliary; not a blueprint node).

Proof: reconstruct the section rings, then transport them to the coefficient-sized small
site. Constant-sheaf inverse image identifies the discrete integral and residue rings
with the constant sheaves of O_E and O_E/(pi). The projection-normalized integral limit
comparison identifies the continuous ring with the inverse limit of the positive constant
quotients. The scalar map commutes with every quotient projection: by the sheafification
adjunction its mate sends each integer to the corresponding constant continuous function,
and projection sends this to its residue class. The valuation-ring DVR theorem gives
Noetherianity and the principal ideal (pi). Apply flat_and_quotients in the constant
completion presentation. The first discrete kernel is the sheaf ideal generated by pi,
hence has the surjection from the rank-one module given by multiplication by pi and is
finite type. The completed kernel is its extended ideal, and both sheaf quotients are the
same constant residue sheaf. Transport flatness and this quotient isomorphism along the
section ring isomorphisms. These transports retain underlying sections and tensor actions,
so the resulting assertions apply to the displayed map and kernel, including on the empty
scheme. -/
theorem integralModels_flat_residue (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    let φ := smallMap X (scalarMap l E X)
    let I := ConstantCompletion.kernelIdeal (smallMap X (residueMap l E X))
    SheafOfModules.IsFiniteType I.module ∧
      SheafOfModules.IsFlat ((ConstantCompletion.res φ).obj
        (SheafOfModules.unit (siteModuleRings _))) ∧ I.IsQuotientIso φ := by
  classical
  dsimp only
  let A := IntegralConstantCompletion.integers l E
  let I := IntegralConstantCompletion.ideal l E
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let F := Scheme.CompletedConstantAlgebra.pushRing X
  let i := discreteRingIso (Padic.coefficientExtensionIntegers l E) X
  let j := discreteRingIso (Padic.coefficientExtensionRing l E 1) X
  let c := sectionMap X (scalarMap l E X)
  let q := sectionMap X (residueMap l E X)
  obtain ⟨e, he⟩ := completedScalar_projection l E X
  let α := F.mapIso i.symm ≪≫ (Scheme.CompletedConstantAlgebra.constantsIso X).app
    (CommRingCat.of A)
  let β := F.mapIso e ≪≫ Scheme.CompletedConstantAlgebra.completionIso X I
  let γ := F.mapIso j.symm ≪≫ (Scheme.CompletedConstantAlgebra.constantsIso X).app
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))) ≪≫
      (constantSheaf J CommRingCat.{u + 1}).mapIso (residueLiftIso l E).symm
  have hscalar : F.map c ≫ β.hom = α.hom ≫
      ConstantCompletion.coefficientMap J A I := by
    apply (cancel_epi (F.map i.hom)).mp
    have h := Scheme.CompletedConstantAlgebra.coefficientMap_eq X I
      (i.hom ≫ c ≫ e.hom) he
    dsimp only [α, β, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    have hi : F.map i.hom ≫ F.map i.inv = 𝟙 _ := by
      rw [← F.map_comp, i.hom_inv_id, F.map_id]
    simp only [Category.assoc]
    rw [← Category.assoc (F.map i.hom) (F.map i.inv), hi, Category.id_comp]
    change F.map (i.hom ≫ c ≫ e.hom) ≫
      (Scheme.CompletedConstantAlgebra.completionIso X I).hom =
        ((Scheme.CompletedConstantAlgebra.constantsIso X).app (CommRingCat.of A)).hom ≫
          ConstantCompletion.coefficientMap J A I at h
    simpa only [F.map_comp, Category.assoc, Iso.app_hom] using h
  have hresidue : F.map q ≫ γ.hom = α.hom ≫
      ConstantCompletion.quotient J A I 0 := by
    apply (cancel_epi (F.map i.hom)).mp
    have hn := discreteRingIso_naturality
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)) X
    have hq : i.hom ≫ q ≫ j.inv =
        (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
            ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)).comp
              ULift.ringEquiv.toRingHom))) := by
      change i.hom ≫ q = _ at hn
      erw [← Category.assoc, hn, Category.assoc, j.hom_inv_id, Category.comp_id]
    let g : CommRingCat.of A ⟶ CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)) :=
      CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)).comp
          ULift.ringEquiv.toRingHom))
    have hm := (Scheme.CompletedConstantAlgebra.constantsIso X).hom.naturality g
    have hm' : F.map (i.hom ≫ q ≫ j.inv) ≫
        (Scheme.CompletedConstantAlgebra.constantsIso X).hom.app
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))) =
      (Scheme.CompletedConstantAlgebra.constantsIso X).hom.app (CommRingCat.of A) ≫
        (constantSheaf J CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))) ≫
            (constantSheaf J CommRingCat.{u + 1}).map (residueLiftIso l E).hom := by
      rw [hq]
      rw [← Functor.map_comp, residueLiftIso_mk]
      exact hm
    dsimp only [α, γ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    have h := congrArg (fun t ↦ t ≫
      (constantSheaf J CommRingCat.{u + 1}).map (residueLiftIso l E).inv) hm'
    have hi : F.map i.hom ≫ F.map i.inv = 𝟙 _ := by
      rw [← F.map_comp, i.hom_inv_id, F.map_id]
    simp only [Category.assoc]
    rw [← Category.assoc (F.map i.hom) (F.map i.inv), hi, Category.id_comp]
    have heq : (constantSheaf J CommRingCat.{u + 1}).map (residueLiftIso l E).hom ≫
        (constantSheaf J CommRingCat.{u + 1}).map (residueLiftIso l E).inv = 𝟙 _ := by
      rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id]
    simp only [Category.assoc] at h
    rw [heq, Category.comp_id] at h
    change _ = _ ≫ ConstantCompletion.quotient J A I 0 at h
    simpa only [F.map_comp, Category.assoc, Iso.app_hom] using h
  let : IsNoetherianRing A := IntegralConstantCompletion.integers_noetherian l E
  refine ⟨kernel_finiteType_transport A I (F.map q) α γ hresidue, ?_,
    quotient_transport A I (F.map c) (F.map q) α β γ hscalar hresidue⟩
  exact flat_transport (F.map c) (ConstantCompletion.coefficientMap J A I)
    α β hscalar (ConstantCompletion.flat_and_quotients J A I).1

end AlgebraicGeometry.ProEtale.IntegralModelsStacks

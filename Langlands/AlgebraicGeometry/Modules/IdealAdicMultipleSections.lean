import Langlands.AlgebraicGeometry.Modules.IdealAdicQuotients
import Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentCore

/-! # Quasi-coherence and affine sections of ideal multiples -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Modules.IdealAdic

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) (M : X.Modules)

local instance : HasFiniteBiproducts X.PresheafOfModules :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance : PreservesFiniteLimits (Scheme.Modules.toPresheafOfModules X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.forget X.ringCatSheaf))

local instance : (sheafify X).IsLeftAdjoint :=
  (sheafifyAdjunction X).isLeftAdjoint

/-- The inclusion of the ideal multiple is injective on sections of every open. -/
lemma inclusion_app_injective (U : X.Opens) :
    Function.Injective ((inclusion f J M).app U) := by
  have : Mono ((PushforwardInjectiveAcyclic.toAbSheaf X).map (inclusion f J M)) :=
    (PushforwardInjectiveAcyclic.toAbSheaf X).map_mono _
  exact QuasicoherentLocal.injective_app_of_mono
    ((PushforwardInjectiveAcyclic.toAbSheaf X).map (inclusion f J M)) U

/-- A scalar generator, with values in the presheaf of ideal multiples. -/
def scalarToMultiple (a : J) :
    M.val ⟶ (multiplePresubmodule f J M).toPresheafOfModules where
  app U := by
    letI : CommRing (X.ringCatSheaf.obj.obj U) := inferInstanceAs (CommRing Γ(X, U.unop))
    exact ModuleCat.ofHom
     ((LinearMap.lsmul (X.ringCatSheaf.obj.obj U) (M.val.obj U) (scalar f U.unop a)).codRestrict
      ((multiplePresubmodule f J M).obj U)
      (fun m => Submodule.subset_span ⟨a, a.property, m, rfl⟩))
  naturality {U V} i := by
    ext m
    apply Subtype.ext
    change scalar f V.unop a • M.val.map i m =
      M.val.map i (scalar f U.unop a • m)
    rw [M.val.map_smul]
    change _ = X.presheaf.map i (scalar f U.unop a) • M.val.map i m
    rw [scalar_naturality]

/-- The finite sum of copies of `M` indexed by chosen ideal generators. -/
private def generatorSum (s : Finset R) : X.Modules :=
  ⨁ fun _ : s => M

private def generatorMap (s : Finset R) (hs : ∀ a ∈ s, a ∈ J) :
    (generatorSum M s).val ⟶ (multiplePresubmodule f J M).toPresheafOfModules := by
  have : PreservesBiproduct (fun _ : s => M) (Scheme.Modules.toPresheafOfModules X) :=
    preservesBiproduct_of_preservesProduct _
  exact ((Scheme.Modules.toPresheafOfModules X).mapBiproduct (fun _ : s => M)).hom ≫
    biproduct.desc (fun a : s => scalarToMultiple f J M ⟨a, hs a a.property⟩)

private lemma generatorMap_ι (s : Finset R) (hs : ∀ a ∈ s, a ∈ J) (a : s) :
    (biproduct.ι (fun _ : s => M) a).val ≫ generatorMap f J M s hs =
      scalarToMultiple f J M ⟨a, hs a a.property⟩ := by
  classical
  let F := Scheme.Modules.toPresheafOfModules X
  have : PreservesBiproduct (fun _ : s => M) F :=
    preservesBiproduct_of_preservesProduct _
  have hι : F.map (biproduct.ι (fun _ : s => M) a) ≫
      (F.mapBiproduct (fun _ : s => M)).hom =
        biproduct.ι (F.obj ∘ (fun _ : s => M)) a := by
    apply biproduct.hom_ext
    intro b
    dsimp only [Function.comp_def]
    simp only [Functor.mapBiproduct_hom, Category.assoc, biproduct.lift_π, ← F.map_comp]
    by_cases h : a = b
    · subst b
      simp
    · simp [biproduct.ι_π_ne _ h]
  change F.map (biproduct.ι (fun _ : s => M) a) ≫
    ((F.mapBiproduct (fun _ : s => M)).hom ≫ _) = _
  rw [← Category.assoc, hι, biproduct.ι_desc]

private lemma generatorMap_surjective (s : Finset R) (hs : ∀ a ∈ s, a ∈ J)
    (hspan : Ideal.span (s : Set R) = J) (U : X.Opensᵒᵖ) :
    Function.Surjective ((generatorMap f J M s hs).app U) := by
  let δ := generatorMap f J M s hs
  let L := LinearMap.range (((δ ≫ (multiplePresubmodule f J M).ι).app U).hom)
  have hgen (a : s) (m : M.val.obj U) : scalar f U.unop a • m ∈ L := by
    refine ⟨((biproduct.ι (fun _ : s => M) a).val.app U) m, ?_⟩
    have h := congrArg (fun g : M.val ⟶ (multiplePresubmodule f J M).toPresheafOfModules =>
      ((g ≫ (multiplePresubmodule f J M).ι).app U) m)
      (generatorMap_ι f J M s hs a)
    exact h
  have hmul (a : R) (ha : a ∈ J) (m : M.val.obj U) :
      scalar f U.unop a • m ∈ L := by
    rw [← hspan] at ha
    induction ha using Submodule.span_induction with
    | mem a ha => exact hgen ⟨a, ha⟩ m
    | zero => simpa only [map_zero, zero_smul] using L.zero_mem
    | add a b ha hb h₁ h₂ =>
      simpa [map_add, add_smul] using L.add_mem h₁ h₂
    | smul a b hb h =>
      simpa [smul_eq_mul, map_mul, mul_smul] using L.smul_mem (scalar f U.unop a) h
  have hle : (multiplePresubmodule f J M).obj U ≤ L := by
    apply Submodule.span_le.2
    rintro x ⟨a, ha, m, rfl⟩
    exact hmul a ha m
  intro x
  obtain ⟨y, hy⟩ := hle x.property
  exact ⟨y, Subtype.ext hy⟩

private def generatorSheafMap (s : Finset R) (hs : ∀ a ∈ s, a ∈ J) :
    generatorSum M s ⟶ multiple f J M :=
  ((sheafifyForgetIso X).app (generatorSum M s)).inv ≫
    (sheafify X).map (generatorMap f J M s hs)

private def generatorAmbientMap (s : Finset R) (hs : ∀ a ∈ s, a ∈ J) :
    generatorSum M s ⟶ M :=
  ⟨generatorMap f J M s hs ≫ (multiplePresubmodule f J M).ι⟩

private lemma generatorSheafMap_inclusion (s : Finset R) (hs : ∀ a ∈ s, a ∈ J) :
    generatorSheafMap f J M s hs ≫ inclusion f J M =
      generatorAmbientMap f J M s hs := by
  unfold generatorSheafMap inclusion
  rw [Category.assoc, ← Category.assoc ((sheafify X).map _),
    ← Functor.map_comp]
  change ((sheafifyForgetIso X).app (generatorSum M s)).inv ≫
    ((Scheme.Modules.toPresheafOfModules X ⋙ sheafify X).map
      (generatorAmbientMap f J M s hs) ≫ (sheafifyForgetIso X).hom.app M) = _
  rw [(sheafifyForgetIso X).hom.naturality]
  change ((sheafifyForgetIso X).app (generatorSum M s)).inv ≫
    ((sheafifyForgetIso X).app (generatorSum M s)).hom ≫
      generatorAmbientMap f J M s hs = _
  rw [Iso.inv_hom_id_assoc]

private lemma epi_generatorSheafMap (s : Finset R) (hs : ∀ a ∈ s, a ∈ J)
    (hspan : Ideal.span (s : Set R) = J) :
    Epi (generatorSheafMap f J M s hs) := by
  have : Epi (generatorMap f J M s hs) :=
    PresheafOfModules.epi_of_surjective (generatorMap_surjective f J M s hs hspan)
  change Epi (((sheafifyForgetIso X).app (generatorSum M s)).inv ≫
    (sheafify X).map (generatorMap f J M s hs))
  infer_instance

/-- A finitely generated base ideal times a quasi-coherent module is quasi-coherent. -/
lemma isQuasicoherent_multiple [M.IsQuasicoherent] (hJ : J.FG) :
    (multiple f J M).IsQuasicoherent := by
  classical
  obtain ⟨s, hs⟩ := hJ
  have hmem : ∀ a ∈ s, a ∈ J := fun a ha => hs ▸ Ideal.subset_span ha
  have : (generatorSum M s).IsQuasicoherent :=
    Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentCore.isQuasicoherent_biproduct (fun _ : s => M)
  have hQ := QuasicoherentLocal.isQuasicoherent_image (generatorAmbientMap f J M s hmem)
  have := epi_generatorSheafMap f J M s hmem hs
  have := strongEpi_of_epi (generatorSheafMap f J M s hmem)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (image.isoStrongEpiMono (generatorSheafMap f J M s hmem) (inclusion f J M)
      (generatorSheafMap_inclusion f J M s hmem)).symm hQ

/-- On an affine open, sheafifying the local ideal multiples adds no new sections. -/
lemma mem_range_inclusion_app_iff [M.IsQuasicoherent] (hJ : J.FG)
    {U : X.Opens} (hU : IsAffineOpen U) (x : Γ(M, U)) :
    x ∈ Set.range ((inclusion f J M).app U) ↔
      x ∈ (multiplePresubmodule f J M).obj (op U) := by
  classical
  obtain ⟨s, hs⟩ := hJ
  have hmem : ∀ a ∈ s, a ∈ J := fun a ha => hs ▸ Ideal.subset_span ha
  have : (generatorSum M s).IsQuasicoherent :=
    Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentCore.isQuasicoherent_biproduct (fun _ : s => M)
  have := isQuasicoherent_multiple f J M ⟨s, hs⟩
  have := epi_generatorSheafMap f J M s hmem hs
  have hcomp := congrArg (fun g : generatorSum M s ⟶ M => g.app U)
    (generatorSheafMap_inclusion f J M s hmem)
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := QuasicoherentLocal.surjective_app_of_epi
      (generatorSheafMap f J M s hmem) U hU y
    have hz := ConcreteCategory.congr_hom hcomp z
    change (inclusion f J M).app U ((generatorSheafMap f J M s hmem).app U z) =
      ((generatorMap f J M s hmem).app (op U) z).val at hz
    rw [hz]
    exact ((generatorMap f J M s hmem).app (op U) z).property
  · intro hx
    obtain ⟨z, hz⟩ := generatorMap_surjective f J M s hmem hs (op U) ⟨x, hx⟩
    refine ⟨(generatorSheafMap f J M s hmem).app U z, ?_⟩
    exact (ConcreteCategory.congr_hom hcomp z).trans (congrArg Subtype.val hz)

end Langlands.AlgebraicGeometry.Modules.IdealAdic

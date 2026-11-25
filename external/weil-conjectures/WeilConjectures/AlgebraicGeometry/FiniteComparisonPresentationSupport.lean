/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import all WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModel
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteRestrictionEncoding
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory

/-! # Private support for finite comparison presentation

These are the completed general coefficient, site-equivalence and constant-model
arguments of `FiniteComparisonPresentation`, separated to bound elaboration time.
Source: blueprint finite comparison, coefficient paragraph, Stacks Tags 03CY, 09AJ
and 09AL (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u c d h k w
open CategoryTheory CategoryTheory.Limits
namespace FiniteComparisonPresentationSupport

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

open MonoidalCategory
open scoped CategoryTheory.Obj

@[instance_reducible] private def monoidalOfOplaxIsos
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (ε : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (μ : ∀ M N : C, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (hn : ∀ {M M' N N' : C} (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (μ M' N').hom = (μ M N).hom ≫ (F.map f ⊗ₘ F.map g))
    (ha : ∀ M N P : C,
      (μ (M ⊗ N) P).hom ≫ (μ M N).hom ▷ F.obj P ≫ (α_ _ _ _).hom =
        F.map (α_ M N P).hom ≫ (μ M (N ⊗ P)).hom ≫ F.obj M ◁ (μ N P).hom)
    (hl : ∀ M : C,
      (μ (𝟙_ C) M).hom ≫ ε.hom ▷ F.obj M ≫ (λ_ _).hom = F.map (λ_ M).hom)
    (hr : ∀ M : C,
      (μ M (𝟙_ C)).hom ≫ F.obj M ◁ ε.hom ≫ (ρ_ _).hom = F.map (ρ_ M).hom) :
    F.Monoidal := by
  refine (Functor.CoreMonoidal.mk' (F := F) ε.symm (fun M N ↦ (μ M N).symm)
    (fun f N ↦ ?_) (fun M f ↦ ?_) ha (fun M ↦ ?_) (fun M ↦ ?_)).toMonoidal
  · simpa only [Iso.symm_inv, CategoryTheory.Functor.map_id, tensorHom_id] using (hn f (𝟙 N)).symm
  · simpa only [Iso.symm_inv, CategoryTheory.Functor.map_id, id_tensorHom] using (hn (𝟙 M) f).symm
  · apply (cancel_mono (λ_ _).hom).mp
    dsimp only [Iso.symm_inv]
    rw [Iso.inv_hom_id, Category.assoc, Category.assoc, hl,
      ← F.map_comp, Iso.inv_hom_id]
    exact (F.map_id M).symm
  · apply (cancel_mono (ρ_ _).hom).mp
    dsimp only [Iso.symm_inv]
    rw [Iso.inv_hom_id, Category.assoc, Category.assoc, hr,
      ← F.map_comp, Iso.inv_hom_id]
    exact (F.map_id M).symm

attribute [local irreducible] monoidalOfOplaxIsos

open InternalAbelianSheafModule in
/-- The section-module equivalence is strong monoidal.

Source: the normalized section tensor and unit comparison with coherence
(auxiliary; not a blueprint node).

Proof: take the tensor and unit isomorphisms and their naturality, associativity,
and unit identities from `internal_section_tensor_comparison`. Feed the inverse
isomorphisms to `Functor.CoreMonoidal.mk'`. Naturality follows from tensoring with
identities; the two unit equations follow by cancelling the unitors. The resulting
core monoidal structure supplies the required strong monoidal structure.
-/
theorem sectionMonoidal_exists
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    [UnivLE.{max c h, w}] [HasSheafify J Ab.{w}]
    [(J.W (A := Ab.{w})).IsMonoidal]
    (R : Sheaf J Ab.{w}) [MonObj R] [IsCommMonObj R] :
    Nonempty (InternalAbelianSheafModule.sectionModuleEquivalence J R).functor.Monoidal := by
  obtain ⟨e, e₀, hh⟩ := (internal_section_tensor_comparison J R).2
  refine ⟨monoidalOfOplaxIsos (sectionModuleEquivalence J R).functor e₀ e ?_ ?_ ?_ ?_⟩
  · intro M M' N N' f g
    exact hh.2.2.1 M M' N N' f g
  · exact hh.2.2.2.1
  · exact hh.2.2.2.2.1
  · exact hh.2.2.2.2.2.1

open InternalAbelianSheafModule in
@[instance_reducible] private def sectionMonoidal
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    [UnivLE.{max c h, w}] [HasSheafify J Ab.{w}]
    [(J.W (A := Ab.{w})).IsMonoidal]
    (R : Sheaf J Ab.{w}) [MonObj R] [IsCommMonObj R] :
    (InternalAbelianSheafModule.sectionModuleEquivalence J R).functor.Monoidal :=
  Classical.choice (sectionMonoidal_exists J R)

attribute [local irreducible] sectionMonoidal

@[instance_reducible] private def monoidalOfAdjointEquivalence
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (E : C ≌ D) (L : C ⥤ D) (adj : L ⊣ E.inverse) [L.Monoidal] :
    E.functor.Monoidal :=
  Functor.Monoidal.transport (adj.leftAdjointUniq E.toAdjunction)

@[instance_reducible] private def monoidalOfInverse
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (E : C ≌ D) (F : C ⥤ D) (G : D ⥤ C) [G.Monoidal]
    (i : F ≅ E.functor) (j : G ≅ E.inverse) : F.Monoidal := by
  letI : E.inverse.Monoidal := Functor.Monoidal.transport j
  letI : E.functor.Monoidal := E.symm.inverseMonoidal
  exact Functor.Monoidal.transport i.symm

private theorem monoidalOfInverse_exists
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (E : C ≌ D) (F : C ⥤ D) (G : D ⥤ C)
    (hG : Nonempty G.Monoidal) (i : F ≅ E.functor) (j : G ≅ E.inverse) :
    Nonempty F.Monoidal := by
  obtain ⟨mG⟩ := hG
  let := mG
  exact ⟨monoidalOfInverse E F G i j⟩

attribute [local irreducible] monoidalOfAdjointEquivalence monoidalOfInverse

private theorem constantScalarMonoidal_exists
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    (R : Type (max c h)) [CommRing R] :
    Nonempty (ConstantScalarRestriction.restriction J R).Monoidal := by
  exact ⟨(ConstantScalarRestriction.ordinary J R).braided.toMonoidal⟩

@[instance_reducible] private def constantScalarMonoidal
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    (R : Type (max c h)) [CommRing R] :
    (ConstantScalarRestriction.restriction J R).Monoidal :=
  Classical.choice (constantScalarMonoidal_exists J R)

attribute [local irreducible] constantScalarMonoidal

private theorem ringScalarMonoidal_exists
    {C : Type c} [Category.{h} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify J Ab.{w}] [J.WEqualsLocallyBijective Ab.{w}]
    {R S : Sheaf J CommRingCat.{w}} (i : R ≅ S) :
    Nonempty (SheafOfModules.scalarRestriction i.hom).Monoidal := by
  let : HasDerivedCategory.{max c h (w + 1)} (SheafOfModules.scalarModules J R) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{max c h (w + 1)} (SheafOfModules.scalarModules J S) :=
    HasDerivedCategory.standard _
  obtain ⟨t⟩ :=
    SheafOfModules.ringIso_tensor_transport.{c, h, w, max c h (w + 1), max c h (w + 1)} i
  exact ⟨t.monoidal.toMonoidal⟩

@[instance_reducible] private def ringScalarMonoidal
    {C : Type c} [Category.{h} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify J Ab.{w}] [J.WEqualsLocallyBijective Ab.{w}]
    {R S : Sheaf J CommRingCat.{w}} (i : R ≅ S) :
    (SheafOfModules.scalarRestriction i.hom).Monoidal :=
  Classical.choice (ringScalarMonoidal_exists i)

attribute [local irreducible] ringScalarMonoidal

attribute [local instance] CategoryTheory.moduleMonoidal CategoryTheory.moduleSymmetric
  CategoryTheory.moduleClosed CategoryTheory.modulePreadditive CategoryTheory.moduleGrothendieck
  CategoryTheory.flatResolution CategoryTheory.standardDerived

private def leftSquareOfRight
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    (L' : E ⥤ H) (R' : H ⥤ E) (adj' : L' ⊣ R')
    (F : C ≌ E) (G : D ≌ H) (i : R ⋙ F.functor ≅ G.functor ⋙ R') :
    L ⋙ G.functor ≅ F.functor ⋙ L' := by
  let a := adj.comp G.toAdjunction
  let b := F.toAdjunction.comp adj'
  let h : (G.inverse ⋙ R) ⋙ F.functor ≅ R' :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft G.inverse i ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight G.counitIso R' ≪≫ Functor.leftUnitor R'
  let h' : (R' ⋙ F.inverse) ⋙ F.functor ≅ R' :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft R' F.counitIso ≪≫
      Functor.rightUnitor R'
  let r := ((Functor.FullyFaithful.ofFullyFaithful F.functor).whiskeringRight _)
    |>.preimageIso (h ≪≫ h'.symm)
  exact ((conjugateIsoEquiv a b).symm r).symm

private def localFinite {C : Type c} [Category.{h} C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    (F : Sheaf J (ModuleCat.{w} A)) : Prop :=
  ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧ ∀ (U : C) (f : U ⟶ V), S f →
    ∃ M : ModuleCat.{w} A, Module.Finite A M ∧
      Nonempty (F.over U ≅ (constantSheaf (J.over U) (ModuleCat.{w} A)).obj M)

private theorem localFinite_precomp
    {C : Type c} {D : Type d} [Category.{h} C] [Category.{k} D]
    [HasPullbacks C] [HasPullbacks D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsEquivalence] [G.IsContinuous J K] [G.IsCocontinuous J K]
    (A : Type w) [CommRing A]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    [∀ V : D, HasSheafify (K.over V) (ModuleCat.{w} A)]
    [HasLimitsOfSize.{h, max c h k} (ModuleCat.{w} A)]
    (F : Sheaf K (ModuleCat.{w} A)) (hF : localFinite K A F) :
    localFinite J A ((G.sheafPushforwardContinuous (ModuleCat.{w} A) J K).obj F) := by
  let : G.PreservesOneHypercovers J K :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (CoverPreserving.of_isContinuous G J K)
  intro V
  obtain ⟨S, hS, hm⟩ := hF (G.obj V)
  refine ⟨S.functorPullback G, G.cover_lift J K hS, fun U f hf ↦ ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := hm (G.obj U) (G.map f) hf
  let H : Over U ⥤ Over (G.obj U) := Over.post G
  let r : ((G.sheafPushforwardContinuous (ModuleCat.{w} A) J K).obj F).over U ≅
      (H.sheafPushforwardContinuous (ModuleCat.{w} A)
        (J.over U) (K.over (G.obj U))).obj (F.over (G.obj U)) :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  let ce := (H.pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{w} A) (J.over U) (K.over (G.obj U))).symm.app
      ((Functor.const (Over (G.obj U))ᵒᵖ).obj M)
  exact ⟨M, hM, ⟨r ≪≫
    (H.sheafPushforwardContinuous (ModuleCat.{w} A)
      (J.over U) (K.over (G.obj U))).mapIso e ≪≫ ce⟩⟩

private theorem localFinite_iso
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    (A : Type w) [CommRing A]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    {F G : Sheaf J (ModuleCat.{w} A)} (e : F ≅ G) (hF : localFinite J A F) :
    localFinite J A G := by
  intro V
  obtain ⟨S, hS, hm⟩ := hF V
  refine ⟨S, hS, fun U f hf ↦ ?_⟩
  obtain ⟨M, hM, ⟨i⟩⟩ := hm U f hf
  exact ⟨M, hM, ⟨(J.overPullback (ModuleCat.{w} A) U).mapIso e.symm ≪≫ i⟩⟩

private theorem localFinite_site_equivalence
    {C : Type c} {D : Type d} [Category.{h} C] [Category.{k} D]
    [HasPullbacks C] [HasPullbacks D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (e : C ≌ D)
    [e.inverse.IsDenseSubsite K J] (A : Type w) [CommRing A]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    [∀ V : D, HasSheafify (K.over V) (ModuleCat.{w} A)]
    [HasLimitsOfSize.{h, max c h k} (ModuleCat.{w} A)]
    [HasLimitsOfSize.{k, max d k h} (ModuleCat.{w} A)]
    (F : Sheaf J (ModuleCat.{w} A)) :
    localFinite J A F ↔ localFinite K A ((e.sheafCongr J K (ModuleCat.{w} A)).functor.obj F) := by
  constructor
  · exact localFinite_precomp K J e.inverse A F
  · intro hF
    have hh := localFinite_precomp J K e.functor A
      ((e.sheafCongr J K (ModuleCat.{w} A)).functor.obj F) hF
    exact localFinite_iso J A ((e.sheafCongr J K (ModuleCat.{w} A)).unitIso.app F).symm hh

private def finiteModelSieve {C : Type c} [Category.{h} C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A]
    [HasSheafify J (ModuleCat.{w} A)]
    (F : Sheaf J (ModuleCat.{w} A)) (V : C) : Sieve V where
  arrows U _ := ∃ M : ModuleCat.{w} A, Module.Finite A M ∧
    Nonempty (F.over U ≅ ((constantSheaf J (ModuleCat.{w} A)).obj M).over U)
  downward_closed := by
    rintro U W f ⟨M, hM, ⟨e⟩⟩ g
    let G := (constantSheaf J (ModuleCat.{w} A)).obj M
    exact ⟨M, hM, ⟨(F.pushforwardOverMapIso g).symm ≪≫
      (J.overMapPullback (ModuleCat.{w} A) g).mapIso e ≪≫ G.pushforwardOverMapIso g⟩⟩

private theorem localFinite_iff_sieve
    {C : Type c} [Category.{h} C] [HasTerminal C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A]
    [HasSheafify J (ModuleCat.{w} A)]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    [∀ (U : C) (P : (Over U)ᵒᵖ ⥤ ModuleCat.{w} A),
      (Over.forget U).op.HasPointwiseRightKanExtension P]
    (F : Sheaf J (ModuleCat.{w} A)) :
    localFinite J A F ↔ finiteModelSieve J A F (⊤_ C) ∈ J (⊤_ C) := by
  constructor
  · intro hf
    obtain ⟨S, hS, hm⟩ := hf (⊤_ C)
    apply J.superset_covering _ hS
    intro U f hf
    obtain ⟨M, hM, ⟨e⟩⟩ := hm U f hf
    exact ⟨M, hM, ⟨e ≪≫ ((J.overPullbackConstantSheafIso (ModuleCat.{w} A) U).app M).symm⟩⟩
  · intro hf V
    refine ⟨(finiteModelSieve J A F (⊤_ C)).pullback (terminal.from V),
      J.pullback_stable _ hf, fun U f hf ↦ ?_⟩
    obtain ⟨M, hM, ⟨e⟩⟩ := hf
    exact ⟨M, hM, ⟨e ≪≫ (J.overPullbackConstantSheafIso (ModuleCat.{w} A) U).app M⟩⟩

private theorem sectionScalarComposite_exists
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{max c h} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{max c h} RingCat.{max c h})]
    [HasSheafify J Ab.{max c h}] [J.WEqualsLocallyBijective Ab.{max c h}]
    [(J.W (A := Ab.{max c h})).IsMonoidal]
    (R : Type (max c h)) [CommRing R]
    (Λ : Sheaf J Ab.{max c h}) [MonObj Λ] [IsCommMonObj Λ]
    (f : realizationRing J R ⟶ InternalAbelianSheafModule.sectionRingSheaf J Λ)
    [IsIso f] :
    Nonempty ((InternalAbelianSheafModule.sectionModuleEquivalence J Λ).functor ⋙
      SheafOfModules.scalarRestriction f ⋙ ConstantScalarRestriction.restriction J R).Monoidal := by
  let := sectionMonoidal.{c, h, max c h} J Λ
  let : (SheafOfModules.scalarRestriction f).Monoidal :=
    ringScalarMonoidal.{c, h, max c h} (asIso f)
  let : (ConstantScalarRestriction.restriction J R).Monoidal :=
    constantScalarMonoidal.{c, h} J R
  exact ⟨inferInstance⟩

end FiniteComparisonPresentationSupport

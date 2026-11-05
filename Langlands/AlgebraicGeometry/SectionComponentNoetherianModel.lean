import Langlands.AlgebraicGeometry.SectionComponent
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Flat_exists_fg_subalgebra_of_flat_pullback_snd
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation

/-! # Noetherian models of flat finitely presented morphisms with a section -/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SectionComponent

namespace NoetherianModelAux

private lemma specMap_comp {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    (T : Subalgebra B A) :
    Spec.map (CommRingCat.ofHom (algebraMap ↥T A)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B ↥T)) =
      Spec.map (CommRingCat.ofHom (algebraMap B A)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

private lemma isPullback_lift_of_fac {X X₁ Y B B' : Scheme.{u}}
    {π : X ⟶ X₁} {g : X ⟶ Y} {f : X₁ ⟶ B} {ι : Y ⟶ B}
    (sq : IsPullback π g f ι) (κ : B' ⟶ B) (ι' : Y ⟶ B') (hι : ι' ≫ κ = ι)
    (w : π ≫ f = (g ≫ ι') ≫ κ) :
    IsPullback (pullback.lift π (g ≫ ι') w) g (pullback.snd f κ) ι' := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f κ) (v₁₃ := f) (h₂₂ := κ)
    ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f κ)
  rw [pullback.lift_fst, hι]
  exact sq

/-- First descend the scheme and then its flatness. -/
theorem exists_flat_model
    {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation f] [Flat f] :
    ∃ (T : Subalgebra A₀ A), T.FG ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : X ⟶ X₀),
        Flat f₀ ∧ LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
        IsPullback π f f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) := by
  classical
  obtain ⟨T₁, hT₁, -, X₁, f₁, π₁, hlfp₁, hqc₁, hqs₁, sq₁⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
      (A₀ := A₀) f ∅
  have := hlfp₁
  have := hqc₁
  have := hqs₁
  have : Flat (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ A)))) := by
    rw [← sq₁.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso (P := @Flat)]
    infer_instance
  obtain ⟨T₂, hT₂, -, hflat₂⟩ :=
    AlgebraicGeometry.Flat.exists_fg_subalgebra_of_flat_pullback_snd (A := A) f₁ ∅
  let κ := Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))
  let σ := Spec.map (CommRingCat.ofHom (algebraMap ↥T₂ A))
  have hσ : σ ≫ κ = Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ A)) :=
    specMap_comp T₂
  have w : π₁ ≫ f₁ = (f ≫ σ) ≫ κ := by
    rw [Category.assoc, hσ]
    exact sq₁.w
  have sq₂ := isPullback_lift_of_fac sq₁ κ σ hσ w
  have : Algebra.FiniteType A₀ ↥T₁ := (Subalgebra.fg_iff_finiteType _).mp hT₁
  have : Algebra.FiniteType ↥T₁ ↥T₂ := (Subalgebra.fg_iff_finiteType _).mp hT₂
  have hFT : Algebra.FiniteType A₀ ↥T₂ :=
    Algebra.FiniteType.trans (S := ↥T₁) inferInstance inferInstance
  exact ⟨T₂.restrictScalars A₀, (Subalgebra.fg_iff_finiteType _).mpr hFT,
    pullback f₁ κ, pullback.snd f₁ κ, pullback.lift π₁ (f ≫ σ) w, hflat₂,
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ hlfp₁,
    MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ hqc₁,
    MorphismProperty.pullback_snd (P := @QuasiSeparated) _ _ hqs₁, sq₂⟩

/-- Descend the actual section as a morphism from the identity model of the base. -/
theorem exists_section_model
    {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (e : Spec (CommRingCat.of A) ⟶ X) (he : e ≫ f = 𝟙 _)
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation f] [Flat f] :
    ∃ (T : Subalgebra A₀ A), T.FG ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T))
        (e₀ : Spec (CommRingCat.of ↥T) ⟶ X₀) (π : X ⟶ X₀),
        e₀ ≫ f₀ = 𝟙 _ ∧ Flat f₀ ∧ LocallyOfFinitePresentation f₀ ∧
        QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
        IsPullback π f f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) ∧
        e ≫ π = Spec.map (CommRingCat.ofHom (algebraMap ↥T A)) ≫ e₀ := by
  classical
  obtain ⟨T₁, hT₁, X₁, f₁, π₁, hflat₁, hlfp₁, hqc₁, hqs₁, sq₁⟩ :=
    exists_flat_model (A₀ := A₀) f
  have := hflat₁
  have := hlfp₁
  have := hqc₁
  have := hqs₁
  let p := 𝟙 (Spec (CommRingCat.of ↥T₁))
  let σ₁ := Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ A))
  let E := sq₁.isoPullback
  let g : pullback p σ₁ ⟶ pullback f₁ σ₁ :=
    pullback.snd p σ₁ ≫ e ≫ E.hom
  have hg : g ≫ pullback.snd f₁ σ₁ = pullback.snd p σ₁ := by
    simp only [g, E, σ₁, Category.assoc, IsPullback.isoPullback_hom_snd, he,
      Category.comp_id]
  obtain ⟨T₂, hT₂, -, g₀, hg₀, hcompat⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (A₀ := ↥T₁) p f₁ g hg ∅
  let τ := Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))
  let σ₂ := Spec.map (CommRingCat.ofHom (algebraMap ↥T₂ A))
  have hσ : σ₂ ≫ τ = σ₁ := specMap_comp T₂
  change g₀ ≫ pullback.snd f₁ τ = pullback.snd p τ at hg₀
  let j : Spec (CommRingCat.of ↥T₂) ⟶ pullback p τ :=
    pullback.lift τ (𝟙 _) (by simp [p])
  have hjfst : j ≫ pullback.fst p τ = τ := pullback.lift_fst ..
  have hjsnd : j ≫ pullback.snd p τ = 𝟙 _ := pullback.lift_snd ..
  let e₀ := j ≫ g₀
  have he₀ : e₀ ≫ pullback.snd f₁ τ = 𝟙 _ := by
    dsimp only [e₀]
    rw [Category.assoc, hg₀, hjsnd]
  have w : π₁ ≫ f₁ = (f ≫ σ₂) ≫ τ := by
    rw [Category.assoc, hσ]
    exact sq₁.w
  let π := pullback.lift π₁ (f ≫ σ₂) w
  have hπfst : π ≫ pullback.fst f₁ τ = π₁ := pullback.lift_fst ..
  have hπsnd : π ≫ pullback.snd f₁ τ = f ≫ σ₂ := pullback.lift_snd ..
  have sq := isPullback_lift_of_fac sq₁ τ σ₂ hσ w
  let q₁ : pullback p σ₁ ⟶ pullback p τ :=
    pullback.snd p σ₁ ≫ σ₂ ≫ j
  have key : q₁ ≫ g₀ = g ≫ (E.inv ≫ π) := by
    apply hcompat
    · change q₁ ≫ pullback.fst p τ = pullback.fst p σ₁
      simp only [q₁, Category.assoc, hjfst, hσ]
      simpa only [p, Category.comp_id] using
        (pullback.condition (f := p) (g := σ₁)).symm
    · change q₁ ≫ pullback.snd p τ = pullback.snd p σ₁ ≫ σ₂
      simp only [q₁, Category.assoc, hjsnd, Category.comp_id]
    · change (E.inv ≫ π) ≫ pullback.fst f₁ τ = pullback.fst f₁ σ₁
      rw [Category.assoc, hπfst]
      exact sq₁.isoPullback_inv_fst
    · change (E.inv ≫ π) ≫ pullback.snd f₁ τ = pullback.snd f₁ σ₁ ≫ σ₂
      rw [Category.assoc, hπsnd, ← Category.assoc]
      rw [show E.inv ≫ f = pullback.snd f₁ σ₁ from sq₁.isoPullback_inv_snd]
  let j₁ : Spec (CommRingCat.of A) ⟶ pullback p σ₁ :=
    pullback.lift σ₁ (𝟙 _) (by simp [p])
  have hj₁snd : j₁ ≫ pullback.snd p σ₁ = 𝟙 _ := pullback.lift_snd ..
  have hcomm : e ≫ π = σ₂ ≫ e₀ := by
    have key' := congrArg (fun k => j₁ ≫ k) key
    simp only [q₁, g, Category.assoc, Iso.hom_inv_id_assoc] at key'
    rw [← Category.assoc j₁ (pullback.snd p σ₁), hj₁snd, Category.id_comp,
      ← Category.assoc j₁ (pullback.snd p σ₁), hj₁snd, Category.id_comp] at key'
    exact key'.symm
  have : Algebra.FiniteType A₀ ↥T₁ := (Subalgebra.fg_iff_finiteType _).mp hT₁
  have : Algebra.FiniteType ↥T₁ ↥T₂ := (Subalgebra.fg_iff_finiteType _).mp hT₂
  have hFT : Algebra.FiniteType A₀ ↥T₂ :=
    Algebra.FiniteType.trans (S := ↥T₁) inferInstance inferInstance
  exact ⟨T₂.restrictScalars A₀, (Subalgebra.fg_iff_finiteType _).mpr hFT,
    pullback f₁ τ, pullback.snd f₁ τ, e₀, π, he₀,
    MorphismProperty.pullback_snd (P := @Flat) _ _ hflat₁,
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ hlfp₁,
    MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ hqc₁,
    MorphismProperty.pullback_snd (P := @QuasiSeparated) _ _ hqs₁, sq, hcomm⟩

end NoetherianModelAux

/-- A finite type model over the integers, including the actual section and Cartesian comparison. -/
structure NoetherianSectionModel {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (e : Spec (CommRingCat.of A) ⟶ X) where
  subalgebra : Subalgebra ℤ A
  finiteGeneration : subalgebra.FG
  scheme : Scheme.{u}
  morphism : scheme ⟶ Spec (CommRingCat.of ↥subalgebra)
  sectionMorphism : Spec (CommRingCat.of ↥subalgebra) ⟶ scheme
  section_eq : sectionMorphism ≫ morphism = 𝟙 _
  comparison : X ⟶ scheme
  flat : Flat morphism
  locallyOfFinitePresentation : LocallyOfFinitePresentation morphism
  quasiCompact : QuasiCompact morphism
  quasiSeparated : QuasiSeparated morphism
  cartesian : IsPullback comparison f morphism
    (Spec.map (CommRingCat.ofHom (algebraMap ↥subalgebra A)))
  section_comparison : e ≫ comparison =
    Spec.map (CommRingCat.ofHom (algebraMap ↥subalgebra A)) ≫ sectionMorphism

attribute [instance] NoetherianSectionModel.flat
  NoetherianSectionModel.locallyOfFinitePresentation NoetherianSectionModel.quasiCompact
  NoetherianSectionModel.quasiSeparated

instance {A : Type u} [CommRing A] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of A)} {e : Spec (CommRingCat.of A) ⟶ X}
    (M : NoetherianSectionModel f e) : IsNoetherianRing ↥M.subalgebra := by
  have : Algebra.FiniteType ℤ ↥M.subalgebra :=
    (Subalgebra.fg_iff_finiteType _).mp M.finiteGeneration
  exact Algebra.FiniteType.isNoetherianRing ℤ ↥M.subalgebra

/-- Every flat quasi-compact quasi-separated locally finitely presented morphism over
an affine base, together with its actual section, admits a Noetherian model. -/
theorem nonempty_noetherianSectionModel
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (e : Spec (CommRingCat.of A) ⟶ X)
    (he : e ≫ f = 𝟙 _)
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation f] [Flat f] :
    Nonempty (NoetherianSectionModel f e) := by
  obtain ⟨T, hT, X₀, f₀, e₀, π, he₀, hflat, hlfp, hqc, hqs, sq, hcomm⟩ :=
    NoetherianModelAux.exists_section_model (A₀ := (⊥ : Subalgebra ℤ A)) f e he
  have : Algebra.FiniteType (⊥ : Subalgebra ℤ A) ↥T :=
    (Subalgebra.fg_iff_finiteType _).mp hT
  have : Algebra.FiniteType ℤ (⊥ : Subalgebra ℤ A) := by
    refine ⟨⟨∅, ?_⟩⟩
    rw [Finset.coe_empty, Algebra.adjoin_empty]
    exact (Algebra.eq_top_iff).mpr fun x => by
      obtain ⟨y, hy⟩ := x
      obtain ⟨n, rfl⟩ := Algebra.mem_bot.mp hy
      exact ⟨n, Subtype.ext rfl⟩
  have hFT : Algebra.FiniteType ℤ ↥T :=
    Algebra.FiniteType.trans (S := (⊥ : Subalgebra ℤ A)) inferInstance inferInstance
  exact ⟨{
    subalgebra := T.restrictScalars ℤ
    finiteGeneration := (Subalgebra.fg_iff_finiteType _).mpr hFT
    scheme := X₀
    morphism := f₀
    sectionMorphism := e₀
    section_eq := he₀
    comparison := π
    flat := hflat
    locallyOfFinitePresentation := hlfp
    quasiCompact := hqc
    quasiSeparated := hqs
    cartesian := sq
    section_comparison := hcomm }⟩

end Langlands.AlgebraicGeometry.SectionComponent

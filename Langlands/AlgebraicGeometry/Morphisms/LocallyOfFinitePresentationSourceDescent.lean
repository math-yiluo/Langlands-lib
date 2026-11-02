import Langlands.AlgebraicGeometry.Morphisms.SourceDescentReduction
import Langlands.Algebra.FinitePresentationSourceDescent
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Local finite presentation descends along fppf covers of the source

Stacks Project, Tag 02KL (Descent, Lemma 35.14.3), local finite presentation case.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An fppf map onto an affine scheme can be refined by a map from an affine scheme which is
still surjective and fppf. The refining map is locally of finite presentation. -/
theorem exists_affine_fppf_refinement_of_locallyOfFinitePresentation
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] :
    ∃ (Z : Scheme.{u}) (p : Z ⟶ X), IsAffine Z ∧ LocallyOfFinitePresentation p ∧
      Surjective (p ≫ f) ∧ Flat (p ≫ f) ∧ LocallyOfFinitePresentation (p ≫ f) := by
  let P : MorphismProperty Scheme.{u} := @Flat ⊓ @LocallyOfFinitePresentation
  have : P.RespectsLeft @IsOpenImmersion := by
    dsimp [P]
    infer_instance
  let 𝒰 := f.cover (show P f from ⟨inferInstance, inferInstance⟩)
  have : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun _ ↦ f.isOpenMap)
  obtain ⟨𝒱, h, hfinite, hopen⟩ := QuasiCompactCover.exists_hom 𝒰
  have : Finite 𝒱.I₀ := hfinite
  have (i : 𝒱.I₀) : IsOpenImmersion (h.h₀ i) := hopen i
  let p : ∐ (fun i : 𝒱.I₀ ↦ Spec (𝒱.X i)) ⟶ X := Sigma.desc (fun i ↦ h.h₀ i)
  have hp : LocallyOfFinitePresentation p := by
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation)
      (sigmaOpenCover _)]
    intro i
    simpa [p] using (inferInstance : LocallyOfFinitePresentation (h.h₀ i))
  have heq : p ≫ f = Sigma.desc 𝒱.f := by
    apply Sigma.hom_ext
    intro i
    simpa only [p, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, 𝒰,
      Scheme.Hom.cover_f, Scheme.AffineCover.cover_f] using h.w₀ i
  refine ⟨_, p, inferInstance, hp, ?_, ?_, ?_⟩
  · rw [heq]
    exact inferInstanceAs (Surjective (Sigma.desc 𝒱.cover.f))
  · rw [heq, IsZariskiLocalAtSource.iff_of_openCover (P := @Flat) (sigmaOpenCover _)]
    intro i
    simpa using (𝒱.map_prop i).1
  · rw [heq, IsZariskiLocalAtSource.iff_of_openCover
      (P := @LocallyOfFinitePresentation) (sigmaOpenCover _)]
    intro i
    simpa using (𝒱.map_prop i).2

/-- Stacks 02KK, finite presentation case, for `CommRingCat` morphisms. -/
theorem finitePresentation_of_faithfullyFlat_finitePresentation_comp
    {R A B : CommRingCat.{u}} (r : R ⟶ A) (s : A ⟶ B) (hff : s.hom.FaithfullyFlat)
    (hfp : s.hom.FinitePresentation) (hrs : (r ≫ s).hom.FinitePresentation) :
    r.hom.FinitePresentation := by
  rw [CommRingCat.hom_comp] at hrs
  algebraize [r.hom, s.hom, s.hom.comp r.hom]
  have : Module.FaithfullyFlat A B := hff
  exact Langlands.Algebra.finitePresentation_of_faithfullyFlat_of_finitePresentation R A B

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 02KL**, local finite presentation case: if `f` is surjective, flat and locally of
finite presentation and `f ≫ g` is locally of finite presentation, then so is `g`. -/
theorem locallyOfFinitePresentation_of_surjective_flat_comp
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [hfSurj : Surjective f] [hfFlat : Flat f] [hfFp : LocallyOfFinitePresentation f]
    [hfg : LocallyOfFinitePresentation (f ≫ g)] :
    LocallyOfFinitePresentation g := by
  wlog hS : IsAffine S generalizing X Y S
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation)
      _ (iSup_affineOpens_eq_top S)]
    intro U
    have hAU : IsAffine U.1 := U.2
    have hcomp : LocallyOfFinitePresentation ((f ∣_ g ⁻¹ᵁ U.1) ≫ (g ∣_ U.1)) := by
      rw [← morphismRestrict_comp]
      exact IsZariskiLocalAtTarget.restrict (P := @LocallyOfFinitePresentation) hfg U.1
    have hsurj : Surjective (f ∣_ g ⁻¹ᵁ U.1) :=
      IsZariskiLocalAtTarget.restrict hfSurj _
    have hflat : Flat (f ∣_ g ⁻¹ᵁ U.1) :=
      IsZariskiLocalAtTarget.restrict hfFlat _
    have hfp : LocallyOfFinitePresentation (f ∣_ g ⁻¹ᵁ U.1) :=
      IsZariskiLocalAtTarget.restrict hfFp _
    exact this (f ∣_ g ⁻¹ᵁ U.1) (g ∣_ U.1) inferInstance
  have : IsAffine S := hS
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation)
      Y.affineCover]
    intro i
    let j := Y.affineCover.f i
    have hcomp : LocallyOfFinitePresentation ((pullback.snd f j) ≫ (j ≫ g)) := by
      rw [← Category.assoc, ← pullback.condition, Category.assoc]
      exact locallyOfFinitePresentation_comp _ _ (hg := hfg)
    exact this (pullback.snd f j) (j ≫ g) inferInstance
  have : IsAffine Y := hY
  obtain ⟨Z, p, hZ, hp, hs, hf, hfp⟩ :=
    exists_affine_fppf_refinement_of_locallyOfFinitePresentation f
  have : IsAffine Z := hZ
  have : LocallyOfFinitePresentation p := hp
  have : LocallyOfFinitePresentation ((p ≫ f) ≫ g) := by
    rw [Category.assoc]
    infer_instance
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  apply finitePresentation_of_faithfullyFlat_finitePresentation_comp g.appTop (p ≫ f).appTop
  · exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (p ≫ f)).mp ⟨hf, hs⟩
  · have : LocallyOfFinitePresentation (p ≫ f) := hfp
    exact (p ≫ f).finitePresentation_appTop
  · simpa only [Scheme.Hom.comp_appTop] using
      HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) ((p ≫ f) ≫ g)
        inferInstance

end Langlands.AlgebraicGeometry

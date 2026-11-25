/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.Induction
public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FinitePresentationApproximation

/-!
# Finite refinements of finite presentation

Let `r₀ : T₀ ⟶ T` be finite and surjective onto a quasi-compact quasi-separated scheme, and
suppose that `r₀` factors Zariski locally through a morphism `u : U ⟶ T` locally of finite
presentation. Then so does some finite, finitely presented, surjective `r : T' ⟶ T`, with a
finite open covering of `T'`.

Write `T₀` as a cofiltered limit of finite `T`-schemes of finite presentation (Stacks Project
Tag 09YZ). Finitely many quasi-compact opens of `T₀` on which `r₀` factors through `u` descend
to opens of some stage which still cover it (Stacks Project Tag 01Z4), and the factorizations
descend to a further stage since `u` is locally of finite presentation (Stacks Project
Tag 01ZC).

## Main statements

- `AlgebraicGeometry.Scheme.Hom.FactorsLocallyThrough.exists_locallyOfFinitePresentation`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Descending a finite refinement to a finitely presented one.** If a finite surjective
`r₀ : T₀ ⟶ T` to a quasi-compact quasi-separated scheme factors Zariski locally through
`u : U ⟶ T` locally of finite presentation, then there are a finite, finitely presented,
surjective `r : T' ⟶ T`, a finite open covering `T' = ⋃ₐ Wₐ` and `φₐ : Wₐ ⟶ U` with
`φₐ ≫ u = r|_{Wₐ}`. -/
theorem Scheme.Hom.FactorsLocallyThrough.exists_locallyOfFinitePresentation
    {T₀ U T : Scheme.{u}} {r₀ : T₀ ⟶ T} {u : U ⟶ T} [LocallyOfFinitePresentation u]
    [IsFinite r₀] [Surjective r₀] [CompactSpace T] [QuasiSeparatedSpace T]
    (h : r₀.FactorsLocallyThrough u) :
    ∃ (T' : Scheme.{u}) (r : T' ⟶ T) (_ : IsFinite r) (_ : LocallyOfFinitePresentation r)
      (_ : Surjective r) (J : Type) (_ : Finite J) (W : J → T'.Opens)
      (φ : ∀ a, (W a).toScheme ⟶ U), ⨆ a, W a = ⊤ ∧ ∀ a, φ a ≫ u = (W a).ι ≫ r := by
  classical
  have : CompactSpace T₀ := QuasiCompact.compactSpace_of_compactSpace r₀
  -- a finite covering of `T₀` by quasi-compact opens on which `r₀` factors through `u`
  have hcov (z : T₀) : ∃ A : T₀.Opens, IsCompact (A : Set T₀) ∧ z ∈ A ∧
      ∃ ψ : A.toScheme ⟶ U, ψ ≫ u = Scheme.Opens.ι A ≫ r₀ := by
    obtain ⟨O, ι, _, φ, hz, hφ⟩ := h z
    obtain ⟨_, ⟨A, hA, rfl⟩, hzA, hAι⟩ :=
      T₀.isBasis_affineOpens.exists_subset_of_mem_open hz ι.isOpenEmbedding.isOpen_range
    have hAr : Set.range (Scheme.Opens.ι A) ⊆ Set.range ι := by
      rw [Scheme.Opens.range_ι]
      exact hAι
    refine ⟨A, hA.isCompact, hzA, IsOpenImmersion.lift ι (Scheme.Opens.ι A) hAr ≫ φ, ?_⟩
    rw [Category.assoc, hφ, IsOpenImmersion.lift_fac_assoc]
  choose A hAc hzA ψ hψ using hcov
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun z ↦ (A z : Set T₀))
    (fun z ↦ (A z).2) (fun z _ ↦ Set.mem_iUnion.mpr ⟨z, hzA z⟩)
  let pt (a : Fin s.card) : T₀ := (s.equivFin.symm a).1
  have hApt : ⨆ a, A (pt a) = ⊤ := by
    refine top_le_iff.mp fun z _ ↦ ?_
    obtain ⟨w, hw, hzw⟩ : ∃ w ∈ s, z ∈ A w := by simpa using hs (Set.mem_univ z)
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨s.equivFin ⟨w, hw⟩, ?_⟩
    simpa [pt] using hzw
  -- the finite approximation of `T₀`
  obtain ⟨F, hF⟩ := r₀.exists_finiteApproximation_of_isIntegralHom
  have := F.isCofiltered
  have := F.isFinite_p
  have hFa {i j : F.I} (f : i ⟶ j) : IsAffineHom (F.D.map f) :=
    MorphismProperty.of_postcomp (W := @IsAffineHom) (W' := @IsSeparated) _ (F.p j)
      inferInstance (by rw [F.map_p]; infer_instance)
  have : ∀ i, CompactSpace (F.D.obj i) := fun i ↦ QuasiCompact.compactSpace_of_compactSpace (F.p i)
  have : ∀ i, QuasiSeparatedSpace (F.D.obj i) :=
    fun i ↦ quasiSeparatedSpace_of_quasiSeparated (F.p i)
  let c : Cone F.D := ⟨T₀, F.π⟩
  have hc : IsLimit c := F.isLimit
  let pT : F.D ⟶ (Functor.const F.I).obj T :=
    { app := F.p
      naturality _ _ g := by simp [F.map_p] }
  -- the opens descend to a stage, where they still cover
  have hdesc (a : Fin s.card) := exists_preimage_eq F.D c hc (A (pt a)) (hAc _)
  choose i V hVc hV using hdesc
  obtain ⟨i₀, hi₀⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  have f (a : Fin s.card) : i₀ ⟶ i a := (hi₀ (by simp)).some
  have hV₀ (a : Fin s.card) : c.π.app i₀ ⁻¹ᵁ (F.D.map (f a) ⁻¹ᵁ V a) = A (pt a) := by
    rw [← Scheme.Hom.comp_preimage, c.w, hV a]
  obtain ⟨i₁, f₁, hf₁⟩ := exists_map_eq_top F.D c hc (⨆ a, F.D.map (f a) ⁻¹ᵁ V a) (by
    rw [Scheme.Hom.preimage_iSup]
    simp_rw [hV₀]
    exact hApt)
  let V₁ (a : Fin s.card) := F.D.map f₁ ⁻¹ᵁ F.D.map (f a) ⁻¹ᵁ V a
  have hV₁ (a : Fin s.card) : c.π.app i₁ ⁻¹ᵁ V₁ a = A (pt a) := by
    rw [← hV₀ a, ← Scheme.Hom.comp_preimage, c.w]
  have hV₁c (a : Fin s.card) : IsCompact (V₁ a : Set (F.D.obj i₁)) :=
    QuasiCompact.isCompact_preimage (f := F.D.map f₁ ≫ F.D.map (f a)) _ (V a).2 (hVc a)
  have hV₁top : ⨆ a, V₁ a = ⊤ := by
    simp only [V₁, ← Scheme.Hom.preimage_iSup, hf₁]
  -- the factorizations descend to a further stage
  have hmor (a : Fin s.card) : ∃ (k : Over i₁) (g : (opensDiagram F.D i₁ (V₁ a)).obj k ⟶ U),
      g ≫ u = (opensDiagramι F.D i₁ (V₁ a)).app k ≫ F.p k.left := by
    have (j : Over i₁) : CompactSpace ((opensDiagram F.D i₁ (V₁ a)).obj j) :=
      isCompact_iff_compactSpace.mp
        (QuasiCompact.isCompact_preimage (f := F.D.map j.hom) _ (V₁ a).2 (hV₁c a))
    have (j : Over i₁) : QuasiSeparatedSpace ((opensDiagram F.D i₁ (V₁ a)).obj j) :=
      quasiSeparatedSpace_of_quasiSeparated (Scheme.Opens.ι _)
    obtain ⟨k, g, -, hg⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (opensDiagram F.D i₁ (V₁ a)) (opensDiagramι F.D i₁ (V₁ a) ≫ (Over.forget i₁).whiskerLeft pT)
      u (opensCone F.D c i₁ (V₁ a)) (isLimitOpensCone F.D c hc i₁ (V₁ a))
      (T₀.homOfLE (hV₁ a).le ≫ ψ (pt a)) (by
        ext j : 2
        simp only [NatTrans.comp_app, Functor.const_map_app, Category.assoc, hψ,
          Scheme.homOfLE_ι_assoc]
        simp only [Functor.const_obj_obj, opensCone_π_app, Functor.comp_obj, Over.forget_obj,
          opensDiagramι_app, Functor.whiskerLeft_app, Scheme.Hom.resLE_comp_ι_assoc]
        change _ ≫ F.π.app j.left ≫ F.p j.left = _
        rw [F.π_p])
    exact ⟨k, g, hg⟩
  choose k g hg using hmor
  obtain ⟨m, hm⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  have hk (a : Fin s.card) : m ⟶ k a := (hm (by simp)).some
  refine ⟨F.D.obj m.left, F.p m.left, inferInstance, hF _, ⟨fun t ↦ ?_⟩, Fin s.card,
    inferInstance, fun a ↦ F.D.map m.hom ⁻¹ᵁ V₁ a,
    fun a ↦ (opensDiagram F.D i₁ (V₁ a)).map (hk a) ≫ g a, ?_, fun a ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := r₀.surjective t
    exact ⟨F.π.app m.left z, by rw [← Scheme.Hom.comp_apply, F.π_p]; rfl⟩
  · rw [← Scheme.Hom.preimage_iSup, hV₁top, Scheme.Hom.preimage_top]
  · rw [Category.assoc, hg, ← Category.assoc, (opensDiagramι F.D i₁ (V₁ a)).naturality]
    simp [F.map_p]

end AlgebraicGeometry

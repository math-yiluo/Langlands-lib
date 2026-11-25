/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone

/-!
# The deformation to the normal cone of a section of a smooth morphism is smooth

For `g : V ⟶ B` smooth, of relative dimension that may vary over `V`, with a closed section `s`,
the projection `g̃ : D_s V ⟶ 𝔸¹_B` of the deformation to the normal cone of the section is smooth
(`AlgebraicGeometry.Scheme.Hom.smooth_deformationSpaceProj`). This is the variant of
`AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj` for smooth `g`
without a fixed relative dimension: the charts of that proof only use the relative dimension near
the point at hand, which is constant there.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.smooth_deformationSpaceProj`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {V B : Scheme.{u}}

namespace Scheme.Hom

open AffineZariskiSite

variable (g : V ⟶ B) (s : B ⟶ V)

/-- The standard smooth charts of a smooth `g` can be shrunk around a point of the source to
basic opens; on such a chart `g` has some relative dimension `d`. -/
lemma exists_isStandardSmoothOfRelativeDimension_appLE_basicOpen [Smooth g] (v : V)
    (O : V.Opens) (hvO : v ∈ O) :
    ∃ (d : ℕ) (W : B.Opens) (_ : IsAffineOpen W) (U : V.Opens) (_ : IsAffineOpen U) (_ : v ∈ U)
      (_ : U ≤ O) (hUW : U ≤ g ⁻¹ᵁ W),
      (g.appLE W U hUW).hom.IsStandardSmoothOfRelativeDimension d := by
  obtain ⟨W, hW, U₀, hU₀, hvU₀, e, hf⟩ := (Smooth.iff_forall_exists_isStandardSmooth g).mp ‹_› v
  obtain ⟨d, hQ⟩ : ∃ d, (g.appLE W U₀ e).hom.IsStandardSmoothOfRelativeDimension d := by
    let := (g.appLE W U₀ e).hom.toAlgebra
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hf.out
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩
  obtain ⟨r, hrO, hvr⟩ := hU₀.exists_basicOpen_le (V := O) ⟨v, hvO⟩ hvU₀
  refine ⟨d, W, hW, V.basicOpen r, hU₀.basicOpen r, hvr, hrO, (V.basicOpen_le r).trans e, ?_⟩
  have := hU₀.isLocalization_basicOpen r
  have h := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
    d).right Γ(V, V.basicOpen r) r _ hQ
  rwa [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map] at h

/-- **Charts away from the section.** Away from `s(B)` the deformation space is
`V ×_B 𝔾_{m,B}`, so `g̃` is smooth there. -/
lemma exists_smooth_chart_of_notMem_range [Smooth g] [IsClosedImmersion s] (v : V)
    (hv : v ∉ Set.range s) :
    ∃ U : V.AffineZariskiSite, v ∈ U.1 ∧ Smooth
      (colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U ≫
        deformationSpaceProj g s) := by
  let O : V.Opens := ⟨(Set.range s)ᶜ, s.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  obtain ⟨d, W, hW, U, hU, hvU, hUO, hUW, hQ⟩ :=
    exists_isStandardSmoothOfRelativeDimension_appLE_basicOpen g v O hv
  refine ⟨⟨U, hU⟩, hvU, ?_⟩
  have := smoothOfRelativeDimension_ι_deformationSpaceProj d ⟨U, hU⟩ hW hUW (s := s) ?_
  · exact SmoothOfRelativeDimension.smooth d _
  have hI : s.ker.siteIdeal ⟨U, hU⟩ = ⊤ := by
    rw [IdealSheafData.siteIdeal, Scheme.Hom.ker_apply, Ideal.eq_top_iff_one, RingHom.mem_ker]
    have : s ⁻¹ᵁ U = ⊥ := eq_bot_iff.mpr fun b hb ↦ hUO hb ⟨b, rfl⟩
    have : Subsingleton Γ(B, s ⁻¹ᵁ U) := by
      rw [this]; infer_instance
    exact Subsingleton.elim _ _
  rw [hI]
  exact smoothOfRelativeDimension_extendedReesAlgebra_top _
    (smoothOfRelativeDimension_specMap_of_isStandardSmooth d _ hQ)

/-- **Étale coordinates along the section.** Near a point `s(b)` there are an affine open
`W ∋ b` of `B`, an affine open `U ⊆ g⁻¹ W` of `V` with `s⁻¹ U = W`, a relative dimension `d`,
and étale coordinates `ψ : Γ(W)[X₁, …, X_d] ⟶ Γ(U)` over `Γ(W)` generating the ideal of the
section. -/
lemma exists_etale_coordinates_of_mem_range_of_smooth [Smooth g] [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 B) (b : B) :
    ∃ (d : ℕ) (W : B.Opens) (_ : IsAffineOpen W) (U : V.AffineZariskiSite)
      (hUW : U.1 ≤ g ⁻¹ᵁ W),
      b ∈ W ∧ s ⁻¹ᵁ U.1 = W ∧ ∃ ψ : MvPolynomial (Fin d) Γ(B, W) →+* Γ(V, U.1), ψ.Etale ∧
        ψ.comp MvPolynomial.C = (g.appLE W U.1 hUW).hom ∧
        s.ker.siteIdeal U = (Ideal.mvPolynomialOrigin Γ(B, W) (Fin d)).map ψ := by
  have hgs : ∀ b, g (s b) = b := fun b ↦ by rw [← Scheme.Hom.comp_apply, hs]; rfl
  obtain ⟨d, W₀, hW₀, U₀, hU₀, hvU₀, -, hUW₀, hQ₀⟩ :=
    exists_isStandardSmoothOfRelativeDimension_appLE_basicOpen g (s b) ⊤ trivial
  have hbW₀ : b ∈ W₀ := hgs b ▸ hUW₀ hvU₀
  obtain ⟨c, hcU, hbc⟩ := hW₀.exists_basicOpen_le (V := s ⁻¹ᵁ U₀) ⟨b, hvU₀⟩ hbW₀
  set W := B.basicOpen c
  have hW : IsAffineOpen W := hW₀.basicOpen c
  set U := V.basicOpen (g.appLE W₀ U₀ hUW₀ c)
  have hU : IsAffineOpen U := hU₀.basicOpen _
  have hUW : U ≤ g ⁻¹ᵁ W := by
    rw [show U = _ from basicOpen_appLE g hUW₀ c]; exact inf_le_right
  have hsU : s ⁻¹ᵁ U = W := by
    rw [show U = _ from basicOpen_appLE g hUW₀ c, Scheme.Hom.preimage_inf,
      ← Scheme.Hom.comp_preimage, hs, Scheme.Hom.id_preimage]
    exact inf_eq_right.mpr hcU
  have hQ : (g.appLE W U hUW).hom.IsStandardSmoothOfRelativeDimension d := by
    have := hW₀.isLocalization_basicOpen c
    have := hU₀.isLocalization_basicOpen (g.appLE W₀ U₀ hUW₀ c)
    have := hW₀.appLE_eq_away_map g hU₀ hUW₀ c
    rw [this]
    exact (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves d).away _ _ _ _ hQ₀
  -- the section as a retraction of rings
  let f := g.appLE W U hUW
  let σ := s.appLE U W hsU.ge
  have hσf : σ.hom.comp f.hom = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
    rw [Scheme.Hom.appLE_congr_hom hs _ _ _ (by simp)]
    ext x
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
    erw [B.presheaf.map_id]
    rfl
  obtain ⟨φ, hφf, hφ⟩ := hQ.exists_etale_mvPolynomial
  obtain ⟨a, hσa, H⟩ := exists_etale_coordinates_of_section f.hom σ.hom hσf φ hφ hφf
  have hσ : σ = s.app U ≫ B.presheaf.map (eqToHom hsU.symm).op := rfl
  have hinj : Function.Injective (B.presheaf.map (eqToHom hsU.symm).op).hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  set U' := V.basicOpen a
  have hU' : IsAffineOpen U' := hU.basicOpen a
  have hU'W : U' ≤ g ⁻¹ᵁ W := (V.basicOpen_le a).trans hUW
  have := hU.isLocalization_basicOpen a
  obtain ⟨ψ, hψ, hψf, hJ⟩ := H Γ(V, U')
  refine ⟨d, W, hW, ⟨U', hU'⟩, hU'W, hbc, ?_, ψ, hψ, ?_, ?_⟩
  · have hb : B.basicOpen (σ a) = W := by
      rw [hσa, Scheme.basicOpen_of_isUnit _ isUnit_one]
    rw [hσ, CommRingCat.comp_apply, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen] at hb
    refine le_antisymm ((s.preimage_mono (V.basicOpen_le a)).trans hsU.le) ?_
    exact hb.ge.trans inf_le_right
  · rw [hψf, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
  · rw [← hJ, hσ, CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hinj,
      ← Scheme.Hom.ker_apply s ⟨U, hU⟩]
    exact (s.ker.map_ideal_basicOpen ⟨U, hU⟩ a).symm

/-- **Charts along the section.** Near a point `s(b)` there are étale coordinates on `V` over `B`
in which `s` is the origin, and on the corresponding chart `g̃` is smooth. -/
lemma exists_smooth_chart_of_mem_range [Smooth g] [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B)
    (b : B) :
    ∃ U : V.AffineZariskiSite, s b ∈ U.1 ∧ Smooth
      (colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U ≫
        deformationSpaceProj g s) := by
  obtain ⟨d, W, hW, U, hUW, hbW, hsU, ψ, hψ, hψf, hI⟩ :=
    exists_etale_coordinates_of_mem_range_of_smooth g s hs b
  refine ⟨U, ?_, ?_⟩
  · change b ∈ s ⁻¹ᵁ U.1
    rwa [hsU]
  · have := smoothOfRelativeDimension_ι_deformationSpaceProj d U hW hUW (s := s) (by
      rw [hI]
      exact smoothOfRelativeDimension_extendedReesAlgebra_of_etale _ _ hψ hψf)
    exact SmoothOfRelativeDimension.smooth d _

/-- Blueprint `prose-09-12` (2): the coordinates, for a smooth morphism whose
relative dimension may vary.

**The deformation space is smooth.** If `g` is smooth with closed section `s`, then
`g̃ : D_s V ⟶ 𝔸¹_B` is smooth: near every point the relative dimension of `g` is constant, and the
charts of `AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj` apply. -/
theorem smooth_deformationSpaceProj [Smooth g] [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    Smooth (deformationSpaceProj g s) := by
  have H : ∀ x, ∃ O : s.ker.deformationSpace.Opens, x ∈ O ∧
      Smooth (O.ι ≫ deformationSpaceProj g s) := fun x ↦ by
    have hex : ∃ U : V.AffineZariskiSite, s.ker.deformationSpaceProj x ∈ U.1 ∧ Smooth
        (colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U ≫
          deformationSpaceProj g s) := by
      by_cases h : s.ker.deformationSpaceProj x ∈ Set.range s
      · obtain ⟨b, hb⟩ := h
        obtain ⟨U, hU, H⟩ := exists_smooth_chart_of_mem_range g s hs b
        exact ⟨U, hb ▸ hU, H⟩
      · exact exists_smooth_chart_of_notMem_range g s _ h
    obtain ⟨U, hxU, H⟩ := hex
    refine ⟨(colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor
      U).opensRange, ?_, ?_⟩
    · rw [← toBase_preimage]
      exact hxU
    · let e := IsOpenImmersion.isoOfRangeEq
        (colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U)
        (colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor
          U).opensRange.ι (by simp)
      rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Smooth) e.hom,
        ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
      exact H
  choose O hxO hO using H
  exact IsZariskiLocalAtSource.of_iSup_eq_top O
    (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxO x⟩) hO

end Scheme.Hom

end AlgebraicGeometry

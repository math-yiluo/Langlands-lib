import Langlands.GroupScheme.ReducedBaseSmooth.Local
import Langlands.GroupScheme.ReducedBaseSmooth.Slice

/-! # Affine charts: the section lies in the smooth locus -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme.ReducedBaseSmooth

/-- The section lies in the smooth locus, assuming the rank of the cotangent fibre of an
algebra at a point equals the relative dimension of its smooth residue fibre (`homega`). -/
theorem mem_smoothLocus_of_fibres_of_finrank
    (homega : ∀ {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] (p : Ideal R) [p.IsPrime]
      (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p] (n : ℕ),
      SmoothOfRelativeDimension n
        (Spec.map (CommRingCat.ofHom (algebraMap p.ResidueField (p.Fiber B)))) →
      Module.finrank Q.ResidueField (Q.ResidueField ⊗[B] Ω[B⁄R]) = n)
    {S Y : Scheme.{u}} [IsReduced S] [IsLocallyNoetherian S] (q : Y ⟶ S) [LocallyOfFiniteType q]
    (e : S ⟶ Y) (he : e ≫ q = 𝟙 S) (n : ℕ) (U : S.Opens)
    (hU : ∀ t ∈ U, SmoothOfRelativeDimension n (q.fiberToSpecResidueField t)) (s : S)
    (hs : s ∈ U) : e s ∈ q.smoothLocus := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  have hes : e s ∈ q ⁻¹ᵁ V := by
    change q (e s) ∈ V
    rw [← Scheme.Hom.comp_apply, he]
    exact hsV
  obtain ⟨_, ⟨W, hW, rfl⟩, hesW, hWV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hes (q ⁻¹ᵁ V).2
  let R := Γ(S, V)
  let A := Γ(Y, W)
  let φ : R ⟶ A := q.appLE V W hWV
  let : Algebra R A := φ.hom.toAlgebra
  have : Algebra.FiniteType R A := q.finiteType_appLE hV hW hWV
  have hsq : Spec.map φ ≫ hV.fromSpec = hW.fromSpec ≫ q :=
    IsAffineOpen.SpecMap_appLE_fromSpec q hV hW hWV
  obtain ⟨x, hx⟩ : s ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hsV
  obtain ⟨y, hy⟩ : e s ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hesW
  have hxy : Spec.map φ y = x := by
    apply hV.fromSpec.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, he, hx]
    rfl
  -- The residue fibre of the affine chart at `x`.
  have hfx : SmoothOfRelativeDimension n ((Spec.map φ).fiberToSpecResidueField x) := by
    have h1 := smoothOfRelativeDimension_fiber_comp_of_isOpenImmersion hW.fromSpec q s n (hU s hs)
    rw [← hsq, ← hx] at h1
    exact smoothOfRelativeDimension_fiber_of_isPullback
      (IsPullback.of_horiz_isIso_mono (fst := 𝟙 _) (snd := Spec.map φ)
        (f := Spec.map φ ≫ hV.fromSpec) (g := hV.fromSpec) ⟨by simp⟩) x n h1
  have hfib : SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom
      (algebraMap x.asIdeal.ResidueField (x.asIdeal.Fiber A)))) :=
    (MorphismProperty.arrow_mk_iso_iff (P := @SmoothOfRelativeDimension n)
      (Spec.fiberToSpecResidueFieldIso R A x)).mp hfx
  have : y.asIdeal.LiesOver x.asIdeal := ⟨by rw [← hxy]; rfl⟩
  have hrank := homega x.asIdeal y.asIdeal n hfib
  obtain ⟨a, ha⟩ := exists_span_eq_top_of_finrank_eq y.asIdeal n hrank
  obtain ⟨f, hfQ, Z0, p0, i0, hp0, hqc, hqs, hi0, hcomp⟩ :=
    exists_closedImmersion_smooth_of_span y.asIdeal a ha
  let ιY := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) ≫ hW.fromSpec
  have hRA : CommRingCat.ofHom (algebraMap R (Localization.Away f)) =
      φ ≫ CommRingCat.ofHom (algebraMap A (Localization.Away f)) := by
    ext r
    exact IsScalarTower.algebraMap_apply R A (Localization.Away f) r
  have hg : Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) ≫ hV.fromSpec =
      ιY ≫ q := by
    rw [hRA, Spec.map_comp, Category.assoc, hsq, Category.assoc]
  have hyY : e s ∈ Set.range ιY := by
    have hy' : y ∈ Set.range
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))) := by
      change y ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away f)))
      rw [PrimeSpectrum.localization_away_comap_range _ f]
      exact hfQ
    obtain ⟨y', hy'⟩ := hy'
    exact ⟨y', by rw [Scheme.Hom.comp_apply, hy']; exact hy⟩
  exact mem_smoothLocus_of_closedImmersion_chart q e he n U hU hV.fromSpec ιY _ hg p0 i0 hcomp
    s hs ⟨x, hx⟩ hyY

end Langlands.GroupScheme.ReducedBaseSmooth

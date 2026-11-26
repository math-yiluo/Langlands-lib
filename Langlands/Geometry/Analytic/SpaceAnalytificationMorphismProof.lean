import Langlands.Geometry.Analytic.EtaleCoverHomExt
import Langlands.Geometry.Analytic.LocalizedChartCoverGluing
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinoidChartCover
import Langlands.Geometry.Analytic.SpaceAnalytificationMorphismCompatibility
import Langlands.Geometry.Analytic.SpaceAnalytificationMorphismStatement

/-! # Morphisms of algebraic spaces induce morphisms of analytifications -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open SaturatedAtlasPresentation AffineAnalytification

/-- A morphism `f : X' ⟶ X` of algebraic spaces over `Spec K`, with `X'` separated and
locally of finite type, induces exactly one morphism of given analytifications that is
compatible with the maps of all affine test points. -/
theorem spaceAnalytificationMorphism : SpaceAnalytificationMorphismStatement.{u} := by
  classical
  intro K _ _ _ X' X f hX' hft' Y' Y p' p hp' hp
  obtain ⟨A₀, hA₀⟩ := localizedObjectEquiv.surjective Y'
  change localizationFunctor.obj A₀ = Y' at hA₀
  subst hA₀
  obtain ⟨A, e, I, hI, hpts⟩ := exists_affinoidPointHom_pair_chartCover
    hp' hp' hX' hft' hX' hft' A₀ (𝟙 _) (𝟙 _)
  -- On each chart of the cover, the chart map factors through the analytic map of a test point.
  have hfac (k : I) : ∃ (B : CommAlgCat.{u} K) (Q : FinitePolynomialPresentation K B)
      (z : RingPoints K X' B)
      (g : localizationFunctor.obj (A.smallChartSpectrum k.val) ⟶ localized K Q),
      g ≫ p' B Q z = localizationFunctor.map (A.smallChartSpectrumInclusion k.val) ≫ e.hom := by
    obtain ⟨x, -, hx, -⟩ := hpts k
    obtain ⟨B, _, _, Q, ψ, z, rfl⟩ := exists_polynomial_point_factorization hft' x
    refine ⟨CommAlgCat.of K B, Q, z, localizedAffinoidHom K Q _ ψ, ?_⟩
    have h := affinoidPointHom_test hp' hX' hft' _ Q ψ z
    rw [hx, Category.comp_id] at h
    exact h.symm
  choose B Q z g hg using hfac
  -- The images of these test points give local maps, which agree on overlaps.
  let l (k : I) : localizationFunctor.obj (A.smallChartSpectrum k.val) ⟶ Y :=
    g k ≫ p (B k) (Q k) (RingPoints.map f (z k))
  obtain ⟨L, hL⟩ := exists_hom_of_chartCover (fun k : I => k.val) hI l (by
    intro k j T a b hab
    have key := hp'.comp_map_eq_of_comp_eq hX' f hp (Q k) (Q j) (z k) (z j) (a ≫ g k) (b ≫ g j)
      (by rw [Category.assoc, Category.assoc, hg, hg, reassoc_of% hab])
    simpa only [l, Category.assoc] using key)
  -- The glued map computes along every map that factors through a test point.
  have hF : ∀ (T : LocalizedCategory.{u, u, u} (K := K)) (w : T ⟶ localizationFunctor.obj A₀)
      (C : Type u) [CommRing C] [Algebra K C] (R : FinitePolynomialPresentation K C)
      (y : RingPoints K X' C) (c : T ⟶ localized K R), c ≫ p' C R y = w →
      w ≫ e.inv ≫ L = c ≫ p C R (RingPoints.map f y) := by
    intro T w C _ _ R y c hc
    obtain ⟨T₀, hT⟩ := localizedObjectEquiv.surjective T
    change localizationFunctor.obj T₀ = T at hT
    subst hT
    obtain ⟨S, s, hs, J, hJ, hmJ⟩ :=
      exists_chartCover_refinement (fun k : I => k.val) hI (w ≫ e.inv)
    apply (cancel_epi (localizedQuasiIso s hs).hom).mp
    rw [localizedQuasiIso_hom]
    apply localizedHom_ext_of_chartCover (fun m : J => m.val) hJ
    intro m
    obtain ⟨k, g', hg'⟩ := hmJ m
    have h₁ : localizationFunctor.map (S.smallChartSpectrumInclusion m.val) ≫
        localizationFunctor.map s ≫ w ≫ e.inv ≫ L =
          g' ≫ g k ≫ p (B k) (Q k) (RingPoints.map f (z k)) := by
      calc _ = (g' ≫ localizationFunctor.map (A.smallChartSpectrumInclusion k.val)) ≫ L := by
              rw [hg']
              simp only [Category.assoc]
        _ = g' ≫ g k ≫ p (B k) (Q k) (RingPoints.map f (z k)) := by
              rw [Category.assoc, hL k]
    rw [h₁]
    have key := hp'.comp_map_eq_of_comp_eq hX' f hp (Q k) R (z k) y (g' ≫ g k)
      (localizationFunctor.map (S.smallChartSpectrumInclusion m.val) ≫
        localizationFunctor.map s ≫ c) (by
        simp only [Category.assoc]
        rw [hg, reassoc_of% hg']
        simp only [Iso.inv_hom_id, Category.comp_id, hc])
    simpa only [Category.assoc] using key
  refine ⟨e.inv ≫ L, fun A _ _ P x =>
    (hF _ (p' A P x) A P x (𝟙 _) (Category.id_comp _)).trans (Category.id_comp _), ?_⟩
  -- Uniqueness: étale test points are étale and jointly surjective.
  intro G hG
  apply etaleCoverHomExt (fun t : EtaleAffineTest K X' => p' t.algebra t.presentation t.point)
    (fun t => hp'.etale_map t.presentation t.point t.etale_point)
  · intro y
    obtain ⟨A, _, _, P, x, hx, hy⟩ := hp'.jointly_surjective y
    exact ⟨⟨CommAlgCat.of K A, P, x, hx⟩, hy⟩
  · intro t
    rw [hG, hF _ _ t.algebra t.presentation t.point (𝟙 _) (Category.id_comp _), Category.id_comp]

end Langlands.Analytic.SpaceAnalytification

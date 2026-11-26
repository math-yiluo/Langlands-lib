import Langlands.Geometry.Analytic.SchemeAnalytificationMorphismCompatibilityProof
import Langlands.Geometry.Analytic.SchemeAnalytificationMorphismProof
import Langlands.Geometry.Analytic.AffineAnalytificationJointSurjectivity

/-! # Analytic images and the algebraic center -/

noncomputable section

universe u w

namespace Langlands.Analytic.SchemeAnalytification

open _root_.CategoryTheory _root_.AlgebraicGeometry
open Langlands.Analytic.AffineSchemeAnalytification

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (f' : Y ⟶ Spec (CommRingCat.of K))
  [LocallyOfFiniteType f] [LocallyOfFiniteType f']
  (g : X ⟶ Y) (hg : g ≫ f' = f)

/-- The image of a map of analytifications is the inverse image of the algebraic image
under the target's center map. -/
theorem range_analytification :
    Set.range (MorphismExistence.analytification K f f' g hg) =
      center K f' ⁻¹' Set.range g := by
  let F := MorphismExistence.analytification K f f' g hg
  have hF := MorphismExistence.isAnalytificationMap_analytification K f f' g hg
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨center K f x, ((MorphismCompatibility.compatibility K f f' g hg F hF).1 x).symm⟩
  · intro z hz
    obtain ⟨V, y, rfl⟩ := exists_ι K f' z
    obtain ⟨x, hx⟩ := hz
    obtain ⟨U₀, hU₀, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (x := x)
      (U := g ⁻¹ᵁ (V : Y.Opens)) (by
        change g x ∈ (V : Y.Opens)
        exact hx.symm ▸ center_ι_mem K f' V y)
    let U : X.affineOpens := ⟨U₀, hU₀⟩
    have hUV' : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens) := hUV
    have : IsAffine (U : X.Opens).toScheme := hU₀
    have : IsAffine (V : Y.Opens).toScheme := V.2
    let res := g.resLE (V : Y.Opens) (U : X.Opens) hUV'
    let xU : (U : X.Opens).toScheme := ⟨x, hxU⟩
    let eU := (U : X.Opens).toScheme.isoSpec
    let q : Spec Γ((U : X.Opens), ⊤) := eU.hom xU
    have hq : affineOpenMap U q = x := by
      change (U : X.Opens).ι ((eU.hom ≫ eU.inv) xU) = x
      exact congrArg (fun k : (U : X.Opens).toScheme ⟶ (U : X.Opens).toScheme =>
        (U : X.Opens).ι (k xU)) eU.hom_inv_id
    have hres : Spec.map res.appTop ≫ affineOpenMap V = affineOpenMap U ≫ g := by
      change Spec.map (g.resLE (V : Y.Opens) (U : X.Opens) hUV').appTop ≫
        affineOpenMap V = affineOpenMap U ≫ g
      rw [affineOpenMap, affineOpenMap, Scheme.isoSpec_inv_naturality_assoc,
        Scheme.Hom.resLE_comp_ι, Category.assoc]
    have : IsOpenImmersion (affineOpenMap V) := by
      unfold affineOpenMap
      infer_instance
    have hqmap : Spec.map res.appTop q = localCenterPoint K f' V y := by
      apply (affineOpenMap V).isOpenEmbedding.injective
      change (Spec.map res.appTop ≫ affineOpenMap V) q = center K f' (ι K f' V y)
      rw [hres, Scheme.Hom.comp_apply, hq]
      exact hx
    have hprime : ∃ p : PrimeSpectrum (CoordinateRing (structureMap f U)),
        PrimeSpectrum.comap (openCoordinateMap g hg hUV').toRingHom p =
          AffineAnalytification.center K (chartPresentation K f' V) y :=
      ⟨q, hqmap⟩
    obtain ⟨a, ha⟩ := AffineAnalytification.exists_baseMap_eq K (chartPresentation K f' V)
      (chartPresentation K f U) (openCoordinateMap g hg hUV') y hprime
    exact ⟨ι K f U a, (hF U V hUV' a).trans (congrArg (ι K f' V) ha)⟩

/-- Lift a point of the target analytification whose center is in the image of the scheme
morphism. The chosen point belongs to the actual analytic fibre. -/
def liftAnalyticPoint (z : Space K f') (hz : center K f' z ∈ Set.range g) :
    {x : Space K f // MorphismExistence.analytification K f f' g hg x = z} :=
  Classical.choice (by
    have h : z ∈ Set.range (MorphismExistence.analytification K f f' g hg) := by
      rw [range_analytification]
      exact hz
    obtain ⟨x, hx⟩ := h
    exact ⟨⟨x, hx⟩⟩)

/-- Any family of scheme maps that hits every underlying scheme point analytifies to a
family that hits every underlying analytic point. -/
theorem analytification_jointlySurjective {I : Type w} {Xᵢ : I → Scheme.{u}}
    (fᵢ : ∀ i, Xᵢ i ⟶ Spec (CommRingCat.of K)) [∀ i, LocallyOfFiniteType (fᵢ i)]
    (gᵢ : ∀ i, Xᵢ i ⟶ Y) (hᵢ : ∀ i, gᵢ i ≫ f' = fᵢ i)
    (hcover : ∀ y : Y, ∃ i, y ∈ Set.range (gᵢ i)) (z : Space K f') :
    ∃ i, z ∈ Set.range (MorphismExistence.analytification K (fᵢ i) f' (gᵢ i) (hᵢ i)) := by
  obtain ⟨i, hi⟩ := hcover (center K f' z)
  refine ⟨i, ?_⟩
  rw [range_analytification]
  exact hi

end Langlands.Analytic.SchemeAnalytification

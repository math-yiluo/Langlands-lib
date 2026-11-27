import Langlands.Geometry.Analytic.AffineAnalytificationFiniteCharts
import Langlands.Geometry.Analytic.SchemeAnalytificationMorphismCompatibilityProof
import Langlands.Geometry.Analytic.SchemeAnalytificationMorphismProof
import Langlands.Geometry.Analytic.SchemeAnalytificationOpenGluing
import Langlands.Geometry.Analytic.SeparatedAnalytificationForward
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Sets.Compacts

/-! # Topological properness of finite scheme maps after analytification -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Filter Set Topology

private theorem proper_of_compact_preimage_neighborhoods {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {f : X → Y} (hf : Continuous f)
    (h : ∀ y, ∃ S ∈ 𝓝 y, IsCompact (f ⁻¹' S)) : IsProperMap f := by
  refine isProperMap_iff_ultrafilter_of_t2.mpr ⟨hf, ?_⟩
  intro F y hFy
  obtain ⟨S, hy, hS⟩ := h y
  obtain ⟨x, _, hx⟩ := hS.ultrafilter_le_nhds' F (hFy hy)
  exact ⟨x, hx⟩

namespace AffineAnalytification

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B) (f : A →ₐ[K] B)

/-- A finite algebra map induces a proper map on affine polynomial-locus analytifications. -/
theorem isProperMap_baseMap_of_finite (hf : f.toRingHom.Finite) : IsProperMap (baseMap K P Q f) := by
  apply proper_of_compact_preimage_neighborhoods (baseMap K P Q f).continuous
  intro y
  obtain ⟨m, s, rfl⟩ := exists_chart K P y
  let n := representative K P (m + 1)
  refine ⟨range (chart K P n.val), ?_, ?_⟩
  · rw [range_representative]
    exact range_chart_mem_nhds K P ⟨s, rfl⟩
  · obtain ⟨S, _, hS, _⟩ := FiniteCharts.exists_isFiniteBanach_preimage P Q f hf n
    rw [← hS]
    exact isCompact_range ((saturated K Q).presentation.atlas.isEmbedding_chart S).continuous

end AffineAnalytification

namespace SchemeAnalytification

open _root_.AlgebraicGeometry CategoryTheory AffineSchemeAnalytification MorphismExistence

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (f' : Y ⟶ Spec (CommRingCat.of K))
  [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (g : X ⟶ Y) (hg : g ≫ f' = f)

/-- Finite morphisms of schemes analytify to topologically proper maps when the target
is separated and both schemes are locally of finite type over the ground field. -/
theorem isProperMap_analytification_of_finite [IsFinite g] [IsSeparated f'] :
    IsProperMap (analytification K f f' g hg) := by
  let F := analytification K f f' g hg
  have hF := isAnalytificationMap_analytification K f f' g hg
  have hcenter := (MorphismCompatibility.compatibility K f f' g hg F hF).1
  let := SeparatedForward.t2Space_of_isSeparated K f'
  apply proper_of_compact_preimage_neighborhoods F.continuous
  intro y
  obtain ⟨V, z, rfl⟩ := exists_ι K f' y
  let U : X.affineOpens := ⟨_, V.property.preimage g⟩
  let hUV : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens) := le_rfl
  let r := g.resLE (V : Y.Opens) (U : X.Opens) hUV
  let : IsAffine ((V : Y.Opens) : Scheme) := V.property
  let : IsFinite r := by
    change IsFinite (g.resLE (V : Y.Opens) (g ⁻¹ᵁ (V : Y.Opens)) le_rfl)
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  have hfinite : (openCoordinateMap g hg hUV).toRingHom.Finite := r.finite_appTop
  let H := AffineAnalytification.baseMap K (chartPresentation K f' V) (chartPresentation K f U)
    (openCoordinateMap g hg hUV)
  have hH := AffineAnalytification.isProperMap_baseMap_of_finite K
    (chartPresentation K f' V) (chartPresentation K f U) (openCoordinateMap g hg hUV) hfinite
  obtain ⟨m, s, hs⟩ := AffineAnalytification.exists_chart K (chartPresentation K f' V) z
  let B := range (AffineAnalytification.chart K (chartPresentation K f' V) (m + 1))
  let e := OpenGluing.isOpenEmbedding_ι K f' V
  have hz : B ∈ 𝓝 z := AffineAnalytification.range_chart_mem_nhds K (chartPresentation K f' V) ⟨s, hs⟩
  refine ⟨ι K f' V '' B, e.isOpenMap.image_mem_nhds hz, ?_⟩
  have heq : F ⁻¹' (ι K f' V '' B) = ι K f U '' (H ⁻¹' B) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, hax⟩ := hx
      have hxU : x ∈ range (ι K f U) := by
        rw [← OpenGluing.range_ι]
        change g (center K f x) ∈ (V : Y.Opens)
        rw [← hcenter x, ← hax]
        exact center_ι_mem K f' V a
      obtain ⟨b, rfl⟩ := hxU
      refine ⟨b, ?_, rfl⟩
      have h := e.injective ((hF U V hUV b).symm.trans hax.symm)
      change H b ∈ B
      change H b = a at h
      rwa [h]
    · rintro ⟨b, hb, rfl⟩
      exact ⟨H b, hb, (hF U V hUV b).symm⟩
  rw [heq]
  exact (hH.isCompact_preimage (isCompact_range
    (AffineAnalytification.continuous_chart K (chartPresentation K f' V) (m + 1)))).image
      (OpenGluing.isOpenEmbedding_ι K f U).continuous

/-- Inverse image of compact supports for a finite scheme map after analytification. -/
def analytificationCompactPreimage [IsFinite g] [IsSeparated f'] :
    TopologicalSpace.Compacts (Space K f') →o TopologicalSpace.Compacts (Space K f) where
  toFun S := ⟨analytification K f f' g hg ⁻¹' S,
    (isProperMap_analytification_of_finite K f f' g hg).isCompact_preimage S.isCompact⟩
  monotone' := by
    intro S T h x hx
    exact h hx

end SchemeAnalytification

end Langlands.Analytic

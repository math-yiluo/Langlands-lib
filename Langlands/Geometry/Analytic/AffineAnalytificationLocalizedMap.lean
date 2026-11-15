import Langlands.Geometry.Analytic.AffineAnalytificationMap
import Langlands.Geometry.Analytic.CoherentStrongSaturationExtension

/-! # Analytic morphisms of polynomial-locus analytifications in the localized category -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory

namespace AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- A strong map into an atlas with directed charts has coherent bounded pullbacks: two
admissible target charts lie in a common chart, through which both pullbacks factor. -/
theorem hasCoherentPullbacks_of_hasDirectedCharts (f : StrongHom A B)
    (hB : B.atlas.HasDirectedCharts) : f.HasCoherentPullbacks := by
  intro i j k hj hk T η m hmj hmk α hα
  obtain ⟨q, hjq, hkq⟩ := hB j k
  have hq : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart q) :=
    hj.trans hjq
  have e1 := f.restriction_comm i i j q subset_rfl hjq hj hq
  have e2 := f.restriction_comm i i k q subset_rfl hkq hk hq
  rw [A.atlas.restriction_id] at e1 e2
  apply B.atlas.restriction_hom_ext k q hkq T
  calc (η.comp (f.pullback i k hk)).comp (B.atlas.restriction k q hkq)
      = η.comp ((f.pullback i k hk).comp (B.atlas.restriction k q hkq)) := rfl
    _ = η.comp (f.pullback i q hq) := by rw [← e2]; rfl
    _ = η.comp ((f.pullback i j hj).comp (B.atlas.restriction j q hjq)) := by rw [← e1]; rfl
    _ = (η.comp (f.pullback i j hj)).comp (B.atlas.restriction j q hjq) := rfl
    _ = (α.comp (B.atlas.restriction m j hmj)).comp (B.atlas.restriction j q hjq) := by
        rw [hα]
    _ = α.comp (B.atlas.restriction m q (hmj.trans hjq)) := by
        rw [B.atlas.restriction_comp m j q hmj hjq (hmj.trans hjq)]; rfl
    _ = (α.comp (B.atlas.restriction m k hmk)).comp (B.atlas.restriction k q hkq) := by
        rw [B.atlas.restriction_comp m k q hmk hkq (hmj.trans hjq)]; rfl

end AffinoidAtlasPresentation.StrongHom

namespace AffineAnalytification

open SaturatedAtlasPresentation

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] {B : Type w} [CommRing B] [Algebra K B]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

/-- The strong map of the affine analytifications induced by `f` has coherent pullbacks,
because the target atlas has directed charts. -/
theorem strongHom_hasCoherentPullbacks : (strongHom K P Q f).HasCoherentPullbacks :=
  (strongHom K P Q f).hasCoherentPullbacks_of_hasDirectedCharts (atlas_hasDirectedCharts K P)

/-- The morphism of saturated presentations induced by `f`: the extension of the strong map
`strongHom K P Q f` to all full local affinoid domains of both atlases. -/
def saturatedHom : saturated K Q ⟶ saturated K P :=
  (strongHom K P Q f).saturationExtension (strongHom_hasCoherentPullbacks K P Q f)

/-- The morphism `Spec(B)ᵃⁿ → Spec(A)ᵃⁿ` of analytic spaces induced by `f`, in the Library's
localized category of saturated presentations. -/
def localizedHom : localized K Q ⟶ localized K P :=
  localizationFunctor.map (saturatedHom K P Q f)

@[simp]
theorem saturatedHom_baseMap : (saturatedHom K P Q f).baseMap = baseMap K P Q f :=
  rfl

/-- The underlying continuous map of the localized morphism is the map of analytifications
induced by `f`. -/
theorem localizedSpaceFunctor_map_localizedHom :
    localizedSpaceFunctor.map (localizedHom K P Q f) = TopCat.ofHom (baseMap K P Q f) :=
  localizedSpaceFunctor_map (saturatedHom K P Q f)

end AffineAnalytification

end Langlands.Analytic

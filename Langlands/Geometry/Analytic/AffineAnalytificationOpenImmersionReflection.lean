import Langlands.Geometry.Analytic.AffineAnalytificationMonomorphismComparison
import Langlands.Geometry.Analytic.AnalyticImmersion
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Analytic open immersions of affine analytifications are algebraic -/

noncomputable section

universe u v

namespace Langlands.Analytic

open CategoryTheory

namespace SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- An analytic open immersion is a monomorphism. -/
theorem openImmersion.mono {X Y : LocalizedCategory.{u, v, v} (K := K)} {φ : X ⟶ Y}
    (hφ : openImmersion φ) : Mono φ := by
  obtain ⟨U, hU, e, rfl⟩ := hφ
  infer_instance

/-- An analytic open immersion is étale. -/
theorem openImmersion.etale {X Y : LocalizedCategory.{u, v, v} (K := K)} {φ : X ⟶ Y}
    (hφ : openImmersion φ) : etale φ := by
  obtain ⟨U, hU, e, rfl⟩ := hφ
  exact etale_comp (etale_of_isIso e.hom) (etaleOpenDomainStatement Y U hU)

end SaturatedAtlasPresentation

namespace AffineAnalytification

open SaturatedAtlasPresentation

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type v} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

/-- If the analytified map is an analytic open immersion, the map of affine
spectra is an open immersion of schemes. -/
theorem isOpenImmersion_of_openImmersion_localizedHom
    (hf : openImmersion (localizedHom K P Q f)) :
    _root_.AlgebraicGeometry.IsOpenImmersion
      (_root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.toRingHom)) := by
  have : Mono (localizedHom K P Q f) := hf.mono
  have : Epi (CommRingCat.ofHom f.toRingHom) := epi_of_mono_localizedHom P Q f
  have : Mono (_root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.toRingHom)) :=
    mono_specMap_of_epi _
  have hEt : f.toRingHom.Etale := (affineAnalytificationEtale K A B P Q f).2.2.mpr
    (isEtale_of_localizedHom_etale P Q f hf.etale)
  have : _root_.AlgebraicGeometry.Etale
      (_root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.toRingHom)) :=
    _root_.AlgebraicGeometry.HasRingHomProperty.Spec_iff.mpr hEt
  exact _root_.AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono _

end AffineAnalytification

end Langlands.Analytic

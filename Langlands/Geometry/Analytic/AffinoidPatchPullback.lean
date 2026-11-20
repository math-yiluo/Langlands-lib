import Langlands.Geometry.Analytic.SaturatedTopChartComparison
import Langlands.Geometry.Analytic.ChartDomainSpectralTests

/-! # Pullbacks of patch-preserving endomorphisms to an affinoid model -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : LocalizedCategory.{u, v, v} (K := K)}

/-- Preimage equality for an analytic domain yields a restriction to it. -/
theorem mapsTo_of_preimage_eq (E : (presentationOf X).AnalyticDomain) {φ : X ⟶ X}
    (h : localizedSpaceFunctor.map φ ⁻¹' E.carrier = E.carrier) :
    ∀ x ∈ E.carrier, localizedSpaceFunctor.map φ x ∈ E.carrier := by
  intro x hx
  change x ∈ localizedSpaceFunctor.map φ ⁻¹' E.carrier
  rw [h]
  exact hx

variable (E : (presentationOf X).AnalyticDomain) {S₀ : SaturatedAtlasPresentation.{u, v, v} K}
  (t : S₀.presentation.atlas.Index)
  (ht : ∀ i, range (S₀.presentation.atlas.chart i) ⊆ range (S₀.presentation.atlas.chart t))
  (ι : localizationFunctor.obj S₀ ≅ domainObj X E)

/-- The endomorphism of an affinoid model of a patch induced by an
endomorphism of the ambient object which maps the patch into itself. -/
def patchConj (φ : X ⟶ X) (h : ∀ x ∈ E.carrier, localizedSpaceFunctor.map φ x ∈ E.carrier) :
    localizationFunctor.obj S₀ ⟶ localizationFunctor.obj S₀ :=
  ι.hom ≫ domainRestrict E E φ h ≫ ι.inv

/-- The bounded pullback, on the greatest chart of an affinoid model of a
patch, of an endomorphism preserving the patch; the identity otherwise. -/
def patchPullback (φ : X ⟶ X) :
    BoundedAlgHom K (S₀.presentation.atlas.algebra t) (S₀.presentation.atlas.algebra t) := by
  classical
  exact if h : localizedSpaceFunctor.map φ ⁻¹' E.carrier = E.carrier then
    ((localizedTopTargetHomEquiv t ht).symm
      (patchConj E ι φ (mapsTo_of_preimage_eq E h))).pullbackAtTop t ht t
  else BoundedAlgHom.id K _

theorem patchPullback_of_preimage_eq (φ : X ⟶ X)
    (h : localizedSpaceFunctor.map φ ⁻¹' E.carrier = E.carrier) :
    patchPullback E t ht ι φ = ((localizedTopTargetHomEquiv t ht).symm
      (patchConj E ι φ (mapsTo_of_preimage_eq E h))).pullbackAtTop t ht t := by
  classical
  exact dite_eq_left h

end Langlands.Analytic.SaturatedAtlasPresentation

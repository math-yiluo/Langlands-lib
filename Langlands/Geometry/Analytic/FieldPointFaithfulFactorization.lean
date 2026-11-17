import Langlands.Geometry.Analytic.FieldPointFaithfulRestriction

/-! # Factorization through faithful full field-point test sources -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FaithfulCharacterQuotient

open Set CategoryTheory AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]
  {R S : PresentedAffinoidAlgebra K}
  [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)]

/-- The faithful quotient test source maps to the original small saturated
spectrum by the actual quotient map. -/
def sourceMap (χ : BoundedAlgHom K R L) :
    testSource.{u, v} χ ⟶ SmallAffinoidSpectrum.saturated.{u, v} R :=
  letI := small_spectrum.{u, v} χ
  SmallAffinoidSpectrum.map (map χ)

/-- Character-compatible restriction commutes with the quotient-source
factorizations as an equality of complete strong morphisms. -/
theorem sourceMap_naturality
    (χ : BoundedAlgHom K R L) (ψ : BoundedAlgHom K S L)
    (φ : BoundedAlgHom K S R) (h : χ.comp φ = ψ) :
    sourceMap χ ≫ SmallAffinoidSpectrum.map φ =
      testMap χ ψ φ h ≫ sourceMap ψ := by
  let := small_spectrum.{u, v} χ
  let := small_spectrum.{u, v} ψ
  change SmallAffinoidSpectrum.map (map χ) ≫ SmallAffinoidSpectrum.map φ =
    SmallAffinoidSpectrum.map (descend χ ψ φ h) ≫ SmallAffinoidSpectrum.map (map ψ)
  rw [← SmallAffinoidSpectrum.map_comp, ← SmallAffinoidSpectrum.map_comp,
    descend_comp_map]

variable [CompleteSpace L]

/-- The quotient's faithful full test point factors the original full
field point, including every chart evaluation. -/
theorem testPoint_sourceMap
    (χ : BoundedAlgHom K R L)
    (hd : DomainCompletedResidueSurjectivityStatement.{u}) :
    (testPoint χ hd).map (sourceMap χ) (testSource χ).hasAllLocalDomains =
      SmallAffinoidSpectrum.fieldPoint R hd χ := by
  let := small_spectrum.{u, v} χ
  change (SmallAffinoidSpectrum.fieldPoint (algebra χ) hd (character χ)).map
    (SmallAffinoidSpectrum.map (map χ)) _ =
      SmallAffinoidSpectrum.fieldPoint R hd χ
  rw [SmallAffinoidSpectrum.fieldPoint_map, character_comp_map]

end Langlands.Analytic.PresentedAffinoidAlgebra.FaithfulCharacterQuotient

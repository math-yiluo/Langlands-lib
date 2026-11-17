import Langlands.Geometry.Analytic.AffineAnalytificationRationalPointNaturalityStatement

/-! # Proof: naturality of the analytic points of algebraic rational points -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open Set Topology PresentedAffinoidAlgebra AnalyticAffineSpace
open Langlands.AlgebraicGeometry.PointTopology

section Chart

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] {B : Type w} [CommRing B] [Algebra K B]
  {P : FinitePolynomialPresentation K A} {Q : FinitePolynomialPresentation K B}
  {f : A →ₐ[K] B}

/-- The image under `φ` of the `t`-th generator of `P` pushed through `f` is the value
of the evaluation character of `φ` at the lifted generator value. -/
theorem character_generatorValue {φ : AlgPoint K B K} {k : ℕ} (hk : RadiusAdmits K Q φ k)
    (t : Fin P.arity) :
    character K Q hk (generatorValue K P Q f k t) =
      pointCoordinates K P (AlgPoint.precomp f φ) t := by
  rw [generatorValue_eq_algebraMap, character_algebraMap]
  rfl

/-- If `φ` lies in the `k`-th polydisc of `Q`, then `φ ∘ f` lies in the
`level k`-th polydisc of `P`. -/
theorem radiusAdmits_precomp {φ : AlgPoint K B K} {k : ℕ} (hk : RadiusAdmits K Q φ k) :
    RadiusAdmits K P (AlgPoint.precomp f φ) (level K P Q f k) := by
  intro t
  rw [← character_generatorValue hk t]
  exact ((spectrumPoint K Q hk).le_norm _).trans (norm_generatorValue_le K P Q f k t)

/-- The evaluation character of `φ` pulled back along the chart map induced by `f` is the
evaluation character of `φ ∘ f`. -/
theorem character_comp_chartMap {φ : AlgPoint K B K} {k : ℕ} (hk : RadiusAdmits K Q φ k) :
    (character K Q hk).comp (chartMap K P Q f k) =
      character K P (radiusAdmits_precomp (f := f) hk) := by
  apply PresentedAffinoidAlgebra.hom_ext_coordinate
  intro t
  have e1 := chartMap_coordinate K P Q f k t
  exact (congrArg (fun b => character K Q hk b) e1).trans
    ((character_generatorValue hk t).trans (character_coordinate K P _ t).symm)

theorem comap_chartMap_spectrumPoint {φ : AlgPoint K B K} {k : ℕ}
    (hk : RadiusAdmits K Q φ k) :
    BanachSpectrum.comap (chartMap K P Q f k).toBoundedRingHom (spectrumPoint K Q hk) =
      spectrumPoint K P (radiusAdmits_precomp (f := f) hk) := by
  apply BanachSpectrum.ext
  intro a
  change ‖character K Q hk (chartMap K P Q f k a)‖ =
    ‖character K P (radiusAdmits_precomp (f := f) hk) a‖
  rw [← character_comp_chartMap hk]
  rfl

end Chart

/-- The analytification map induced by `f` sends the analytic point of `φ` to the
analytic point of `φ ∘ f`. -/
theorem affineAnalytificationRationalPointNaturality :
    AffineAnalytificationRationalPointNaturalityStatement.{u, v, w} := by
  intro K _ _ _ A _ _ B _ _ P Q f φ
  have hk := radiusAdmits_minimalRadius K Q φ
  rw [analyticPoint, baseMap_chart, comap_chartMap_spectrumPoint hk]
  exact chart_spectrumPoint K P _

end Langlands.Analytic.AffineAnalytification

import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedMap
import Langlands.Geometry.Analytic.FullRecognitionEtaleMorphisms

/-! # Statement: flatness and unramifiedness at a point where the analytification is finite -/

universe u v w

namespace Langlands.Analytic.AffineAnalytification

/-- Statement (derived pointwise form of Berkovich 1993, Propositions 3.2.10 and 3.3.11,
over the affinoid base `K`, for the Library's polynomial-locus analytification): let `K`
be a complete nonarchimedean nontrivially normed field, `f : A → B` a map of
`K`-algebras with finite polynomial presentations `P`, `Q`, `g := saturatedHom K P Q f`,
`y` the point of the analytification of `B` given by a point `s` of the `m`-th chart,
and `q` the prime of `B` under `y` (the pullback of the kernel of `s`). If `g` is
finite at `y`, then `g` is unramified at `y` if and only if `f` is unramified at `q`, and
`g` is flat at `y` if and only if the local map `A_{f⁻¹(q)} → B_q` is flat. -/
def AffineAnalytificationFiniteGermComparisonStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Algebra K A] (B : Type w) [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : A →ₐ[K] B) (m : ℕ) (s : BanachSpectrum (algebra K Q m)),
    let g := saturatedHom K P Q f
    let y := chart K Q m s
    let q := s.kernel.comap
      (PolynomialLocus.algebraMap Q (AnalyticAffineSpace.polyradius K Q.arity m)).toRingHom
    AffinoidAtlasPresentation.StrongHom.IsFiniteAt (A := presentation K Q)
      (B := presentation K P) g y →
      ((AffinoidAtlasPresentation.StrongHom.IsUnramifiedAt (A := presentation K Q)
          (B := presentation K P) g y ↔
          (letI : Algebra A B := f.toRingHom.toAlgebra
           Algebra.IsUnramifiedAt A q)) ∧
        (AffinoidAtlasPresentation.StrongHom.IsFlatAt (A := presentation K Q)
          (B := presentation K P) g y ↔
          (Localization.localRingHom (q.comap f.toRingHom) q f.toRingHom rfl).Flat))

end Langlands.Analytic.AffineAnalytification

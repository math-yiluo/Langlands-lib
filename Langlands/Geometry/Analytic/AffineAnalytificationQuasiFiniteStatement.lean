import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedMap
import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms
import Mathlib.RingTheory.RingHom.QuasiFinite

/-! # Statement: the affine analytification detects quasi-finite maps -/

universe u v w

namespace Langlands.Analytic.AffineAnalytification

/-- Statement (Berkovich 1993, Corollary 3.1.7, over the affinoid base `K`, for the
Library's polynomial-locus analytification): for a complete nonarchimedean nontrivially
normed field `K`, commutative `K`-algebras `A`, `B` with finite polynomial presentations
`P`, `Q`, and a `K`-algebra map `f : A → B`, the ring map `f` is quasi-finite if and only
if the induced morphism `saturatedHom K P Q f` of analytifications is quasifinite, that
is, finite at every point. -/
def AffineAnalytificationQuasiFiniteStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Algebra K A] (B : Type w) [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : A →ₐ[K] B),
    f.toRingHom.QuasiFinite ↔
      AffinoidAtlasPresentation.StrongHom.IsQuasifinite (A := presentation K Q)
        (B := presentation K P) (saturatedHom K P Q f)

end Langlands.Analytic.AffineAnalytification

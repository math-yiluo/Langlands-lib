import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.RingHom.Unramified
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedMap
import Langlands.Geometry.Analytic.FullRecognitionEtaleMorphisms

/-! # Statement: affine analytification detects unramified, flat quasifinite and étale maps -/

universe u v w

namespace Langlands.Analytic.AffineAnalytification

/-- Statement (affine case of Berkovich 1993, Propositions 3.2.10 and 3.3.11, over the
ground field, for the Library's polynomial-locus model): for a complete nonarchimedean
nontrivially normed field `K`, commutative `K`-algebras `A` and `B` with finite polynomial
presentations `P` and `Q`, and a `K`-algebra map `f : A →ₐ[K] B`, the strong map
`saturatedHom K P Q f : Spec(B)ᵃⁿ → Spec(A)ᵃⁿ` of saturated presentations is
(1) unramified in the Library's sense of Berkovich 1993, Definition 3.3.4, if and only if
`f` is formally unramified; (2) flat (a flat quasifinite morphism, Definition 3.2.5) if and
only if `f` is flat and quasi-finite; (3) étale (Definition 3.3.4) if and only if `f` is
étale. -/
def AffineAnalytificationEtaleStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Algebra K A] (B : Type w) [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : A →ₐ[K] B),
    (f.toRingHom.FormallyUnramified ↔
        AffinoidAtlasPresentation.StrongHom.IsUnramified (A := presentation K Q)
          (B := presentation K P) (saturatedHom K P Q f)) ∧
      ((f.toRingHom.Flat ∧ f.toRingHom.QuasiFinite) ↔
        AffinoidAtlasPresentation.StrongHom.IsFlat (A := presentation K Q)
          (B := presentation K P) (saturatedHom K P Q f)) ∧
      (f.toRingHom.Etale ↔
        AffinoidAtlasPresentation.StrongHom.IsEtale (A := presentation K Q)
          (B := presentation K P) (saturatedHom K P Q f))

end Langlands.Analytic.AffineAnalytification

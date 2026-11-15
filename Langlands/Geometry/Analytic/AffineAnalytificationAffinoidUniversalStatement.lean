import Langlands.Geometry.Analytic.AffineAnalytificationAffinoidMap
import Langlands.Geometry.Analytic.AffineAnalytificationSeminorm
import Langlands.Geometry.Analytic.DirectedAtlasComposition

/-! # Statement: strong maps from affinoid spectra to an affine analytification -/

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open CategoryTheory AffinoidAtlasPresentation AnalyticAffineSpace

/-- For every presented affinoid algebra `R`, strong maps from the singleton atlas
of `M(R)` to the polynomial-locus analytification of `A` correspond to `K`-algebra
maps `A → R`, naturally in `R` and in `A`:
(1) every admissible pullback of a strong map `F` recovers `strongHomAlgHom F` on
the coordinate-algebra image of `A`; (2) and (3) `affinoidStrongHom` and
`strongHomAlgHom` are mutually inverse; (4) the image of a point `x` has the
seminorm `a ↦ x (φ a)`; (5) precomposition with the strong map of a bounded
algebra map `g : R → R'` corresponds to `φ ↦ g ∘ φ`; (6) composition with the
induced map of a `K`-algebra map `f : A → B` corresponds to `ψ ↦ ψ ∘ f`. -/
def AffineAnalytificationAffinoidUniversalStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A),
    (∀ (R : PresentedAffinoidAlgebra K)
      (F : StrongHom (PresentedAffinoidSpace.atlasPresentation (Opposite.op R))
        (presentation K P))
      (j : (presentation K P).atlas.Index)
      (h : F.baseMap '' Set.range
          ((PresentedAffinoidSpace.atlasPresentation (Opposite.op R)).atlas.chart PUnit.unit) ⊆
        Set.range ((presentation K P).atlas.chart j))
      (a : A),
      F.pullback PUnit.unit j h (PolynomialLocus.algebraMap P (polyradius K P.arity j.val) a) =
        strongHomAlgHom F a) ∧
    (∀ (R : PresentedAffinoidAlgebra K) (φ : A →ₐ[K] R),
      strongHomAlgHom (affinoidStrongHom K P R φ) = φ) ∧
    (∀ (R : PresentedAffinoidAlgebra K)
      (F : StrongHom (PresentedAffinoidSpace.atlasPresentation (Opposite.op R))
        (presentation K P)),
      affinoidStrongHom K P R (strongHomAlgHom F) = F) ∧
    (∀ (R : PresentedAffinoidAlgebra K) (φ : A →ₐ[K] R) (x : BanachSpectrum R) (a : A),
      pointSeminorm K P ((affinoidStrongHom K P R φ).baseMap x) a = x (φ a)) ∧
    (∀ (R R' : PresentedAffinoidAlgebra K) (g : R ⟶ R') (φ : A →ₐ[K] R),
      (PresentedAffinoidSpace.strongAtlasMap g.op).compOfDirected (affinoidStrongHom K P R φ)
          (PresentedAffinoidSpace.atlasPresentation_hasDirectedCharts (Opposite.op R))
          (atlas_hasDirectedCharts K P) =
        affinoidStrongHom K P R' (g.toAlgHom.comp φ)) ∧
    (∀ (B : Type w) [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
      (f : A →ₐ[K] B) (R : PresentedAffinoidAlgebra K) (ψ : B →ₐ[K] R),
      (affinoidStrongHom K Q R ψ).compOfDirected (strongHom K P Q f)
          (atlas_hasDirectedCharts K Q) (atlas_hasDirectedCharts K P) =
        affinoidStrongHom K P R (ψ.comp f))

end Langlands.Analytic.AffineAnalytification

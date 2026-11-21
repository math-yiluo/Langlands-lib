import Langlands.Geometry.Analytic.AffineAnalytificationGroundFieldComparisonStatement
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityProof
import Langlands.Geometry.Analytic.GroundFieldExtensionMaps

/-! # Naturality of the actual strong affine scalar-extension comparisons -/

universe u u' v w

namespace Langlands.Analytic.AffineAnalytification

open Set AffinoidAtlasPresentation
open scoped TensorProduct

section Coordinates

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] {A : Type v} [CommRing A] [Algebra K A]
  (P : FinitePolynomialPresentation K A)

/-- The bounded chart equation on the original algebra characterizing the
strong comparison, in the direction from the extended atlas to the new affine atlas. -/
def RespectsBaseChangeCoordinates
    (f : CompatibleStrongHom
      (IndexedAffinoidAtlas.GroundFieldExtension.presentation K L (atlas K P))
      (presentation L (baseChangePresentation K L P))) : Prop :=
  let Q := baseChangePresentation K L P
  let S := IndexedAffinoidAtlas.GroundFieldExtension.presentation K L (atlas K P)
  let T := presentation L Q
  ∀ (i : ChartIndex K P) (j : ChartIndex L Q)
    (h : f.baseMap '' range (S.atlas.chart i) ⊆ range (T.atlas.chart j)) (a : A),
    f.pullback i j h
      (PolynomialLocus.algebraMap Q (AnalyticAffineSpace.polyradius L Q.arity j.val)
        ((1 : L) ⊗ₜ[K] a)) =
      PresentedAffinoidAlgebra.GroundFieldExtension.iota K L (algebra K P i.val)
        (PolynomialLocus.algebraMap P (AnalyticAffineSpace.polyradius K P.arity i.val) a)

end Coordinates

open LocalizedFunctorialityComparison (compatibleHom)

/-- Every pair of strong comparisons satisfying the specified coordinate
equations forms a natural square with the two actual induced compatible maps. -/
def AffineAnalytificationGroundFieldNaturalityStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type u') [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [NormedAlgebra K L] (A : Type v) [CommRing A] [Algebra K A]
    (B : Type w) [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (R : FinitePolynomialPresentation K B) (φ : A →ₐ[K] B),
    let PL := baseChangePresentation K L P
    let RL := baseChangePresentation K L R
    let S (C : AffinoidAtlasPresentation.{u, u, 0} K) :=
      IndexedAffinoidAtlas.GroundFieldExtension.presentation K L C.atlas
    ∀ (cP : CompatibleStrongHom (S (presentation K P)) (presentation L PL))
      (cR : CompatibleStrongHom (S (presentation K R)) (presentation L RL)),
      RespectsBaseChangeCoordinates K L P cP → RespectsBaseChangeCoordinates K L R cR →
        (AffinoidAtlasPresentation.GroundFieldExtension.compatibleMap K L
          (compatibleHom P R φ)).comp cP =
          cR.comp (compatibleHom PL RL (Algebra.TensorProduct.map (AlgHom.id L L) φ))

end Langlands.Analytic.AffineAnalytification

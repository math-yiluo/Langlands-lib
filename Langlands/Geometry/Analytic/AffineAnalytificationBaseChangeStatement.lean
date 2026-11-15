import Langlands.Geometry.Analytic.AffineAnalytificationScalarExtension
import Langlands.Geometry.Analytic.AffineAnalytificationRationalPoints

/-! # Statement: the base-change map of affine analytifications -/

universe u u' v

namespace Langlands.Analytic.AffineAnalytification

open Set Langlands.AlgebraicGeometry.PointTopology

/-- Statement (Berkovich 1990, §2.3 and Remark 3.4.2; Conrad 2011, p.19): let `K → L` be
an extension of complete nonarchimedean nontrivially normed fields, with `L` a normed
`K`-algebra, and let `P` be a finite polynomial presentation of a commutative
`K`-algebra `A`. For the canonical map `baseChangeMap K L P : (X_L)^an → X^an`,
`X = Spec A`, from the polynomial-locus analytification of `L ⊗[K] A` over `L`:
1. the map is surjective;
2. for every `K`-rational point `φ : A →ₐ[K] K`, the fibre over the analytic point of `φ`
   is the single analytic point of the `L`-rational point of `L ⊗[K] A` obtained from `φ`,
   that is, of `1 ⊗ a ↦ φ a` (the image of `φ` under `X(K) → X(L)`, followed by
   Mathlib's identification of `A →ₐ[K] L` with `L ⊗[K] A →ₐ[L] L`). -/
def AffineAnalytificationBaseChangeStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type u') [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [NormedAlgebra K L]
    (A : Type v) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A),
    Function.Surjective (baseChangeMap K L P) ∧
    ∀ φ : AlgPoint K A K,
      baseChangeMap K L P ⁻¹' {analyticPoint K P φ} =
        {analyticPoint L (baseChangePresentation K L P)
          (AlgPoint.ofAlgHom (Algebra.TensorProduct.liftEquivRight K L A L
            (AlgPoint.mapCoefficients (Algebra.ofId K L) φ).toAlgHom))}

end Langlands.Analytic.AffineAnalytification

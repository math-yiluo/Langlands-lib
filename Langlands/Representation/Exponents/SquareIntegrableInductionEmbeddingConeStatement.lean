import Langlands.Representation.Exponents.SquareIntegrableActualJacquetConeStatement
import Langlands.Representation.Induction.Parabolic

/-! # Strict scalar cones from actual normalized induction embeddings -/

namespace Langlands

universe uF uV

/-- An actual embedding of a nonzero analytically square-integrable smooth
representation in normalized upper induction forces the real part of the
inducing split-centre scalar character into the strict positive root cone. -/
def SquareIntegrableInductionEmbeddingConeStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
        [Nontrivial π],
        T.IsSquareIntegrable π.representation →
        ∀ (B : GeneralLinear.BlockShape n)
          (σ : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)),
          SmoothRep.IsSubrepresentation π
            ((T.normalizedParabolicInductionFunctor B).obj σ) →
          ∀ (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
            (∀ (a : Fin B.length → F.Carrierˣ) (v : σ),
              σ.representation (B.blockScalarLevi F.Carrier a) v =
                (χ a : ℂ) • v) →
            ∀ (x : Fin B.length → ℝ), T.IsRealPartOf χ x →
              Exponents.IsPositiveRootCone x

end Langlands

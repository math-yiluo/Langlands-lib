import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.InfiniteAdelicLinearRealization
import Langlands.Representation.Archimedean.SmoothVectors

/-! # Smooth-vector factorization for reductive adelic groups -/

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Archimedean AdelicGroupPoints InfiniteAdelicGroupPoints

universe u uE

/-- Finite-level, archimedean smooth vectors are finite sums of smooth adelic
test-function averages for the existing full adelic Haar measure. -/
def AdelicSmoothVectorFactorizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G),
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := reductiveChartedSpace F G hG
    let A := AdelicGroupPoints F G
    let ν : Measure A := Measure.haar
    ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      (π : A →* (E →L[ℂ] E)), IsContinuousRepresentation π →
      ∀ (L : OpenSubgroup (FiniteAdelicGroupPoints F G)) (v : E),
        Archimedean.IsSmoothVector 𝓘(ℝ, smoothModel F hG.smoothDimension)
          (π.comp (ofInfinite F G).toMonoidHom) v →
        (∀ l : L, π (ofFinite F G l) v = v) →
        ∃ (n : ℕ) (w : Fin n → E) (k : Fin n → A → ℂ),
          (∀ i, Archimedean.IsSmoothVector 𝓘(ℝ, smoothModel F hG.smoothDimension)
              (π.comp (ofInfinite F G).toMonoidHom) (w i) ∧
            IsAdelicTestFunction F G (k i) ∧ Integrable (k i) ν ∧
            Integrable (fun g => k i g • π g (w i)) ν) ∧
          v = ∑ i, ∫ g, k i g • π g (w i) ∂ν

end Langlands.Global

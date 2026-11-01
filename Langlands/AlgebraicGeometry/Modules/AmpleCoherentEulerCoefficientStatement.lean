import Langlands.AlgebraicGeometry.Modules.CoherentEulerCoefficientSupport
import Langlands.AlgebraicGeometry.Modules.CoherentIntegralIdealFiltrationStatement
import Langlands.AlgebraicGeometry.Picard.Ample

/-! # The ample coherent Euler coefficient criterion -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- The ample coefficient criterion in a fixed support dimension, for actual
proper coherent sheaves over arbitrary fields. -/
def AmpleCoherentEulerCoefficientInDimension (d : ℕ) : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    [IsNoetherian X] [X.IsSeparated] (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (L : Picard.LineBundle X),
    L.IsAmple → HasSupportDimensionLT M (d + 1) →
      EulerCoefficientDetectsSupport f M hM L d

/-- Finite coherent filtrations by integral closed ideal sheaves imply the
ample coherent Euler coefficient criterion in every finite support dimension. -/
def AmpleCoherentEulerCoefficientReductionStatement : Prop :=
  CoherentIntegralIdealFiltrationStatement.{u} →
    ∀ d : ℕ, AmpleCoherentEulerCoefficientInDimension.{u} d

end Langlands.AlgebraicGeometry.Modules.DerivedSections

import Langlands.Global.AdelicEisensteinConstantTermStatement
import Langlands.Global.AdelicEisensteinContinuationStatement

/-! # Meromorphy of constant-term evaluations of Eisenstein continuations -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Local uniform-growth meromorphic presentations give meromorphic scalar
constant-term values on one common open dense set in the chart. -/
def EisensteinConstantTermContinuationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G H : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine H.X.left]
    (j : H ⟶ G) [IsClosedImmersion j.hom.hom.left]
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j))]
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (n : ℕ) (E : (Fin n → ℂ) → AdelicGroupPoints F G → ℂ),
    (∀ s₀ : Fin n → ℂ, ∃ W : TopologicalSpace.Opens (Fin n → ℂ), s₀ ∈ W ∧
      ∃ (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G))
        (f : W → UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L) (D : Set W),
        IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f D ∧
        ∀ s ∈ D, UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (f s) = E s) →
    ∃ U : Set (Fin n → ℂ), IsOpen U ∧ Dense U ∧
      ∀ g, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun s => subgroupConstantTerm F j (E s) g) U

end Langlands.Global

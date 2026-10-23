import Langlands.AlgebraicGeometry.RelativeDifferentials
import Langlands.AlgebraicGeometry.LocallyFreeRank
import Langlands.AlgebraicGeometry.ModuleDual
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Finite local basis and rank targets for actual scheme modules -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme

/-- Smooth differentials have finite local bases, with rank prescribed by
geometric smooth relative dimension when one is specified. -/
def SmoothDifferentialsFiniteLocalBasisRankStatement : Prop :=
  ∀ (X S : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ S),
    (Smooth f →
      ∃ q : SheafOfModules.LocalGeneratorsData.{u} (relativeDifferentials f),
        q.IsLocallyFreeData ∧ q.IsFiniteType) ∧
    ∀ n : ℕ, SmoothOfRelativeDimension n f →
      Modules.IsLocallyFreeOfRank (relativeDifferentials f) n

namespace Modules

/-- Actual module pullback preserves finite local bases and each specified
finite local rank. -/
def PullbackFiniteLocalBasisRankStatement : Prop :=
  ∀ (X Y : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ Y) (M : Y.Modules),
    ((∃ q : SheafOfModules.LocalGeneratorsData.{u} M,
        q.IsLocallyFreeData ∧ q.IsFiniteType) →
      ∃ q : SheafOfModules.LocalGeneratorsData.{u}
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M),
        q.IsLocallyFreeData ∧ q.IsFiniteType) ∧
    ∀ n : ℕ, IsLocallyFreeOfRank M n →
      IsLocallyFreeOfRank ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) n

/-- The actual internal dual preserves finite local bases and each specified
finite local rank. -/
def DualFiniteLocalBasisRankStatement : Prop :=
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (M : X.Modules),
    ((∃ q : SheafOfModules.LocalGeneratorsData.{u} M,
        q.IsLocallyFreeData ∧ q.IsFiniteType) →
      ∃ q : SheafOfModules.LocalGeneratorsData.{u} (dual M),
        q.IsLocallyFreeData ∧ q.IsFiniteType) ∧
    ∀ n : ℕ, IsLocallyFreeOfRank M n → IsLocallyFreeOfRank (dual M) n

end Modules
end Langlands.Scheme

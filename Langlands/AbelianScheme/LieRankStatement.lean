import Langlands.AbelianScheme.Lie
import Langlands.AlgebraicGeometry.LocallyFreeRank

/-! # Local freeness and rank targets for the relative Lie module -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

variable {S : AlgebraicGeometry.Scheme.{u}}

/-- The actual relative Lie module of an abelian scheme is finite locally free. -/
def LieFiniteLocallyFreeStatement (A : AbelianScheme S) : Prop :=
  SheafOfModules.IsLocallyFree (R := S.ringCatSheaf) A.Lie ∧
    SheafOfModules.IsFiniteType (R := S.ringCatSheaf) A.Lie

/-- A specified constant relative dimension gives the same local rank for the Lie module. -/
def LieRankStatement (A : AbelianScheme S) (g : ℕ) : Prop :=
  A.HasRelativeDimension g →
    Langlands.Scheme.Modules.IsLocallyFreeOfRank A.Lie g

/-- The combined local-freeness and fixed-relative-dimension rank target. -/
def LieLocalFreenessRankStatement (A : AbelianScheme S) : Prop :=
  LieFiniteLocallyFreeStatement A ∧ ∀ g : ℕ, LieRankStatement A g

end Langlands.AbelianScheme

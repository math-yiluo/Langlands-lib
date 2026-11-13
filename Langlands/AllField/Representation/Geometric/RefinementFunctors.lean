import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.AllField.Representation.Geometric.RefinementDefinitions
/-! Actual normalized induction and Jacquet functors inside product Levis. -/

noncomputable section

open scoped NNReal

namespace Langlands.AllField.Geometric
open Langlands.Geometric
open Langlands.AllField.Geometric

open CategoryTheory
open Langlands.GeneralLinear

universe uF uV uW uX

variable {F : Type uF} [CommRing F] {n : ℕ}
  (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} {W : Type uW} {X : Type uX}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F]

end Topology
end Langlands.AllField.Geometric

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open CategoryTheory
open Langlands.Geometric
open Langlands.AllField.Geometric

universe uF uV uW

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
  (S : BlockRefinement B) {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The actual local-field refined Jacquet action, with the explicit full product modulus. -/
def normalizedRefinedJacquet (ρ : Representation ℂ (B.Levi F) V) :
    Representation ℂ (refinedLevi F B S) (RefinedJacquetModule B S ρ) :=
  normalizedRefinedJacquetOf B S (T.refinedLeviModulus B S) ρ

/-- Its action on quotient classes uses the canonical inverse half. -/
theorem normalizedRefinedJacquet_mk (ρ : Representation ℂ (B.Levi F) V)
    (m : refinedLevi F B S) (v : V) :
    T.normalizedRefinedJacquet B S ρ m (refinedJacquetMk B S ρ v) =
      (T.refinedLeviInverseHalfModulus B S m : ℂ) •
        refinedJacquetMk B S ρ (ρ m.val v) :=
  by simpa only [normalizedRefinedJacquet, refinedLeviInverseHalfModulus_apply] using
    normalizedRefinedJacquetOf_mk B S (T.refinedLeviModulus B S) ρ m v

/-- Refined Jacquet maps preserve the actual quotient representatives. -/
def normalizedRefinedJacquetMap
    {ρ : Representation ℂ (B.Levi F) V}
    {τ : Representation ℂ (B.Levi F) W} (f : ρ.IntertwiningMap τ) :
    (T.normalizedRefinedJacquet B S ρ).IntertwiningMap
      (T.normalizedRefinedJacquet B S τ) :=
  normalizedRefinedJacquetOfMap B S (T.refinedLeviModulus B S) f

end Langlands.LocalFieldData

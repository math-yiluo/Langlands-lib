import Langlands.AllFieldBZ.Representation.Geometric.RefinementDefinitions
import Langlands.Representation.Geometric.RefinementFunctors

/-!
# All-field port of `Langlands.Representation.Geometric.RefinementFunctors`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.RefinementFunctors` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open scoped NNReal
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric
open Langlands.GeneralLinear
open CategoryTheory
universe uF uV uW uX

variable {F : Type uF} [CommRing F] {n : ℕ}
  (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} {W : Type uW} {X : Type uX}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

section Topology
variable [TopologicalSpace F] [IsTopologicalRing F]

end Topology
end Langlands.AllFieldBZ.Geometric
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.Geometric
open CategoryTheory
universe uF uV uW

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
  (S : BlockRefinement B) {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The actual p-adic refined Jacquet action, with the explicit full product modulus. -/
def normalizedRefinedJacquet (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    Representation ℂ (refinedLevi F.Carrier B S) (RefinedJacquetModule B S ρ) :=
  normalizedRefinedJacquetOf B S (T.refinedLeviModulus B S) ρ

/-- Its action on quotient classes uses the canonical inverse half. -/
theorem normalizedRefinedJacquet_mk (ρ : Representation ℂ (B.Levi F.Carrier) V)
    (m : refinedLevi F.Carrier B S) (v : V) :
    T.normalizedRefinedJacquet B S ρ m (refinedJacquetMk B S ρ v) =
      (T.refinedLeviInverseHalfModulus B S m : ℂ) •
        refinedJacquetMk B S ρ (ρ m.val v) :=
  by simpa only [normalizedRefinedJacquet, refinedLeviInverseHalfModulus_apply] using
    normalizedRefinedJacquetOf_mk B S (T.refinedLeviModulus B S) ρ m v

/-- Refined Jacquet maps preserve the actual quotient representatives. -/
def normalizedRefinedJacquetMap
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W} (f : ρ.IntertwiningMap τ) :
    (T.normalizedRefinedJacquet B S ρ).IntertwiningMap
      (T.normalizedRefinedJacquet B S τ) :=
  normalizedRefinedJacquetOfMap B S (T.refinedLeviModulus B S) f

/-- The actual normalized Jacquet functor of a refinement of a product Levi. -/
def normalizedRefinedJacquetFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact normalizedRefinedJacquetFunctorOf B S (T.refinedLeviModulus B S)
    (T.isOpen_ker_refinedLeviModulus B S)

/-- The normalized refined induction action uses the positive half of the same modulus. -/
def normalizedRefinedInduced (σ : Representation ℂ (refinedLevi F.Carrier B S) V) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    Representation ℂ (B.Levi F.Carrier)
      (Induction.SmoothFunctions (refinedParabolic F.Carrier B S)
        (twist (T.refinedParabolicHalfModulus B S)
          (σ.comp (refinedLeviProjection F.Carrier B S)))) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact normalizedRefinedInducedOf B S (T.refinedLeviHalfModulus B S) σ

/-- The normalized induced map is postcomposition by the original intertwiner. -/
def normalizedRefinedInducedMap
    {σ : Representation ℂ (refinedLevi F.Carrier B S) V}
    {τ : Representation ℂ (refinedLevi F.Carrier B S) W} (f : σ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    (T.normalizedRefinedInduced B S σ).IntertwiningMap
      (T.normalizedRefinedInduced B S τ) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact normalizedRefinedInducedOfMap B S (T.refinedLeviHalfModulus B S) f

/-- Normalized induction between the actual smooth categories of product Levi subgroups. -/
def normalizedRefinedInductionFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact normalizedRefinedInductionFunctorOf B S (T.refinedLeviHalfModulus B S)

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData

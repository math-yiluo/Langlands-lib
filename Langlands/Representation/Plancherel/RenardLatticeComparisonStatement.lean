import Langlands.Representation.Plancherel.RenardRepresentativeData

/-! # Actual split-component lattice comparison for Renard's representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Plancherel.RenardCartan

/-- The actual norm kernel pulls back to the norm kernel of a split component. -/
def SplitComponentKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (Z : GroupScheme (Spec (CommRingCat.of F))), IsConnectedReductive Z →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ Z),
      IsSplitComponent s →
      (rationalCommonNormKernel Z).comap (rationalPoints.map s) =
        rationalCommonNormKernel T.toGrp

/-- The split-component valuation image has finite index in the actual image,
and valuation gives a bijection from the uniformizer subgroup onto that image. -/
def SplitComponentLatticeStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (Z : GroupScheme (Spec (CommRingCat.of F))), IsConnectedReductive Z →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ Z),
      IsSplitComponent s →
      (splitValuationImage s).FiniteIndex ∧
      Set.BijOn (rationalCharacterValuation Z).rangeRestrict
        (C0 T s : Set (rationalPoints Z))
        (splitValuationImage s : Set (rationalCharacterValuationImage Z))

/-- There are finite actual-point representatives of all full lattice cosets.
Every such transversal gives a full valuation section by multiplication with
`C0`, and the product pairs have distinct valuation values. -/
def FullLatticeRepresentativeStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (Z : GroupScheme (Spec (CommRingCat.of F))), IsConnectedReductive Z →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ Z),
      IsSplitComponent s →
      (∃ F0 : Set (rationalPoints Z), IsFiniteLatticeTransversal s F0) ∧
      ∀ F0 : Set (rationalPoints Z), IsFiniteLatticeTransversal s F0 →
        IsValuationSection (tildeC0 s F0) ∧
        Function.Injective (fun cf : (C0 T s) × F0 =>
          rationalCharacterValuation Z (cf.1.val * cf.2.val))

/-- The split-component comparison and full representative targets needed
before cutting the actual centralizer lattice by its dominant chamber. -/
def RenardLatticeComparisonStatement : Prop :=
  SplitComponentKernelStatement.{u} ∧ SplitComponentLatticeStatement.{u} ∧
    FullLatticeRepresentativeStatement.{u}

end Langlands.Plancherel.RenardCartan

import Langlands.Representation.Aubert.General.SemidirectQuotientCompactness
import Langlands.Representation.Aubert.General.RationalSupportInduction
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction

/-! # Compact quotient representatives inside actual standard Levis -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hStandard : StandardCocharacterStatement.{u})

local instance rationalLeviQuotientPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]

local notation "dec" => isSemidirectDecomposition_of_standardCocharacterStatement
  i ν hStandard hG hi hν

include hInter hG hi hν hStandard

/-- A compact representative set for the literal standard parabolic quotient
inside a Levi, obtained by projecting ambient compact representatives. -/
def standardLeviCompactCosetCover
    (K : Finset (SimpleRoot i ν)) (I : Finset K)
    [CompactSpace (Induction.LeftQuotient (parabolic i ν (leviIndex K I)))] :
    {C : Set (levi i ν K) // IsCompact C ∧
      ∀ m : levi i ν K,
        ∃ q ∈ (parabolic i ν (leviIndex K I)).subgroupOf (levi i ν K),
          ∃ c ∈ C, m = q * c} := by
  apply Classical.choice
  have hcover := (dec K).hasCompactCosetCover_subgroupOf_levi
    (standardParabolic_isClosed_of_standardCocharacterStatement
      i ν hStandard hG hi hν K)
    (continuous_standard_projection i ν hStandard hG hi hν K)
    (parabolic_le_of_subset i ν hInter hG hi hν hStandard
      (leviIndex K I) K (leviIndex_subset K I))
    ((unipotent_le_of_subset i ν hInter hG hi hν
      (leviIndex K I) K (leviIndex_subset K I)).trans
      (unipotent_le_parabolic i ν (leviIndex K I)))
    (Induction.hasCompactCosetCover_of_compactSpace
      (parabolic i ν (leviIndex K I)))
  obtain ⟨C, hC, hCcover⟩ := hcover
  exact ⟨⟨C, hC, hCcover⟩⟩

/-- Compactness of the ambient fine-parabolic quotient gives compactness of
the exact subgroup-of-Levi quotient used by inside-Levi induction. -/
theorem compactSpace_leftQuotient_in_levi_of_ambient
    (K : Finset (SimpleRoot i ν)) (I : Finset K)
    [CompactSpace (Induction.LeftQuotient (parabolic i ν (leviIndex K I)))] :
    CompactSpace (Induction.LeftQuotient
      ((parabolic i ν (leviIndex K I)).subgroupOf (levi i ν K))) := by
  let C := standardLeviCompactCosetCover i ν hInter hG hi hν hStandard K I
  exact Induction.compactSpace_of_hasCompactCosetCover
    ⟨C.val, C.property.1, C.property.2⟩

/-- The uniform dynamic quotient-compactness statement supplies every literal
inside-Levi quotient, with its canonical quotient topology. -/
theorem compactSpace_leftQuotient_in_levi_of_dynamic
    (hcompact : BruhatTits.DynamicParabolicQuotientCompactStatement.{u})
    (K : Finset (SimpleRoot i ν)) (I : Finset K) :
    CompactSpace (Induction.LeftQuotient
      ((parabolic i ν (leviIndex K I)).subgroupOf (levi i ν K))) := by
  let := compactSpace_leftQuotient_parabolic
    i ν hcompact hStandard hG hi hν (leviIndex K I)
  exact compactSpace_leftQuotient_in_levi_of_ambient
    i ν hInter hG hi hν hStandard K I

end Langlands.Aubert.General.RationalPointFamily

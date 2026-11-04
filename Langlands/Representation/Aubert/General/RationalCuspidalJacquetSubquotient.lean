import Langlands.Representation.Aubert.General.RationalMinimalJacquet
import Langlands.Representation.Aubert.General.RestrictedLeviTopology
import Langlands.Representation.Aubert.General.SupportCategoryReductions

/-! # An irreducible cuspidal subquotient of a nonzero standard Jacquet module -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe uI uG uV u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

open SmoothRep

section Subquotient

variable {H : Type uG} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
  [NonarchimedeanGroup H]
  {Index : Type uI} {P M U : Finset Index → Subgroup H}
  {hU : ∀ I, IsClosed (U I : Set H)}
  {I : Finset Index} {hM : IsClosed (M I : Set H)}
  {hI : ∀ K : Finset I,
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I))
      ((U (leviIndex I K)).subgroupOf (M I))}

/-- Exactness of all proper inner Jacquet functors makes Levi cuspidality
pass to actual subquotients. -/
theorem IsLeviCuspidal.of_isSubquotient
    (hUc : ∀ K : Finset I, Jacquet.Localization.IsLimitOfCompactSubgroups
      ((U (leviIndex I K)).subgroupOf (M I)))
    {E σ : SmoothRep.{0, uG, uV} ℂ (M I)}
    (hE : IsLeviCuspidal P M U hU I hM hI E)
    (hσ : SmoothRep.IsSubquotient σ E) :
    IsLeviCuspidal P M U hU I hM hI σ := by
  let := hM.locallyCompactSpace
  intro K
  exact jacquet_subsingleton_of_isSubquotient (hI K.1)
    ((hU (leviIndex I K.1)).preimage continuous_subtype_val) (hUc K.1) hσ (hE K)

end Subquotient

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

local instance : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hInter : StandardLeviIntersectionStatement.{u})
  (hRoots : HasRelativeRootSystem i)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  (π : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) [Nontrivial π]

local notation "h" =>
  isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν
local notation "hL" => isSemidirectDecomposition_in_levi i ν hInter hG hi hν

include hRoots

/-- A nonzero actual smooth representation has a nonzero standard Jacquet
module containing an actual irreducible cuspidal subquotient. -/
theorem exists_irreducible_cuspidal_jacquet_subquotient :
    ∃ I : Finset (SimpleRoot i ν),
      Nontrivial ((jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π) ∧
      ∃ σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I),
        σ.IsIrreducible ∧
        IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I (hM I) (hL I) σ ∧
        SmoothRep.IsSubquotient σ
          ((jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π) := by
  obtain ⟨I, hI, hcusp⟩ := exists_nontrivial_isLeviCuspidal_jacquet
    i ν hStandard hInter hRoots hG hi hν hU hM π
  let := hI
  obtain ⟨σ, hσ, hσr⟩ := SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial
    ((jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π)
  refine ⟨I, hI, σ, hσ, ?_, hσr⟩
  exact IsLeviCuspidal.of_isSubquotient (fun K =>
    isLimitOfCompactSubgroups_subgroupOf _ _ (hM I)
      (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν hStandard hG hi hν (leviIndex I K))) hcusp hσr

/-- Choose a nonzero standard Jacquet module together with an actual
irreducible cuspidal subquotient, retaining that same standard index. -/
def irreducibleCuspidalJacquetSubquotient :
    Σ I : Finset (SimpleRoot i ν),
      { σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I) //
        Nontrivial ((jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π) ∧
        σ.IsIrreducible ∧
        IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I (hM I) (hL I) σ ∧
        SmoothRep.IsSubquotient σ
          ((jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π) } := by
  let hex := exists_irreducible_cuspidal_jacquet_subquotient
    i ν hStandard hInter hRoots hG hi hν hU hM π
  let I := Classical.choose hex
  have hI := Classical.choose_spec hex
  refine ⟨I, Classical.choose hI.2, hI.1, ?_⟩
  exact Classical.choose_spec hI.2

end RationalPointFamily

end Langlands.Aubert.General

import Langlands.Representation.Aubert.General.CuspidalQuotientEmbedding

/-! # Cuspidal embeddings inside an actual standard rational-point Levi -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k]

local instance leviCuspidalInductionPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hStandard : StandardCocharacterStatement.{u})
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))

include hStandard hG hi hν in
/-- The actual standard radical restricted to a closed Levi is unimodular. -/
theorem isUnimodularModulus_standardUnipotent_in_levi
    (K : Finset (SimpleRoot i ν)) (I : Finset K) :
    letI := (hM K).locallyCompactSpace
    IsUnimodularModulus ((unipotent i ν (leviIndex K I)).subgroupOf (levi i ν K))
      ((hU (leviIndex K I)).preimage continuous_subtype_val) := by
  let := (hM K).locallyCompactSpace
  exact isUnimodularModulus_of_isLimitOfCompactSubgroups _ _
    (isLimitOfCompactSubgroups_subgroupOf _ _ (hM K)
      (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν hStandard hG hi hν (leviIndex K I)))

include hStandard in
/-- Every irreducible smooth representation of a standard Levi embeds into
normalized induction inside that Levi from irreducible cuspidal data on a
smaller actual standard Levi. Compactness of the literal inside-Levi
parabolic quotients is the only extra input to this supporting theorem. -/
theorem exists_cuspidal_embedding_in_levi
    (K : Finset (SimpleRoot i ν))
    (hCompact : ∀ I : Finset K, CompactSpace
      (Induction.LeftQuotient ((parabolic i ν (leviIndex K I)).subgroupOf (levi i ν K))))
    (τ : SmoothRep.{0, u, max u v} ℂ (levi i ν K)) (hτ : τ.IsIrreducible) :
    ∃ (I : Finset K) (σ : SmoothRep.{0, u, max u v} ℂ (levi i ν (leviIndex K I))),
      σ.IsIrreducible ∧
      IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU
        (leviIndex K I) (hM (leviIndex K I))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν (leviIndex K I)) σ ∧
      SmoothRep.IsSubrepresentation τ
        ((leviNormalizedInductionFunctor (hM K)
          (levi_le_of_subset i ν hInter hG hi hν _ K (leviIndex_subset K I))
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν K I)
          (hU (leviIndex K I))).obj σ) := by
  classical
  let := (hM K).locallyCompactSpace
  obtain ⟨I, hI, hcusp⟩ := exists_nonzero_cuspidal_leviJacquet
    i ν hInter hG hi hν hStandard hU hM K τ hτ
  let h := isSemidirectDecomposition_in_levi i ν hInter hG hi hν K I
  let hUK := (hU (leviIndex K I)).preimage
    (continuous_subtype_val : Continuous (fun x : levi i ν K => (x : RationalPoint k G.X)))
  let hAK := levi_le_of_subset i ν hInter hG hi hν _ K (leviIndex_subset K I)
  let e := subgroupOfContinuousEquiv hAK
  have : Nontrivial ((jacquetFunctor h hUK).obj τ) := hI
  let := hCompact I
  obtain ⟨σ, hσ, q, hq, hemb⟩ := CuspidalEmbedding.exists_irreducible_quotient_embedding
    h hUK (isUnimodularModulus_standardUnipotent_in_levi i ν hG hi hν hStandard hU hM K I)
    e τ hτ
  exact ⟨I, σ, hσ, hcusp.of_surjective q hq, hemb⟩

end Langlands.Aubert.General.RationalPointFamily

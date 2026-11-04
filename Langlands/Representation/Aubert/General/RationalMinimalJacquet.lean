import Langlands.Representation.Aubert.General.RationalCuspidalEmbeddingProof
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity

/-! # A nonzero cuspidal Jacquet module from the displayed rational support data -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

local instance instRationalMinimalJacquet1 : TopologicalSpace (RationalPoint k G.X) := pointTopology

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

/-- Every nonzero actual smooth representation has a nonzero standard Jacquet
module that is cuspidal for the proper standard tests inside the same Levi.
The compact-limit input is deduced from the displayed standard-cocharacter data. -/
theorem exists_nontrivial_isLeviCuspidal_jacquet :
    ∃ I : Finset (SimpleRoot i ν),
      Nontrivial ((jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π) ∧
      IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I (hM I) (hL I)
        ((jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π) := by
  classical
  let : Fintype (SimpleRoot i ν) := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  obtain ⟨v₀, hv₀⟩ : ∃ x : π, x ≠ 0 := exists_ne 0
  -- The standard indices with nonzero actual Jacquet module.
  let S : Set (Finset (SimpleRoot i ν)) :=
    {I | Nontrivial ((jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π)}
  have hbot : ∀ x : RationalPoint k G.X, x ∈ unipotent i ν Finset.univ → x = 1 := by
    intro x hx
    rw [unipotent_univ_eq_bot i ν] at hx
    exact Subgroup.mem_bot.mp hx
  have huniv : Finset.univ ∈ S := by
    refine ⟨⟨Jacquet.Localization.mk π.representation (unipotent i ν Finset.univ) 1 v₀,
      0, ?_⟩⟩
    intro hzero
    apply hv₀
    have hmem := (Jacquet.Localization.mk_eq_zero _ _ _ v₀).1 hzero
    have hle : Jacquet.Localization.relations π.representation
        (unipotent i ν Finset.univ) 1 ≤ ⊥ := by
      apply Submodule.span_le.2
      rintro _ ⟨⟨x, b⟩, rfl⟩
      have hx : (x : RationalPoint k G.X) = 1 := hbot x x.2
      simp [hx]
    exact (Submodule.mem_bot ℂ).1 (hle hmem)
  -- A standard index of minimal cardinality with nonzero Jacquet module.
  obtain ⟨I, hI, hImin⟩ :=
    (measure (Finset.card : Finset (SimpleRoot i ν) → ℕ)).wf.has_min S ⟨_, huniv⟩
  have hsmall : ∀ K : Finset I, K ≠ Finset.univ →
      Subsingleton ((jacquetFunctor.{u, max (u + 1) v} (h (leviIndex I K))
        (hU (leviIndex I K))).obj π) := by
    intro K hK
    rw [← not_nontrivial_iff_subsingleton]
    intro hns
    apply hImin (leviIndex I K) hns
    change (leviIndex I K).card < I.card
    rw [card_leviIndex]
    calc K.card < (Finset.univ : Finset I).card :=
          Finset.card_lt_card (Finset.ssubset_univ_iff.2 hK)
      _ = I.card := by rw [Finset.card_univ, Fintype.card_coe]
  let := (hM I).locallyCompactSpace
  -- Cuspidality of the minimal nonzero Jacquet module.
  have hcusp : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I (hM I) (hL I)
      ((jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π) := by
    intro K
    have hsub := leviIndex_subset I K.1
    have hWN : unipotent i ν (leviIndex I K.1) ≤
        Subgroup.normalizer (unipotent i ν I : Set (RationalPoint k G.X)) :=
      (unipotent_le_parabolic_of_subset i ν hInter hG hi hν _ I hsub).trans
        (h I).le_normalizer
    apply CuspidalEmbedding.subsingleton_jacquet_of_forall_mem_relations
    apply CuspidalEmbedding.mem_relations_of_subsingleton (h I) (hU I)
      (unipotent i ν (leviIndex I K.1))
    · intro x hx
      change x ∈ (unipotent i ν (leviIndex I K.1) : Set (RationalPoint k G.X)) at hx
      rw [unipotent_product_of_subset i ν hInter hG hi hν _ I hsub] at hx
      exact Set.mem_mul.mp hx
    · intro w hwV
      apply (Jacquet.inverseHalfCharacter_eq_one _ _).2
      exact CuspidalEmbedding.closedNormalizerCharacter_eq_one_of_compactLimit
        (unipotent i ν I) (unipotent i ν (leviIndex I K.1)) (hU I) hWN
        (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
          i ν hStandard hG hi hν (leviIndex I K.1)) ⟨w, hwV⟩
    · exact hsmall K.1 K.2
  exact ⟨I, hI, hcusp⟩

/-- Choose a standard index together with nonvanishing and cuspidality of its
actual normalized Jacquet module, using only the rational support premises. -/
def nonzeroCuspidalJacquetIndex :
    { I : Finset (SimpleRoot i ν) //
      Nontrivial ((jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π) ∧
      IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I (hM I) (hL I)
        ((jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π) } :=
  Classical.indefiniteDescription _
    (exists_nontrivial_isLeviCuspidal_jacquet i ν hStandard hInter hRoots hG hi hν hU hM π)

end Langlands.Aubert.General.RationalPointFamily

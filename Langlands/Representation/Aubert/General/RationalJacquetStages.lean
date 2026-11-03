import Langlands.Representation.Aubert.General.JacquetStages
import Langlands.Representation.Aubert.General.RationalInductionStagesGeometry

/-! # Actual rational standard Jacquet restriction in stages -/

noncomputable section

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

include hInter hG hi hν

/-- The actual fine radical is the join of the coarse radical and its
intersection with the coarse Levi. -/
theorem unipotent_sup_inter_of_subset
    (I J : Finset (SimpleRoot i ν)) (hIJ : I ⊆ J) :
    unipotent i ν J ⊔ (levi i ν J ⊓ unipotent i ν I) = unipotent i ν I := by
  apply le_antisymm
  · exact sup_le (unipotent_le_of_subset i ν hInter hG hi hν I J hIJ) inf_le_right
  · intro x hx
    change x ∈ (unipotent i ν I : Set (RationalPoint k G.X)) at hx
    rw [unipotent_product_of_subset i ν hInter hG hi hν I J hIJ] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    exact (unipotent i ν J ⊔ (levi i ν J ⊓ unipotent i ν I)).mul_mem
      (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_left hb)

variable (hStandard : StandardCocharacterStatement.{u})

include hStandard in
/-- The fine Levi normalizes the actual second radical in the ambient group. -/
theorem levi_le_normalizer_inter_unipotent
    (J : Finset (SimpleRoot i ν)) (I : Finset J) :
    levi i ν (leviIndex J I) ≤
      Subgroup.normalizer ((levi i ν J ⊓ unipotent i ν (leviIndex J I) :
        Subgroup (RationalPoint k G.X)) : Set (RationalPoint k G.X)) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro m hm w hw
  have hMJ := levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I) hm
  refine ⟨(levi i ν J).mul_mem ((levi i ν J).mul_mem hMJ hw.1)
    ((levi i ν J).inv_mem hMJ), ?_⟩
  exact (Subgroup.le_normalizer_iff.mp
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν (leviIndex J I)).levi_le_normalizer) m hm w hw.2

variable [TopologicalSpace k]

local instance rationalJacquetPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (J : Finset (SimpleRoot i ν)) (I : Finset J)
  (hM : IsClosed (levi i ν J : Set (RationalPoint k G.X)))

/-- The actual inner Haar modulus, pulled back from the literal fine Levi
inside the coarse one. -/
def standardInnerJacquetModulus : levi i ν (leviIndex J I) →* NNRealˣ :=
  letI := hM.locallyCompactSpace
  (HaarModulus.closedRestrictCharacter
    ((unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J))
    ((hU (leviIndex J I)).preimage continuous_subtype_val)
    ((levi i ν (leviIndex J I)).subgroupOf (levi i ν J))
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I).levi_le_normalizer).comp
      (subgroupOfContinuousEquiv
        (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))).symm.toMonoidHom

/-- Actual normalized Jacquet restriction in stages, with the exact positive
Haar-modulus product equality still explicit. -/
def standardJacquetStagesIso
    (hWc : Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)))
    (hδ :
      (HaarModulus.closedRestrictCharacter (unipotent i ν J) (hU J) (levi i ν J)
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν J).levi_le_normalizer).comp
          (Subgroup.inclusion
            (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))) *
        standardInnerJacquetModulus i ν hInter hG hi hν hU J I hM =
      HaarModulus.closedRestrictCharacter (unipotent i ν (leviIndex J I))
        (hU (leviIndex J I)) (levi i ν (leviIndex J I))
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν (leviIndex J I)).levi_le_normalizer) :
    jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν J) (hU J) ⋙
      leviNormalizedJacquetFunctor hM
        (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
        (hU (leviIndex J I)) ≅
    jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν (leviIndex J I)) (hU (leviIndex J I)) := by
  have hjoin := unipotent_sup_inter_of_subset i ν hInter hG hi hν
    (leviIndex J I) J (leviIndex_subset J I)
  have hW : IsClosed
      (((levi i ν J ⊓ unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)) :
        Set (levi i ν J)) := by
    simpa only [Subgroup.inf_subgroupOf_left, Subgroup.coe_subgroupOf, Subgroup.coe_subtype] using
      (hU (leviIndex J I)).preimage (continuous_subtype_val (p := (· ∈ levi i ν J)))
  have hV : IsClosed
      ((unipotent i ν J ⊔ (levi i ν J ⊓ unipotent i ν (leviIndex J I)) :
        Subgroup (RationalPoint k G.X)) : Set (RationalPoint k G.X)) := by
    rw [hjoin]
    exact hU (leviIndex J I)
  have hWc' : Jacquet.Localization.IsLimitOfCompactSubgroups
      ((levi i ν J ⊓ unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)) := by
    simpa only [Subgroup.inf_subgroupOf_left] using hWc
  have hδ' :
      (HaarModulus.closedRestrictCharacter (unipotent i ν J) (hU J) (levi i ν J)
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν J).levi_le_normalizer).comp
          (Subgroup.inclusion
            (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))) *
        innerJacquetModulus (unipotent i ν J) (levi i ν J)
          (levi i ν J ⊓ unipotent i ν (leviIndex J I)) (levi i ν (leviIndex J I))
          inf_le_left
          (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν J).levi_le_normalizer
          (levi_le_normalizer_inter_unipotent i ν hInter hG hi hν hStandard J I)
          hM hW =
      HaarModulus.closedRestrictCharacter
        (unipotent i ν J ⊔ (levi i ν J ⊓ unipotent i ν (leviIndex J I))) hV
        (levi i ν (leviIndex J I))
        (jacquetTowerDatum (unipotent i ν J) (levi i ν J)
          (levi i ν J ⊓ unipotent i ν (leviIndex J I)) (levi i ν (leviIndex J I))
          inf_le_left
          (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν J).levi_le_normalizer
          (levi_le_normalizer_inter_unipotent i ν hInter hG hi hν hStandard J I)
          ).H_le_normalizer_sup := by
    simpa only [innerJacquetModulus, standardInnerJacquetModulus,
      jacquetTowerDatum, Subgroup.inf_subgroupOf_left, hjoin] using hδ
  simpa only [iteratedNormalizedJacquetFunctor, jacquetFunctor,
    leviNormalizedJacquetFunctor, jacquetTowerDatum, Subgroup.inf_subgroupOf_left, hjoin,
    Functor.assoc] using
    (normalizedJacquetStagesIso.{u, max (u + 1) v}
      (unipotent i ν J) (levi i ν J)
      (levi i ν J ⊓ unipotent i ν (leviIndex J I)) (levi i ν (leviIndex J I))
      inf_le_left
      (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν J).levi_le_normalizer
      (levi_le_normalizer_inter_unipotent i ν hInter hG hi hν hStandard J I)
      (hU J) hM hW hV hWc' hδ')

end Langlands.Aubert.General.RationalPointFamily

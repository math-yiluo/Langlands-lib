import Langlands.Representation.CuspidalSupport.BernsteinStandardStages
import Langlands.Representation.Aubert.General.RationalJacquetStages

/-! # Standard Jacquet stages at the Bernstein carrier universes -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinStandardJacquetStagesAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinStandardJacquetStagesTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- Normalized Jacquet restriction in stages at the original saturated
Bernstein carrier universe, including the literal inner-Levi transport. -/
def bernsteinStandardJacquetStagesIso
    (J : Finset (SimpleRoot i ν)) (I : Finset J) :
    jacquetFunctor.{uF, max uF uV} (family.decomposition J) (family.closedUnipotent J) ⋙
      leviNormalizedJacquetFunctor (family.closedLevi J)
        (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
          family.maximalSplitTorus family.genericCocharacter _ J (leviIndex_subset J I))
        (family.leviDecomposition J I) (family.closedUnipotent (leviIndex J I)) ≅
    jacquetFunctor (family.decomposition (leviIndex J I))
      (family.closedUnipotent (leviIndex J I)) := by
  have hWc := isLimitOfCompactSubgroups_subgroupOf _ _ (family.closedLevi J)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter family.connectedReductive family.maximalSplitTorus
      family.genericCocharacter (leviIndex J I))
  have hδ := standardJacquetModulus_stages i ν standardLeviIntersection
    family.connectedReductive family.maximalSplitTorus family.genericCocharacter
    standardCocharacter (continuous_standard_projection i ν standardCocharacter
      family.connectedReductive family.maximalSplitTorus family.genericCocharacter)
    J I family.closedUnipotent (family.closedLevi J)
  have hjoin := unipotent_sup_inter_of_subset i ν standardLeviIntersection family.connectedReductive family.maximalSplitTorus family.genericCocharacter
    (leviIndex J I) J (leviIndex_subset J I)
  have hW : IsClosed
      (((levi i ν J ⊓ unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)) :
        Set (levi i ν J)) := by
    simpa only [Subgroup.inf_subgroupOf_left, Subgroup.coe_subgroupOf, Subgroup.coe_subtype] using
      (family.closedUnipotent (leviIndex J I)).preimage (continuous_subtype_val (p := (· ∈ levi i ν J)))
  have hV : IsClosed
      ((unipotent i ν J ⊔ (levi i ν J ⊓ unipotent i ν (leviIndex J I)) :
        Subgroup (RationalPoint F G.X)) : Set (RationalPoint F G.X)) := by
    rw [hjoin]
    exact family.closedUnipotent (leviIndex J I)
  have hWc' : Jacquet.Localization.IsLimitOfCompactSubgroups
      ((levi i ν J ⊓ unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)) := by
    simpa only [Subgroup.inf_subgroupOf_left] using hWc
  have hδ' :
      (HaarModulus.closedRestrictCharacter (unipotent i ν J) (family.closedUnipotent J) (levi i ν J)
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν standardCocharacter family.connectedReductive family.maximalSplitTorus family.genericCocharacter J).levi_le_normalizer).comp
          (Subgroup.inclusion
            (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive family.maximalSplitTorus family.genericCocharacter _ J (leviIndex_subset J I))) *
        innerJacquetModulus (unipotent i ν J) (levi i ν J)
          (levi i ν J ⊓ unipotent i ν (leviIndex J I)) (levi i ν (leviIndex J I))
          inf_le_left
          (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive family.maximalSplitTorus family.genericCocharacter _ J (leviIndex_subset J I))
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν standardCocharacter family.connectedReductive family.maximalSplitTorus family.genericCocharacter J).levi_le_normalizer
          (levi_le_normalizer_inter_unipotent i ν standardLeviIntersection family.connectedReductive family.maximalSplitTorus family.genericCocharacter standardCocharacter J I)
          (family.closedLevi J) hW =
      HaarModulus.closedRestrictCharacter
        (unipotent i ν J ⊔ (levi i ν J ⊓ unipotent i ν (leviIndex J I))) hV
        (levi i ν (leviIndex J I))
        (jacquetTowerDatum (unipotent i ν J) (levi i ν J)
          (levi i ν J ⊓ unipotent i ν (leviIndex J I)) (levi i ν (leviIndex J I))
          inf_le_left
          (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive family.maximalSplitTorus family.genericCocharacter _ J (leviIndex_subset J I))
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν standardCocharacter family.connectedReductive family.maximalSplitTorus family.genericCocharacter J).levi_le_normalizer
          (levi_le_normalizer_inter_unipotent i ν standardLeviIntersection family.connectedReductive family.maximalSplitTorus family.genericCocharacter standardCocharacter J I)
          ).H_le_normalizer_sup := by
    simpa only [innerJacquetModulus, standardInnerJacquetModulus,
      jacquetTowerDatum, Subgroup.inf_subgroupOf_left, hjoin] using hδ
  simpa only [iteratedNormalizedJacquetFunctor, jacquetFunctor,
    leviNormalizedJacquetFunctor, jacquetTowerDatum, Subgroup.inf_subgroupOf_left, hjoin,
    Functor.assoc] using
    (normalizedJacquetStagesIso.{uF, max uF uV}
      (unipotent i ν J) (levi i ν J)
      (levi i ν J ⊓ unipotent i ν (leviIndex J I)) (levi i ν (leviIndex J I))
      inf_le_left
      (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive family.maximalSplitTorus family.genericCocharacter _ J (leviIndex_subset J I))
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν standardCocharacter family.connectedReductive family.maximalSplitTorus family.genericCocharacter J).levi_le_normalizer
      (levi_le_normalizer_inter_unipotent i ν standardLeviIntersection family.connectedReductive family.maximalSplitTorus family.genericCocharacter standardCocharacter J I)
      (family.closedUnipotent J) (family.closedLevi J) hW hV hWc' hδ')


omit [LocallyOfFiniteType G.X.hom] in
/-- Inner normalized Jacquet restriction preserves actual subquotients,
including its continuous-group-equivalence transport. -/
theorem bernsteinLeviJacquet_isSubquotient
    (J : Finset (SimpleRoot i ν)) (I : Finset J)
    {A B : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J)}
    (hBA : SmoothRep.IsSubquotient B A) :
    SmoothRep.IsSubquotient
      ((leviNormalizedJacquetFunctor (family.closedLevi J)
        (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
          family.maximalSplitTorus family.genericCocharacter _ J (leviIndex_subset J I))
        (family.leviDecomposition J I) (family.closedUnipotent (leviIndex J I))).obj B)
      ((leviNormalizedJacquetFunctor (family.closedLevi J)
        (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
          family.maximalSplitTorus family.genericCocharacter _ J (leviIndex_subset J I))
        (family.leviDecomposition J I) (family.closedUnipotent (leviIndex J I))).obj A) := by
  let := (family.closedLevi J).locallyCompactSpace
  apply ExactSmoothTransport.map_isSubquotient _ _ hBA
  intro A B C f g hf hg hfg
  have h := jacquetFunctor_map_isShortExact (family.leviDecomposition J I)
    ((family.closedUnipotent (leviIndex J I)).preimage continuous_subtype_val)
    (isLimitOfCompactSubgroups_subgroupOf _ _ (family.closedLevi J)
      (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν standardCocharacter family.connectedReductive family.maximalSplitTorus
        family.genericCocharacter (leviIndex J I))) f g ⟨hf, hg, hfg⟩
  exact ⟨h.1, h.2.2, h.2.1⟩

end Langlands.CuspidalSupport

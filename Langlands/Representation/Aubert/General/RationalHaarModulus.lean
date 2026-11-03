import Langlands.Representation.Aubert.General.RationalInductionStagesGeometry
import Langlands.Representation.Aubert.General.SemidirectRestriction
import Langlands.Representation.Aubert.General.RationalJacquetStages
import Langlands.GroupScheme.AffinePointRingPointComparison
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof

/-! # Haar modulus for the actual rational standard family -/

noncomputable section

set_option maxHeartbeats 200000

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- Finite-type affine rational points inherit second countability from the field. -/
theorem pointTopology_secondCountable
    (k : Type u) [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    [SecondCountableTopology k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    SecondCountableTopology (RationalPoint k G.X) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of k k)) :=
    G.affinePointsTopologicalSpace (CommAlgCat.of k k)
  have : SecondCountableTopology (G.affinePoints (CommAlgCat.of k k)) :=
    G.affinePointsSecondCountableTopology (CommAlgCat.of k k)
  let e := (rationalPointHomeomorph k G.X).trans
    (G.affinePointsRingPointHomeomorph (CommAlgCat.of k k)).symm
  exact e.isEmbedding.secondCountableTopology

/-- Connected reductive rational points over a nonarchimedean local field
are second countable for the exact topology of the Aubert target. -/
theorem pointTopology_secondCountable_of_reductive
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    have := hG.isAffineHom
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    SecondCountableTopology (RationalPoint k G.X) := by
  have := hG.isAffineHom
  have := hG.smooth
  have := HarmonicAnalysis.GeneralLocalField.secondCountableTopology k
  exact pointTopology_secondCountable k G

private theorem closedNormalizerCharacter_eq_of_eq
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] {U V : Subgroup H} (hUV : U = V)
    (hU : IsClosed (U : Set H)) (hV : IsClosed (V : Set H))
    (g : H) (hgU : g ∈ Subgroup.normalizer (U : Set H))
    (hgV : g ∈ Subgroup.normalizer (V : Set H)) :
    HaarModulus.closedNormalizerCharacter U hU ⟨g, hgU⟩ =
      HaarModulus.closedNormalizerCharacter V hV ⟨g, hgV⟩ := by
  subst V
  rfl

private theorem closedRestrictCharacter_stages
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    {P M U V L : Subgroup H} (d : IsSemidirectDecomposition P M U)
    (hp : Continuous d.projection) (hVP : V ≤ P) (hUV : U ≤ V) (hLM : L ≤ M)
    (hM : IsClosed (M : Set H)) (hU : IsClosed (U : Set H))
    (hV : IsClosed (V : Set H))
    (hLV : L ≤ Subgroup.normalizer (V : Set H))
    (hLW : L ≤ Subgroup.normalizer ((M ⊓ V : Subgroup H) : Set H))
    (hLVm : L.subgroupOf M ≤ Subgroup.normalizer (V.subgroupOf M : Set M)) :
    (HaarModulus.closedRestrictCharacter U hU M d.levi_le_normalizer).comp
        (Subgroup.inclusion hLM) *
      (letI := hM.locallyCompactSpace
       (HaarModulus.closedRestrictCharacter (V.subgroupOf M)
         (hV.preimage continuous_subtype_val) (L.subgroupOf M) hLVm).comp
           (subgroupOfContinuousEquiv hLM).symm.toMonoidHom) =
    HaarModulus.closedRestrictCharacter V hV L hLV := by
  let W := M ⊓ V
  have hW : IsClosed (W : Set H) := hM.inter hV
  let dV := d.restrict hVP hUV
  have hdV : Continuous dV.projection := d.continuous_restrict_projection hVP hUV hp
  apply MonoidHom.ext
  intro l
  let lM : M := ⟨l, hLM l.property⟩
  have hlM : ((subgroupOfContinuousEquiv hLM).symm l : M) = lM := by
    apply Subtype.ext
    exact subgroupOfContinuousEquiv_symm_apply hLM l
  have hlW : (l : H) ∈ Subgroup.normalizer (W : Set H) := hLW l.property
  have hlU : (l : H) ∈ Subgroup.normalizer (U : Set H) :=
    d.levi_le_normalizer (hLM l.property)
  have hlWm : lM ∈ Subgroup.normalizer (W.subgroupOf M : Set M) := by
    simpa only [hlM, W, Subgroup.inf_subgroupOf_left] using
      hLVm ((subgroupOfContinuousEquiv hLM).symm l).property
  have hinner :
      (letI := hM.locallyCompactSpace
       HaarModulus.closedNormalizerCharacter (V.subgroupOf M)
         (hV.preimage continuous_subtype_val)
         ⟨lM, hLVm ((subgroupOfContinuousEquiv hLM).symm l).property⟩) =
      HaarModulus.closedNormalizerCharacter W hW ⟨l, hlW⟩ := by
    let : LocallyCompactSpace M := hM.locallyCompactSpace
    trans HaarModulus.closedNormalizerCharacter (W.subgroupOf M)
      (hW.preimage continuous_subtype_val) ⟨lM, hlWm⟩
    · exact closedNormalizerCharacter_eq_of_eq
        (Subgroup.inf_subgroupOf_left _ _).symm _ _ lM _ _
    · exact closedNormalizerCharacter_subgroupOf_of_mem M W hM hW inf_le_left lM hlW hlWm
  have hprod := dV.closedNormalizerCharacter_eq_mul hdV hV hW hU
    (l : H) (hLV l.property) hlW hlU
  change HaarModulus.closedNormalizerCharacter U hU ⟨l, hlU⟩ *
      (letI := hM.locallyCompactSpace
       HaarModulus.closedNormalizerCharacter (V.subgroupOf M)
         (hV.preimage continuous_subtype_val)
         ⟨lM, hLVm ((subgroupOfContinuousEquiv hLM).symm l).property⟩) =
    HaarModulus.closedNormalizerCharacter V hV ⟨l, hLV l.property⟩
  rw [hinner]
  exact (hprod.trans (mul_comm _ _)).symm

section Stages

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})

local instance rationalHaarPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hproj : ∀ A : Finset (SimpleRoot i ν), Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A).projection)
  (J : Finset (SimpleRoot i ν)) (I : Finset J)

/-- Multiplication coordinates for the actual nested rational radicals. -/
def standardUnipotentStagesCoordinates :
    ↥(levi i ν J ⊓ unipotent i ν (leviIndex J I)) × unipotent i ν J ≃ₜ
      unipotent i ν (leviIndex J I) := by
  refine IsSemidirectDecomposition.restrictedCoordinates
    (G := RationalPoint k G.X) (P := parabolic i ν J) (M := levi i ν J)
    (U := unipotent i ν J) (Q := unipotent i ν (leviIndex J I))
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν J) ?_ ?_ ?_
  · exact unipotent_le_parabolic_of_subset i ν hInter hG hi hν
      (leviIndex J I) J (leviIndex_subset J I)
  · exact unipotent_le_of_subset i ν hInter hG hi hν
      (leviIndex J I) J (leviIndex_subset J I)
  · exact hproj J

variable
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (hM : IsClosed (levi i ν J : Set (RationalPoint k G.X)))

include hproj

/-- The actual coarse and inner positive Haar characters multiply to the fine one. -/
theorem standardJacquetModulus_stages :
    (HaarModulus.closedRestrictCharacter (unipotent i ν J) (hU J) (levi i ν J)
      (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν J).levi_le_normalizer).comp
        (Subgroup.inclusion
          (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))) *
      standardInnerJacquetModulus i ν hInter hG hi hν hU J I hM =
    HaarModulus.closedRestrictCharacter (unipotent i ν (leviIndex J I))
      (hU (leviIndex J I)) (levi i ν (leviIndex J I))
      (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν (leviIndex J I)).levi_le_normalizer := by
  have : SecondCountableTopology (RationalPoint k G.X) :=
    pointTopology_secondCountable_of_reductive k G hG
  exact closedRestrictCharacter_stages
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν J) (hproj J)
    (unipotent_le_parabolic_of_subset i ν hInter hG hi hν
      (leviIndex J I) J (leviIndex_subset J I))
    (unipotent_le_of_subset i ν hInter hG hi hν
      (leviIndex J I) J (leviIndex_subset J I))
    (levi_le_of_subset i ν hInter hG hi hν
      (leviIndex J I) J (leviIndex_subset J I))
    hM (hU J) (hU (leviIndex J I))
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν (leviIndex J I)).levi_le_normalizer
    (levi_le_normalizer_inter_unipotent i ν hInter hG hi hν hStandard J I)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I).levi_le_normalizer

end Stages

end Langlands.Aubert.General.RationalPointFamily

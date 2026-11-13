import Langlands.BruhatTits.IntegralModels.DepthZeroCompactOpen
import Langlands.AlgebraicGeometry.PointTopology.RationalPointEvaluation
import Langlands.GroupTheory.ProPPreimage
import Langlands.GroupTheory.ProPDiscreteImage

/-! # Discrete parahoric reduction and pro-p inverse images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Cohomology

namespace Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {D : RelativeComponentModelData 𝒪[F] F G} (Q : SpecialFibreQuotientData D)

local instance genericPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance genericPointTopologicalGroup : IsTopologicalGroup (rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G
local instance genericPointTotallyDisconnected : TotallyDisconnectedSpace (rationalPoints G) :=
  rationalPoint_totallyDisconnectedSpace_of_localField F G.X
local instance quotientPointTopology : TopologicalSpace (rationalPoints Q.quotient) := ⊥
local instance quotientPointDiscrete : DiscreteTopology (rationalPoints Q.quotient) :=
  discreteTopology_bot _

/-- Actual parahoric reduction is continuous into the discrete quotient
point group because its kernel contains an open congruence subgroup. -/
theorem localField_continuous_parahoricReduction : Continuous Q.parahoricReduction := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one, nhds_discrete (rationalPoints Q.quotient),
    Filter.tendsto_pure]
  exact (Q.isOpen_ker_parahoricReduction
    (isOpen_congruenceSubgroup_of_congruenceBasis
      LocalFieldIntegralModel.congruenceNeighborhoodBasis_proof D)).mem_nhds
    Q.parahoricReduction.map_one

/-- The actual reduction on the neutral integral-point image, bundled as
a continuous homomorphism to the discrete quotient point group. -/
def localFieldReductionContinuousHom :
    D.neutral.integralPoints →ₜ* rationalPoints Q.quotient where
  toMonoidHom := Q.parahoricReduction
  continuous_toFun := Q.localField_continuous_parahoricReduction

@[simp]
theorem localFieldReductionContinuousHom_toMonoidHom :
    Q.localFieldReductionContinuousHom.toMonoidHom = Q.parahoricReduction := rfl

/-- Lift a quotient-point subgroup to an open subgroup of the original
generic rational points through the actual parahoric reduction. -/
def localFieldReductionPreimage (P : Subgroup (rationalPoints Q.quotient)) :
    OpenSubgroup (rationalPoints G) where
  toSubgroup := (P.comap Q.parahoricReduction).map D.neutral.integralPoints.subtype
  isOpen' := by
    change IsOpen (Subtype.val '' (P.comap Q.parahoricReduction :
      Set D.neutral.integralPoints))
    exact D.neutral.isOpen_integralPoints_localField.isOpenMap_subtype_val _
      (discretePreimageOpenSubgroup Q.parahoricReduction
        Q.localField_continuous_parahoricReduction P).isOpen

@[simp]
theorem localFieldReductionPreimage_toSubgroup
    (P : Subgroup (rationalPoints Q.quotient)) :
    (Q.localFieldReductionPreimage P).toSubgroup =
      (P.comap Q.parahoricReduction).map D.neutral.integralPoints.subtype := rfl

/-- The lifted subgroup remains inside the actual neutral integral-point image. -/
theorem localFieldReductionPreimage_le_integralPoints
    (P : Subgroup (rationalPoints Q.quotient)) :
    (Q.localFieldReductionPreimage P).toSubgroup ≤ D.neutral.integralPoints :=
  ((P.comap Q.parahoricReduction).map_le_range _).trans_eq
    D.neutral.integralPoints.range_subtype

/-- Viewing the ambient lift inside the neutral integral-point image recovers
the original inverse image. -/
theorem localFieldReductionPreimage_subgroupOf
    (P : Subgroup (rationalPoints Q.quotient)) :
    (Q.localFieldReductionPreimage P).toSubgroup.subgroupOf D.neutral.integralPoints =
      P.comap Q.parahoricReduction :=
  Subgroup.comap_map_eq_self_of_injective D.neutral.integralPoints.subtype_injective _

omit [LocallyOfFiniteType G.X.hom] in
/-- The pro-p property of the actual radical preimage gives the pro-p property
of the actual parahoric reduction kernel, preserving the induced topology. -/
theorem localField_isProP_ker_parahoricReduction {p : ℕ}
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
      Q.projection) (hpos : IsProPSubgroup p Q.positivePoints) :
    IsProPSubgroup p Q.parahoricReduction.ker := by
  rw [Q.ker_parahoricReduction hQ]
  exact hpos.subgroupOf Q.positivePoints_le_integralPoints

/-- A p-subgroup of the quotient lifts to an open pro-p subgroup of the
generic point group if the radical preimage is pro-p. -/
theorem localField_isProP_reductionPreimage {p : ℕ}
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
      Q.projection) (hpos : IsProPSubgroup p Q.positivePoints)
    (P : Subgroup (rationalPoints Q.quotient)) (hP : IsPGroup p P) :
    IsProPSubgroup p (Q.localFieldReductionPreimage P).toSubgroup := by
  let : CompactSpace D.neutral.integralPoints :=
    isCompact_iff_compactSpace.mp D.neutral.isCompact_integralPoints_localField
  have hp := (Q.localField_isProP_ker_parahoricReduction hQ hpos).isOpen_and_comap_of_isPGroup
    Q.localField_continuous_parahoricReduction P hP
  apply IsProPSubgroup.of_subgroupOf
    (K := D.neutral.integralPoints)
    (hHK := Q.localFieldReductionPreimage_le_integralPoints P)
  rw [Q.localFieldReductionPreimage_subgroupOf]
  exact hp.2

/-- A pro-p subgroup contained in the neutral integral points has p-group
image under actual parahoric reduction. -/
theorem localField_isPGroup_reductionImage {p : ℕ}
    {H : Subgroup (rationalPoints G)} (hH : IsProPSubgroup p H)
    (hHI : H ≤ D.neutral.integralPoints) :
    IsPGroup p ((H.subgroupOf D.neutral.integralPoints).map Q.parahoricReduction) :=
  (hH.subgroupOf hHI).isPGroup_map Q.parahoricReduction
    Q.localField_continuous_parahoricReduction

end Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData

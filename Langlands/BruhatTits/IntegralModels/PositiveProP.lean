import Langlands.BruhatTits.IntegralModels.PositiveProPStatement
import Langlands.BruhatTits.IntegralModels.DepthZeroReduction
import Langlands.GroupScheme.IntegralModel.CongruenceProP
import Langlands.GroupScheme.Rational.UnipotentPointsPGroup
import Langlands.GroupTheory.ProPPreimage

/-! # Full special-fibre reduction and pro-p radical preimages -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Cohomology

namespace Langlands.BruhatTits.IntegralModels

section Local

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}

namespace RelativeComponentModelData

/-- Actual reduction from the neutral integral-point image to the full special
fibre, before passage to a reductive quotient. -/
def neutralSpecialReduction (D : RelativeComponentModelData R K G) :
    D.neutral.integralPoints →* rationalPoints D.neutral.specialFibre :=
  D.neutral.reduction.comp D.neutralSectionsEquiv.symm.toMonoidHom

@[simp]
theorem neutralSpecialReduction_neutralSectionsEquiv
    (D : RelativeComponentModelData R K G) (x : D.neutral.integralSections) :
    D.neutralSpecialReduction (D.neutralSectionsEquiv x) = D.neutral.reduction x := by
  simp [neutralSpecialReduction]

/-- The full reduction kernel is exactly the congruence subgroup, viewed in
the neutral integral-point image. -/
theorem ker_neutralSpecialReduction (D : RelativeComponentModelData R K G) :
    D.neutralSpecialReduction.ker =
      D.neutral.congruenceSubgroup.subgroupOf D.neutral.integralPoints := by
  ext g
  obtain ⟨x, rfl⟩ := D.neutralSectionsEquiv.surjective g
  rw [MonoidHom.mem_ker, neutralSpecialReduction_neutralSectionsEquiv,
    Subgroup.mem_subgroupOf, neutralSectionsEquiv_apply, IntegralModel.congruenceSubgroup,
    Subgroup.mem_map_iff_mem D.neutral.integralPointMap_injective]
  rfl

end RelativeComponentModelData

namespace SpecialFibreQuotientData

variable {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)

/-- The actual positive subgroup is the inverse image of the radical points
under full special-fibre reduction, with the neutral ambient group explicit. -/
theorem comap_radicalPoints_neutralSpecialReduction :
    Q.radicalPoints.comap D.neutralSpecialReduction =
      Q.positivePoints.subgroupOf D.neutral.integralPoints := by
  ext g
  obtain ⟨x, rfl⟩ := D.neutralSectionsEquiv.surjective g
  rw [Subgroup.mem_comap,
    RelativeComponentModelData.neutralSpecialReduction_neutralSectionsEquiv,
    Subgroup.mem_subgroupOf, RelativeComponentModelData.neutralSectionsEquiv_apply,
    positivePoints, Subgroup.mem_map_iff_mem D.neutral.integralPointMap_injective]
  rfl

end SpecialFibreQuotientData

end Local

section LocalField

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {D : RelativeComponentModelData 𝒪[F] F G}

local instance positiveProPPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance positiveProPPointTotallyDisconnected :
    TotallyDisconnectedSpace (rationalPoints G) :=
  rationalPoint_totallyDisconnectedSpace_of_localField F G.X

local instance positiveProPSpecialFibreAffine :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap ↥𝒪[F]))
  infer_instance

namespace RelativeComponentModelData

omit [LocallyOfFiniteType G.X.hom] in
/-- The full reduction kernel is pro-p in its induced integral-point topology. -/
theorem localField_isProP_ker_neutralSpecialReduction
    (D : RelativeComponentModelData 𝒪[F] F G) :
    IsProPSubgroup (ringChar 𝓀[F]) D.neutralSpecialReduction.ker := by
  rw [D.ker_neutralSpecialReduction]
  exact D.neutral.localField_isProP_congruenceSubgroup.subgroupOf
    D.neutral.congruenceSubgroup_le_integralPoints

end RelativeComponentModelData

namespace SpecialFibreQuotientData

variable (Q : SpecialFibreQuotientData D)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The actual residue-field image of the supplied unipotent radical is
a p-group for the actual residue characteristic. -/
theorem localField_isPGroup_radicalPoints
    (hrad : IsUnipotentRadical Q.radicalInclusion) :
    IsPGroup (ringChar 𝓀[F]) Q.radicalPoints := by
  let : Smooth Q.radical.X.hom := hrad.smooth
  let : IsAffineHom Q.radical.X.hom :=
    HomogeneousQuotient.affine_subgroup_of_closed _ _ Q.radicalInclusion
      hrad.isClosedSubgroup
  let : Fact (ringChar 𝓀[F]).Prime := ⟨CharP.prime_ringChar 𝓀[F]⟩
  exact isPGroup_range_testPoints_of_isUnipotent (ringChar 𝓀[F])
    hrad.isUnipotent Q.radicalInclusion (Over.mk (𝟙 _))

/-- The actual radical preimage is pro-p in the original rational-point
topology. Only the radical property of the supplied special-fibre data is needed. -/
theorem localField_isProP_positivePoints
    (hrad : IsUnipotentRadical Q.radicalInclusion) :
    IsProPSubgroup (ringChar 𝓀[F]) Q.positivePoints := by
  let e := Subgroup.subgroupOfContinuousMulEquivOfLe Q.positivePoints_le_integralPoints
  let : CompactSpace Q.positivePoints :=
    isCompact_iff_compactSpace.mp Q.localField_isCompact_positivePoints
  let : CompactSpace (Q.positivePoints.subgroupOf D.neutral.integralPoints) :=
    e.symm.toHomeomorph.compactSpace
  have hc : CompactSpace (Q.radicalPoints.comap D.neutralSpecialReduction) := by
    rw [Q.comap_radicalPoints_neutralSpecialReduction]
    infer_instance
  let := hc
  have h := D.localField_isProP_ker_neutralSpecialReduction.comap_of_isPGroup
    Q.radicalPoints (Q.localField_isPGroup_radicalPoints hrad)
  rw [Q.comap_radicalPoints_neutralSpecialReduction] at h
  exact h.of_subgroupOf Q.positivePoints_le_integralPoints

end SpecialFibreQuotientData

end LocalField

/-- The published local-field positive pro-p statement at arbitrary universe. -/
theorem localFieldPositiveProP : LocalFieldPositiveProPStatement.{u} := by
  intro F _ _ _ _ G _ _ D Q hQ
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact Q.localField_isProP_positivePoints hQ.1

end Langlands.BruhatTits.IntegralModels

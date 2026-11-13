import Langlands.BruhatTits.IntegralModels.DepthZeroInduction
import Langlands.GroupScheme.IntegralModel.CongruenceNeighborhoodBasisProof
import Langlands.GroupScheme.IntegralModel.LocalCompactPoints
import Langlands.GroupScheme.IntegralModel.LocalIntegralSeparation

/-! # Compact open depth-zero subgroups of supplied KP models

Over the valuation ring of a nonarchimedean local field `F`, with `G(F)` carrying its
canonical topology, the radical preimage `G(F)^{0+}` is a compact open subgroup of `G(F)`.
Compactness and openness of the integral points `G^0(𝒪)` are the published
`IntegralModel.isCompact_integralPoints_localField` and
`IntegralModel.isOpen_integralPoints_localField`, reused here.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

namespace SpecialFibreQuotientData

variable [IsLocalRing R] {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)

/-- The level-one congruence subgroup of the neutral model lies in the radical
preimage `G(K)^{0+}`: a section reducing to the identity reduces into the radical. -/
theorem congruenceSubgroup_le_positivePoints :
    D.neutral.congruenceSubgroup ≤ Q.positivePoints := by
  intro g hg
  obtain ⟨x, hx, hxg⟩ := (IntegralModel.mem_congruenceSubgroup _ _).mp hg
  refine (Q.mem_positivePoints g).mpr ⟨x, ?_, hxg⟩
  rw [hx]
  exact one_mem _

/-- Under the fppf-quotient hypothesis, `G(K)^{0+} ∩ G^0(R)` is normal in `G^0(R)`, being
the kernel of the depth-zero reduction. -/
theorem positivePoints_subgroupOf_normal
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
      Q.projection) :
    (Q.positivePoints.subgroupOf D.neutral.integralPoints).Normal := by
  rw [← Q.ker_parahoricReduction hQ]
  infer_instance

end SpecialFibreQuotientData

section LocalField

open Langlands.AlgebraicGeometry.PointTopology
open scoped ValuativeRel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left]

namespace RelativeComponentModelData

/-- `G^0(𝒪)` as an open subgroup of `G(F)` with its canonical topology. -/
def localFieldIntegralOpenSubgroup (D : RelativeComponentModelData 𝒪[F] F G) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    OpenSubgroup (rationalPoints G) :=
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  ⟨D.neutral.integralPoints, D.neutral.isOpen_integralPoints_localField⟩

end RelativeComponentModelData

namespace SpecialFibreQuotientData

variable [LocallyOfFiniteType G.X.hom]
  {D : RelativeComponentModelData 𝒪[F] F G} (Q : SpecialFibreQuotientData D)

/-- The radical preimage `G(F)^{0+}` is open in `G(F)`. -/
theorem localField_isOpen_positivePoints :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsOpen (Q.positivePoints : Set (rationalPoints G)) :=
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  Subgroup.isOpen_mono Q.congruenceSubgroup_le_positivePoints
    (isOpen_congruenceSubgroup_of_congruenceBasis
      LocalFieldIntegralModel.congruenceNeighborhoodBasis_proof D)

/-- The radical preimage `G(F)^{0+}` as an open subgroup of `G(F)`. -/
def localFieldPositiveOpenSubgroup :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    OpenSubgroup (rationalPoints G) :=
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  ⟨Q.positivePoints, Q.localField_isOpen_positivePoints⟩

/-- The radical preimage `G(F)^{0+}` is compact in `G(F)`: it is an open, hence
closed, subgroup contained in the compact group `G^0(𝒪)`. -/
theorem localField_isCompact_positivePoints :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsCompact (Q.positivePoints : Set (rationalPoints G)) :=
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  D.neutral.isCompact_integralPoints_localField.of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ Q.localField_isOpen_positivePoints)
    Q.positivePoints_le_integralPoints

end SpecialFibreQuotientData

end LocalField

end Langlands.BruhatTits.IntegralModels

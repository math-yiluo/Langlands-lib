import Langlands.BruhatTits.Unipotent.CompactOpenContainmentProof
import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceProof
import Langlands.GroupScheme.Rational.UnipotentCompactProPRange

/-! # Compact subgroups of actual dynamic unipotent point groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Cohomology

namespace Langlands.BruhatTits.DynamicUnipotentContainment

variable {F : Type u} [Field F] [TopologicalSpace F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local instance dynamicCompactAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance dynamicCompactPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance dynamicCompactUnipotentAffine : IsAffine (Dynamic.Affine.unipotentScheme χ).X.left := by
  let : IsClosedImmersion (Dynamic.Affine.unipotentHom χ).hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_unipotentHom χ
  exact isAffine_of_isAffineHom (Dynamic.Affine.unipotentHom χ).hom.hom.left
local instance dynamicCompactUnipotentPointTopology :
    TopologicalSpace (rationalPoints (Dynamic.Affine.unipotentScheme χ)) :=
  rationalPointTopology F (Dynamic.Affine.unipotentScheme χ).X

/-- The chosen closed representative has exactly the original dynamic subgroup
with its inherited rational-point topology. -/
def unipotentPointsHomeomorph :
    rationalPoints (Dynamic.Affine.unipotentScheme χ) ≃ₜ* unipotentPoints χ :=
  rationalPointSubgroupHomeomorph F (Dynamic.unipotent χ) (Dynamic.Affine.unipotentHom χ)
    (Dynamic.Affine.isRepresentedBy_unipotentHom χ)
    (Dynamic.Affine.isClosedSubgroup_unipotentHom χ)

omit [TopologicalSpace F] in
/-- Evaluation of actual dynamic representability at the identity test gives
the literal rational-point image, without a rational lifting premise. -/
theorem unipotentPoints_eq_range :
    unipotentPoints χ = (rationalPoints.map (Dynamic.Affine.unipotentHom χ)).range := by
  exact congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _)))
    (Dynamic.Affine.isRepresentedBy_unipotentHom χ).2.symm

/-- Every compact ambient subgroup contained in the actual dynamic unipotent
points is pro-p for the residue characteristic, with the original topology. -/
theorem isProPSubgroup_of_isCompact_le_unipotentPoints
    [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
    (K : Subgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hKU : K ≤ unipotentPoints χ) : IsProPSubgroup (ringChar 𝓀[F]) K := by
  let j := Dynamic.Affine.unipotentHom χ
  let : IsClosedImmersion j.hom.hom.left := Dynamic.Affine.isClosedSubgroup_unipotentHom χ
  let : LocallyOfFiniteType (Dynamic.Affine.unipotentScheme χ).X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have hU : IsUnipotent (Dynamic.Affine.unipotentScheme χ) :=
    dynamicUnipotentUnipotence F G χ _ j (Dynamic.Affine.isRepresentedBy_unipotentHom χ)
  apply isProPSubgroup_of_isCompact_le_range_of_isUnipotent j
    (Dynamic.Affine.isClosedSubgroup_unipotentHom χ) hU K hK
  rwa [← unipotentPoints_eq_range χ]

end Langlands.BruhatTits.DynamicUnipotentContainment

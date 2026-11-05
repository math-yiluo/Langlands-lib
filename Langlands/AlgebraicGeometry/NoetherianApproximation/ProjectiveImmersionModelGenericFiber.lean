import Langlands.AlgebraicGeometry.NoetherianApproximation.ProjectiveImmersionCoefficientBaseChange
import Langlands.AlgebraicGeometry.PointTopology.RingPointBaseChange
import Langlands.AlgebraicGeometry.PointTopology.QuasiProjectiveWeilRestriction

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

open PointTopology

set_option backward.isDefEq.respectTransparency false

namespace ProjectiveImmersionRingModelData

variable {R F : Type u} [CommRing R] [Field F] [Algebra R F]
  {X : Scheme.{u}} {n : ℕ} {j : X ⟶ ProjectiveSpace F n}
  (D : ProjectiveImmersionRingModelData R F X n j)

/-- Regard the constructed actual model over its original coefficient spectrum. -/
def asOver : Over (Spec (CommRingCat.of R)) :=
  Over.mk (D.immersion ≫ projectiveSpaceToSpec R n)

scoped instance locallyOfFiniteType : LocallyOfFiniteType D.asOver.hom := by
  let : LocallyOfFinitePresentation (D.immersion ≫ projectiveSpaceToSpec R n) :=
    D.locallyOfFinitePresentation
  change LocallyOfFiniteType (D.immersion ≫ projectiveSpaceToSpec R n)
  infer_instance

scoped instance asOverQuasiCompact : QuasiCompact D.asOver.hom := D.quasiCompact

scoped instance separated : IsSeparated D.asOver.hom := by
  let : IsImmersion D.immersion := D.isImmersion
  exact isSeparated_of_projectiveImmersion R D.asOver n D.immersion rfl

/-- The actual constructed model has affine neighborhoods for every finite subset. -/
theorem hasFiniteAffineNeighborhoods : HasFiniteAffineNeighborhoods D.asOver.left := by
  let : IsImmersion D.immersion := D.isImmersion
  exact hasFiniteAffineNeighborhoods_of_projectiveImmersion R n D.immersion

/-- Its original-field pullback is canonically the originally specified projective scheme. -/
def genericFiberIso : ringBaseChange R F D.asOver ≅
    Over.mk (j ≫ projectiveSpaceToSpec F n) :=
  (Over.isoMk D.cartesian.isoPullback D.cartesian.isoPullback_hom_snd).symm

/-- The inverse generic-fiber isomorphism projects to the originally specified model comparison. -/
@[simp]
theorem genericFiberIso_inv_left_fst :
    D.genericFiberIso.inv.left ≫
      pullback.fst (D.immersion ≫ projectiveSpaceToSpec R n) (Spec.algebraMap R F) =
        D.comparison :=
  D.cartesian.isoPullback_hom_fst

/-- The forward generic-fiber isomorphism recovers the first projection under original comparison. -/
@[simp]
theorem genericFiberIso_hom_left_comparison :
    D.genericFiberIso.hom.left ≫ D.comparison =
      pullback.fst (D.immersion ≫ projectiveSpaceToSpec R n) (Spec.algebraMap R F) :=
  D.cartesian.isoPullback_inv_fst

/-- The constructed generic-fiber isomorphism also retains the specified original projective map. -/
theorem genericFiberIso_originalImmersion :
    D.genericFiberIso.inv.left ≫
      pullback.fst (D.immersion ≫ projectiveSpaceToSpec R n) (Spec.algebraMap R F) ≫
        D.immersion = j ≫ ProjSpace.map R F n := by
  rw [← Category.assoc, D.genericFiberIso_inv_left_fst]
  exact D.originalImmersion

end ProjectiveImmersionRingModelData

end Langlands.AlgebraicGeometry.NoetherianApproximation

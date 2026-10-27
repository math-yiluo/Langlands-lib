import Langlands.AlgebraicGeometry.Picard.RelativePicardZero
import Langlands.AlgebraicGeometry.Picard.UniversalFamilyTriviality

/-! # The identity-component open of an actual universal Picard family over a field -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable (k : Type u) [Field k]
  (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
  {P : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
  (L : RigidifiedFamily A P)
  (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L)

/-- The point of the full parameter scheme at which the published section classifying the
trivial rigidified family takes the unique point of the base. -/
def fullPicardOriginPoint : P.left :=
  (RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A) (unitSection_comp A) L hL).left
    (IsLocalRing.closedPoint k)

/-- A specified open subset of the full parameter scheme is exactly the topological connected
component of the origin point. This predicate makes no existence or openness assertion. -/
def IsFullPicardIdentityComponentOpen (U : P.left.Opens) : Prop :=
  (U : Set P.left) = connectedComponent (fullPicardOriginPoint k A L hL)

/-- The origin point lies in any specified identity-component open. -/
lemma fullPicardOriginPoint_mem {U : P.left.Opens}
    (hU : IsFullPicardIdentityComponentOpen k A L hL U) :
    fullPicardOriginPoint k A L hL ∈ U := by
  change fullPicardOriginPoint k A L hL ∈ (U : Set P.left)
  rw [hU]
  exact mem_connectedComponent

end Langlands.AbelianScheme

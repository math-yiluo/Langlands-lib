import Langlands.GroupScheme.HomogeneousQuotientBaseChange
import Langlands.GroupScheme.HomogeneousQuotientComparison
import Langlands.AlgebraicGeometry.FieldExtensionAffineDescentProof

/-! # Affineness of actual homogeneous quotients by field descent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousQuotientFromEmbedding.HomogeneousQuotient

section Comparison

variable {S : Scheme.{u}} {G H : GroupScheme S} {i : H ⟶ G}
    (D E : HomogeneousQuotient i)

local instance instHomogeneousQuotientAffineDescent1 : Smooth D.projection.left := D.smooth_projection
local instance instHomogeneousQuotientAffineDescent2 : Surjective D.projection.left := D.surjective_projection
local instance instHomogeneousQuotientAffineDescent3 : QuasiCompact D.projection.left := D.quasiCompact_projection
local instance instHomogeneousQuotientAffineDescent4 : Smooth E.projection.left := E.smooth_projection
local instance instHomogeneousQuotientAffineDescent5 : Surjective E.projection.left := E.surjective_projection
local instance instHomogeneousQuotientAffineDescent6 : QuasiCompact E.projection.left := E.quasiCompact_projection

/-- The compatible comparison isomorphism between two actual homogeneous quotients
by the same subgroup. -/
def comparisonIso : D.scheme ≅ E.scheme :=
  HomogeneousQuotientComparison.iso D.projection E.projection
    (fun T g h => (D.fibers T g h).trans (E.fibers T g h).symm)

/-- Comparison retains the actual quotient projection. -/
@[reassoc]
theorem projection_comparisonIso_hom :
    D.projection ≫ (D.comparisonIso E).hom = E.projection :=
  HomogeneousQuotientComparison.comp_iso_hom D.projection E.projection _

/-- Affineness transfers between actual quotient models for the same subgroup. -/
theorem isAffine_of_comparison (hE : IsAffine E.scheme.left) :
    IsAffine D.scheme.left := by
  let : IsAffine E.scheme.left := hE
  let e := D.comparisonIso E
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  exact IsAffine.of_isIso e.hom.left

end Comparison

/-- If a quotient after a field extension has an affine model, the original
actual homogeneous quotient is affine. -/
theorem isAffine_of_fieldExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G H : GroupScheme (Spec (CommRingCat.of k))} {i : H ⟶ G}
    (D : HomogeneousQuotient i)
    (E : HomogeneousQuotient ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i))
    (hE : IsAffine E.scheme.left) : IsAffine D.scheme.left := by
  have hbase : IsAffine (D.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).scheme.left :=
    isAffine_of_comparison _ E hE
  exact Langlands.AlgebraicGeometry.fieldExtensionAffineDescent k K
    D.scheme.left D.scheme.hom hbase

end Langlands.GroupScheme.HomogeneousQuotientFromEmbedding.HomogeneousQuotient

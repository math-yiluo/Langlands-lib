import Langlands.GroupScheme.Rational.StandardLeviLieWeights
import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.GroupScheme.Rational.LeviSplitComponentFactorization

/-! # The central split-torus image annihilates the selected roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G L : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (hDynamic : DynamicLieStatement.{u})
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (J : Set (characterLattice T))
  (hJ : J ⊆ simpleRelativeRoots i ν)
  {j : L ⟶ G} (hjc : IsClosedSubgroup j)
  (hj : (standardLevi i ν J).IsRepresentedBy j)
  (a : A.toGrp ⟶ L) (ha : IsCentralSplitTorus a)
  (f : A ⟶ T) (hf : CommGroupScheme.groupHom f ≫ i = a ≫ j)

include hDynamic hJ hjc hj ha hf

/-- Every selected root restricts to zero along the actual torus map of a
central split torus in the standard Levi. -/
theorem selectedRoot_restrict_eq_zero_standardLevi
    {α : characterLattice T} (hα : α ∈ J) : f ≫ α = 0 := by
  have : IsAffineHom L.X.hom := hjc.isAffineHom_source
  have : IsClosedImmersion j.hom.hom.left := hjc
  have : LocallyOfFiniteType L.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have hfL : CommGroupScheme.groupHom f ≫ standardLeviTorusFactor i ν J hj = a :=
    hj.hom_ext (by rw [Category.assoc, standardLeviTorusFactor_comp]; exact hf)
  apply root_restrict_eq_zero_of_isCentral
    (standardLeviTorusFactor i ν J hj) f ha.1.1
    (by rw [hfL]; exact ha.2)
  exact selectedRoots_subset_relativeRoots_standardLeviTorusFactor
    hDynamic i ν J hj hJ hα

/-- The integral cocharacter image of a central split torus annihilates the
selected roots under the actual integer pairing. -/
theorem latticePairing_cocharacterMapInt_standardLevi_eq_zero
    (zeta : cocharacterLattice A) {α : characterLattice T} (hα : α ∈ J) :
    latticePairing T α (cocharacterMapInt f zeta) = 0 := by
  change gmEndEquiv k ((zeta ≫ f) ≫ α) = 0
  rw [Category.assoc,
    selectedRoot_restrict_eq_zero_standardLevi hDynamic i ν J hJ hjc hj a ha f hf hα,
    Limits.comp_zero, map_zero]

/-- The whole real cocharacter image of an actual central split torus in the
standard Levi lies in the selected-root annihilator. -/
theorem range_cocharacterMapReal_le_rootAnnihilator_standardLevi :
    (cocharacterMapReal f).range ≤ rootAnnihilator T J := by
  rintro _ ⟨x, rfl⟩
  rw [mem_rootAnnihilator]
  intro α hα
  induction x using TensorProduct.inductionOn with
  | tmul r zeta =>
    rw [cocharacterMapReal_tmul, eval_tmul]
    change r * (latticePairing T α (cocharacterMapInt f zeta) : ℝ) = 0
    rw [latticePairing_cocharacterMapInt_standardLevi_eq_zero
        hDynamic i ν J hJ hjc hj a ha f hf zeta hα,
      Int.cast_zero, mul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

/-- The real cocharacter map of an actual central split torus in a standard
Levi, with codomain restricted to the selected-root annihilator. -/
def standardLeviCentralDirectionsMap : V A →ₗ[ℝ] rootAnnihilator T J :=
  (cocharacterMapReal f).codRestrict (rootAnnihilator T J) fun x =>
    range_cocharacterMapReal_le_rootAnnihilator_standardLevi
      hDynamic i ν J hJ hjc hj a ha f hf (LinearMap.mem_range_self _ x)

@[simp] theorem standardLeviCentralDirectionsMap_coe (x : V A) :
    (standardLeviCentralDirectionsMap hDynamic i ν J hJ hjc hj a ha f hf x :
      V T) = cocharacterMapReal f x := rfl

end Langlands.GroupScheme

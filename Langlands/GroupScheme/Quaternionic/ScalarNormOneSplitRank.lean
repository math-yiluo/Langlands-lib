import Langlands.GroupScheme.Quaternionic.ScalarHyperbolicNorm
import Langlands.GroupScheme.Quaternionic.NormOneIsometry
import Langlands.GroupScheme.Quaternionic.RadicalFreeHyperbolicFamily
import Langlands.GroupScheme.Quaternionic.QuadraticTorusWittBound

/-! # Split rank of the actual norm-one group of a scalar quadratic form -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K : Type u} [Field K] {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
  {q : (scalar K).QuadraticForms n} {I : Type u} [Fintype I] [DecidableEq I]
  {x y : I → n → K}

instance isAffineHom_scalar_normOneIsometryGroup (q : (scalar K).QuadraticForms n) :
    IsAffineHom ((scalar K).normOneIsometryGroup q).X.hom := by
  have : IsClosedImmersion ((scalar K).normOneIsometryAmbientι q).hom.hom.left :=
    (scalar K).isClosedSubgroup_normOneIsometryAmbientι q
  rw [← ((scalar K).normOneIsometryAmbientι q).hom.hom.w]
  infer_instance

instance locallyOfFiniteType_scalar_normOneIsometryGroup (q : (scalar K).QuadraticForms n) :
    LocallyOfFiniteType ((scalar K).normOneIsometryGroup q).X.hom := by
  have : IsClosedImmersion ((scalar K).normOneIsometryAmbientι q).hom.hom.left :=
    (scalar K).isClosedSubgroup_normOneIsometryAmbientι q
  rw [← ((scalar K).normOneIsometryAmbientι q).hom.hom.w]
  infer_instance

namespace IsHyperbolicFamily

variable (h : (scalar K).IsHyperbolicFamily q x y)
include h

local notation "𝕊" => splitTorus (Spec (CommRingCat.of K)) I

/-- The actual scaling torus of a scalar hyperbolic family lands in the actual
reduced-norm-one isometry subgroup, on all test schemes. -/
theorem exists_normOneTorus :
    ∃ f : 𝕊 ⟶ (scalar K).normOneIsometryGroup q,
      f ≫ (scalar K).normOneIsometryAmbientι q = h.unitTorus := by
  let j := ((scalar K).normOneIsometryAmbientι q).hom.hom
  have hmem : h.unitTorus.hom.hom ∈
      (SubgroupFunctor.range ((scalar K).normOneIsometryAmbientι q)).carrier (𝕊).X := by
    rw [mem_range_normOneIsometryAmbientι_iff_equations (scalar K) q (Quotient.out q)
      (Submodule.Quotient.mk_out q)]
    have hc := h.pointsEquiv_unitTorus (𝟙 (𝕊).X)
    simp only [Category.id_comp] at hc
    rw [hc]
    refine ⟨h.defect_familyScalingValue_mem _ _, ?_⟩
    apply Units.ext
    exact h.reducedNorm_familyScalingValue _ _
  obtain ⟨l, hl⟩ := SubgroupFunctor.mem_range.mp hmem
  have : IsMonHom l :=
    { one_hom := by
        apply (cancel_mono j).mp
        rw [Category.assoc, hl, IsMonHom.one_hom, IsMonHom.one_hom]
      mul_hom := by
        apply (cancel_mono j).mp
        rw [Category.assoc, hl, IsMonHom.mul_hom, Category.assoc,
          IsMonHom.mul_hom, CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc, hl] }
  exact ⟨Grp.homMk l, Grp.hom_ext _ _ hl⟩

/-- The scaling torus of a scalar hyperbolic family as a homomorphism into the
actual reduced-norm-one isometry group. -/
def normOneTorus : 𝕊 ⟶ (scalar K).normOneIsometryGroup q :=
  Classical.choose h.exists_normOneTorus

@[reassoc (attr := simp)] theorem normOneTorus_comp :
    h.normOneTorus ≫ (scalar K).normOneIsometryAmbientι q = h.unitTorus :=
  Classical.choose_spec h.exists_normOneTorus

instance mono_normOneTorus : Mono h.normOneTorus.hom.hom := by
  have hm : Mono (h.normOneTorus ≫ (scalar K).normOneIsometryAmbientι q).hom.hom := by
    rw [h.normOneTorus_comp]
    infer_instance
  change Mono (h.normOneTorus.hom.hom ≫
    ((scalar K).normOneIsometryAmbientι q).hom.hom) at hm
  exact mono_of_mono _ ((scalar K).normOneIsometryAmbientι q).hom.hom

/-- The family scaling is a closed split subtorus of the norm-one isometry group,
without a smoothness hypothesis on the isometry group. -/
theorem isClosedSubgroup_normOneTorus : IsClosedSubgroup h.normOneTorus := by
  have := isAffineHom_splitTorus (Spec (CommRingCat.of K)) I
  exact IsTorus.isClosedSubgroup_of_mono
    (IsSplitTorus.isTorus (isSplitTorus_splitTorus _)) _

/-- A scalar hyperbolic family gives the corresponding split-rank lower bound
for the actual norm-one isometry group. -/
theorem card_le_splitRank_normOneIsometryGroup :
    (Nat.card I : ℕ∞) ≤ splitRank ((scalar K).normOneIsometryGroup q) :=
  card_le_splitRank I h.normOneTorus h.isClosedSubgroup_normOneTorus

end IsHyperbolicFamily

/-- The actual norm-one isometry group's split rank is bounded above by the
quadratic Witt index, with no regularity or smoothness hypothesis. -/
theorem splitRank_normOneIsometryGroup_le (q : (scalar K).QuadraticForms n) :
    splitRank ((scalar K).normOneIsometryGroup q) ≤ ((scalar K).quadraticWittIndex q : ℕ∞) :=
  (splitRank_le_of_isClosedSubgroup ((scalar K).normOneIsometryGroupι q)
    ((scalar K).isClosedSubgroup_normOneIsometryGroupι q)).trans
      (QuadraticTorusWittBound.splitRank_isometryGroup_le (scalar K) q)

/-- For a scalar form with zero quadratic radical, the actual norm-one isometry
group has split rank equal to the quadratic Witt index in every characteristic. -/
theorem splitRank_normOneIsometryGroup_eq (q : (scalar K).QuadraticForms n)
    (hq : (scalar K).IsRadicalFreeQuadratic q) :
    splitRank ((scalar K).normOneIsometryGroup q) = ((scalar K).quadraticWittIndex q : ℕ∞) := by
  apply le_antisymm (splitRank_normOneIsometryGroup_le q)
  obtain ⟨x, y, h⟩ := exists_isHyperbolicFamily_of_radicalFree q hq
  have h' := (h.comp (fun k : ULift.{u} (Fin ((scalar K).quadraticWittIndex q)) => k.down)
    ULift.down_injective).card_le_splitRank_normOneIsometryGroup
  simpa using h'

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution

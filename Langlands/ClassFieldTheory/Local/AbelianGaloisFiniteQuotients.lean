import Langlands.ClassFieldTheory.Local.Galois
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-! # Finite quotients of the actual abelianized absolute Galois group -/

noncomputable section

namespace Langlands.LocalClassField

universe u

variable (K : Type u) [Field K] [PerfectField K]

namespace AbelianGaloisFiniteQuotients

/-- Pull an open subgroup back along the actual closed-commutator projection. -/
def fixingGroup (U : OpenSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    OpenSubgroup (Field.absoluteGaloisGroup K) :=
  U.comap (absoluteAbelianizationProjection K).toMonoidHom
    (absoluteAbelianizationProjection K).continuous

instance fixingGroup_normal
    (U : OpenSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    (fixingGroup K U).toSubgroup.Normal :=
  inferInstanceAs (Subgroup.comap (absoluteAbelianizationProjection K).toMonoidHom
    U.toSubgroup).Normal

/-- The fixed field of the actual inverse image of an open subgroup. -/
def fixedField (U : OpenSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.fixedField (fixingGroup K U).toSubgroup

private theorem fixedField_fixingGroup
    (U : OpenSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    (fixedField K U).fixingSubgroup = (fixingGroup K U).toSubgroup := by
  let : IsGalois K (AlgebraicClosure K) := ⟨⟩
  exact InfiniteGalois.fixingSubgroup_fixedField
    ⟨(fixingGroup K U).toSubgroup, (fixingGroup K U).isClosed⟩

instance fixedField_finite
    (U : OpenSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    FiniteDimensional K (fixedField K U) := by
  let : IsGalois K (AlgebraicClosure K) := ⟨⟩
  apply (InfiniteGalois.isOpen_iff_finite _).mp
  rw [fixedField_fixingGroup]
  exact (fixingGroup K U).isOpen

instance fixedField_galois
    (U : OpenSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    IsGalois K (fixedField K U) := by
  let : IsGalois K (AlgebraicClosure K) := ⟨⟩
  apply (InfiniteGalois.normal_iff_isGalois _).mp
  rw [fixedField_fixingGroup]
  exact fixingGroup_normal K U

instance fixedField_commutative
    (U : OpenSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    IsMulCommutative Gal(fixedField K U/K) := by
  let : IsGalois K (AlgebraicClosure K) := ⟨⟩
  let : (fixingGroup K U).toSubgroup.Normal := fixingGroup_normal K U
  have hcomm : commutator (Field.absoluteGaloisGroup K) ≤
      (fixingGroup K U).toSubgroup := by
    intro g hg
    change absoluteAbelianizationProjection K g ∈ U
    have hg' := Abelianization.commutator_subset_ker
      (absoluteAbelianizationProjection K).toMonoidHom hg
    change absoluteAbelianizationProjection K g = 1 at hg'
    rw [hg']
    exact U.one_mem
  let H : ClosedSubgroup Gal(AlgebraicClosure K/K) :=
    ⟨(fixingGroup K U).toSubgroup, (fixingGroup K U).isClosed⟩
  let : H.toSubgroup.Normal := fixingGroup_normal K U
  let : IsMulCommutative (Gal(AlgebraicClosure K/K) ⧸ H.toSubgroup) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  let e := InfiniteGalois.normalAutEquivQuotient H
  exact e.surjective.isMulCommutative inferInstance

/-- Every open subgroup of the actual Galois abelianization determines an
actual finite abelian intermediate extension in the chosen algebraic closure. -/
def extension (U : OpenSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    FiniteAbelianExtension K :=
  ⟨{ fixedField K U with
      finiteDimensional := inferInstance
      isGalois := inferInstance }, inferInstance⟩

/-- The defining finite restriction has exactly the original open subgroup
as its kernel. -/
theorem extension_ker
    (U : OpenSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    (extension K U).abelianRestriction.toMonoidHom.ker = U.toSubgroup := by
  apply Subgroup.comap_injective
    (f := (absoluteAbelianizationProjection K).toMonoidHom)
    (QuotientGroup.mk'_surjective _)
  change ((extension K U).restriction.toMonoidHom).ker =
    (fixingGroup K U).toSubgroup
  exact (fixedField K U).restrictNormalHom_ker.trans (fixedField_fixingGroup K U)

omit [PerfectField K] in
/-- Actual finite restriction is surjective after closed-commutator descent. -/
theorem abelianRestriction_surjective (L : FiniteAbelianExtension K) :
    Function.Surjective L.abelianRestriction := by
  intro s
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) s
  exact ⟨absoluteAbelianizationProjection K g, hg⟩

/-- The finite Galois quotient of the field attached to an open subgroup is
canonically the corresponding group quotient. -/
def quotientEquiv (U : OpenSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    (Field.absoluteGaloisGroupAbelianization K ⧸ U.toSubgroup) ≃ₜ*
      (extension K U).galoisGroup :=
  { QuotientGroup.liftEquiv U.toSubgroup
      (abelianRestriction_surjective K (extension K U)) (extension_ker K U).symm with
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

@[simp] theorem quotientEquiv_mk
    (U : OpenSubgroup (Field.absoluteGaloisGroupAbelianization K))
    (g : Field.absoluteGaloisGroupAbelianization K) :
    quotientEquiv K U (QuotientGroup.mk g) = (extension K U).abelianRestriction g :=
  rfl

end AbelianGaloisFiniteQuotients

end Langlands.LocalClassField

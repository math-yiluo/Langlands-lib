import Langlands.GroupTheory.CocycleExtension
import Mathlib.GroupTheory.Transfer

noncomputable section

universe u v

namespace Langlands.NormalizedTwoCocycle.ExtensionTransfer

open Subgroup Subgroup.leftTransversals MulAction
open scoped Pointwise

variable {G : Type u} {A : Type v} [Group G] [CommGroup A]
  [MulDistribMulAction G A] (c : NormalizedTwoCocycle G A)

/-- The actual coefficient subgroup of the cocycle extension. -/
abbrev coefficientSubgroup : Subgroup c.Extension := (Extension.inl c).range

instance coefficientSubgroup_normal : (coefficientSubgroup c).Normal := by
  rw [coefficientSubgroup, Extension.range_inl_eq_ker_projection]
  infer_instance

/-- The actual coefficient-subgroup identification with the coefficient group. -/
def coefficientSubgroupEquiv : coefficientSubgroup c ≃* A :=
  (MonoidHom.ofInjective (Extension.inl_injective c)).symm

@[simp] lemma inl_coefficientSubgroupEquiv (a : coefficientSubgroup c) :
    Extension.inl c (coefficientSubgroupEquiv c a) = a :=
  MonoidHom.apply_ofInjective_symm (Extension.inl_injective c) a

lemma quotient_eq_iff_projection (x y : c.Extension) :
    (QuotientGroup.mk x : c.Extension ⧸ coefficientSubgroup c) =
        QuotientGroup.mk y ↔ x.right = y.right := by
  rw [QuotientGroup.eq, coefficientSubgroup, Extension.range_inl_eq_ker_projection,
    MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
  rfl

/-- Projection identifies the coefficient quotient with the acting group. -/
def quotientProjection : c.Extension ⧸ coefficientSubgroup c →* G :=
  QuotientGroup.lift _ (Extension.projection c) (by
    rintro x ⟨a, rfl⟩
    rfl)

@[simp] lemma quotientProjection_mk (x : c.Extension) :
    quotientProjection c (QuotientGroup.mk x) = x.right := rfl

lemma quotientProjection_bijective : Function.Bijective (quotientProjection c) := by
  constructor
  · intro q r h
    induction q using QuotientGroup.induction_on with
    | H x =>
      induction r using QuotientGroup.induction_on with
      | H y =>
        exact (quotient_eq_iff_projection c x y).2 h
  · intro g
    exact ⟨QuotientGroup.mk (Extension.sectionMap c g), rfl⟩

def quotientProjectionEquiv : c.Extension ⧸ coefficientSubgroup c ≃* G :=
  MulEquiv.ofBijective (quotientProjection c) (quotientProjection_bijective c)

lemma quotientProjection_smul (x : c.Extension) (q : c.Extension ⧸ coefficientSubgroup c) :
    quotientProjection c (x • q) = x.right * quotientProjection c q := by
  induction q using QuotientGroup.induction_on with
  | H y => rfl

/-- Representatives given by the inverses of the distinguished section. -/
def inverseSectionRepresentative (q : c.Extension ⧸ coefficientSubgroup c) : c.Extension :=
  (Extension.sectionMap c (quotientProjection c q)⁻¹)⁻¹

lemma inverseSectionRepresentative_mk (q : c.Extension ⧸ coefficientSubgroup c) :
    (QuotientGroup.mk (inverseSectionRepresentative c q) :
      c.Extension ⧸ coefficientSubgroup c) = q := by
  apply (quotientProjection_bijective c).1
  change (Extension.projection c)
    ((Extension.sectionMap c (quotientProjection c q)⁻¹)⁻¹) = quotientProjection c q
  simp

/-- The inverse-section representatives form a left transversal. -/
def inverseSectionTransversal : (coefficientSubgroup c).LeftTransversal :=
  ⟨Set.range (inverseSectionRepresentative c),
    isComplement_range_left (inverseSectionRepresentative_mk c)⟩

lemma inverseSectionTransversal_apply (q : c.Extension ⧸ coefficientSubgroup c) :
    ((inverseSectionTransversal c).2.leftQuotientEquiv q : c.Extension) =
      inverseSectionRepresentative c q :=
  IsComplement.leftQuotientEquiv_apply (inverseSectionRepresentative_mk c) q

lemma section_mul_element (g : G) (x : c.Extension) :
    Extension.sectionMap c g * x =
      Extension.inl c ((g • x.left) * c (g, x.right)) *
        Extension.sectionMap c (g * x.right) := by
  apply Extension.ext <;> simp

lemma section_mul_element_factor (g : G) (x : c.Extension) :
    Extension.sectionMap c g * x * (Extension.sectionMap c (g * x.right))⁻¹ =
      Extension.inl c ((g • x.left) * c (g, x.right)) := by
  rw [section_mul_element, mul_inv_cancel_right]

variable [Fintype G]

instance coefficientSubgroup_finiteIndex : (coefficientSubgroup c).FiniteIndex := by
  let _ : Finite (c.Extension ⧸ coefficientSubgroup c) :=
    Finite.of_equiv G (quotientProjectionEquiv c).toEquiv.symm
  exact Subgroup.finiteIndex_of_finite_quotient

/-- Mathlib's actual coset-product transfer is the product of the explicit cocycle factors. -/
theorem transfer_eq_prod (x : c.Extension) :
    MonoidHom.transfer (coefficientSubgroupEquiv c).toMonoidHom x =
      ∏ g : G, (g • x.left) * c (g, x.right) := by
  let _ := (coefficientSubgroup c).fintypeQuotientOfFiniteIndex
  let e : (c.Extension ⧸ coefficientSubgroup c) ≃ G :=
    (quotientProjectionEquiv c).toEquiv.trans (Equiv.inv G)
  rw [MonoidHom.transfer_def _ (inverseSectionTransversal c)]
  simp only [diff]
  refine Fintype.prod_equiv e _ _ fun q => ?_
  apply (Extension.inl_injective c)
  change Extension.inl c (coefficientSubgroupEquiv c _) = _
  rw [inl_coefficientSubgroupEquiv]
  change ((inverseSectionTransversal c).2.leftQuotientEquiv q : c.Extension)⁻¹ *
      ((x • inverseSectionTransversal c).2.leftQuotientEquiv q : c.Extension) =
    Extension.inl c ((e q • x.left) * c (e q, x.right))
  rw [smul_apply_eq_smul_apply_inv_smul, smul_eq_mul,
    inverseSectionTransversal_apply, inverseSectionTransversal_apply]
  simp only [inverseSectionRepresentative, quotientProjection_smul,
    Extension.inv_right, mul_inv_rev, inv_inv]
  change Extension.sectionMap c (quotientProjection c q)⁻¹ *
      (x * (Extension.sectionMap c ((quotientProjection c q)⁻¹ * x.right))⁻¹) =
    Extension.inl c (((quotientProjection c q)⁻¹ • x.left) *
      c ((quotientProjection c q)⁻¹, x.right))
  rw [← mul_assoc, section_mul_element_factor]

end Langlands.NormalizedTwoCocycle.ExtensionTransfer

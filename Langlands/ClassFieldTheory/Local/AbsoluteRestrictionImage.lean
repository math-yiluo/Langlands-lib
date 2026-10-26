import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section

namespace Langlands.ClassFieldTheory.Local.AbsoluteRestriction

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]

local instance canonicalClosureAlgebra : Algebra L (AlgebraicClosure L) :=
  AlgebraicClosure.instAlgebra L

/-- The supplied base-compatible closure embedding is a field equivalence. -/
def closureEquiv : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure L := by
  haveI : Algebra.IsIntegral K (AlgebraicClosure L) :=
    Algebra.IsIntegral.trans (R := K) (A := L) (B := AlgebraicClosure L)
  haveI : Algebra.IsIntegral (AlgebraicClosure K) (AlgebraicClosure L) :=
    Algebra.IsIntegral.tower_top (R := K)
  exact AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom K (AlgebraicClosure K) (AlgebraicClosure L))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

@[simp] theorem closureEquiv_apply (x : AlgebraicClosure K) :
    closureEquiv K L x = algebraMap (AlgebraicClosure K) (AlgebraicClosure L) x := rfl

/-- The embedding of L in the lower closure determined by the supplied closure map. -/
def fieldEmbedding : L →ₐ[K] AlgebraicClosure K :=
  (closureEquiv K L).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom K L (AlgebraicClosure L))

@[simp] theorem closureEquiv_fieldEmbedding (x : L) :
    closureEquiv K L (fieldEmbedding K L x) = algebraMap L (AlgebraicClosure L) x :=
  (closureEquiv K L).apply_symm_apply _

/-- The actual image field; no chosen normal copy of L is used. -/
def imageField : IntermediateField K (AlgebraicClosure K) :=
  (fieldEmbedding K L).fieldRange

/-- The original extension and its actual image have the same degree. -/
def imageFieldEquiv : L ≃ₐ[K] imageField K L :=
  (fieldEmbedding K L).equivFieldRange

instance imageField_finiteDimensional : FiniteDimensional K (imageField K L) :=
  (imageFieldEquiv K L).toLinearEquiv.finiteDimensional

theorem imageField_finrank : Module.finrank K (imageField K L) = Module.finrank K L :=
  (imageFieldEquiv K L).toLinearEquiv.finrank_eq.symm

theorem closureEquiv_symm_mem (x : L) :
    (closureEquiv K L).symm (algebraMap L (AlgebraicClosure L) x) ∈ imageField K L :=
  ⟨x, rfl⟩

/-- Actual absolute restriction fixes the image field pointwise. -/
theorem map_mem_fixingSubgroup (σ : Field.absoluteGaloisGroup L) :
    Field.absoluteGaloisGroup.mapOfAlgebra K L σ ∈ (imageField K L).fixingSubgroup := by
  change Gal(AlgebraicClosure L/L) at σ
  change ((σ.restrictScalars K).restrictNormal (AlgebraicClosure K)) ∈
    (imageField K L).fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  rintro x ⟨y, rfl⟩
  apply (closureEquiv K L).injective
  change algebraMap (AlgebraicClosure K) (AlgebraicClosure L)
      ((σ.restrictScalars K).restrictNormal (AlgebraicClosure K) (fieldEmbedding K L y)) = _
  rw [AlgEquiv.restrictNormal_commutes]
  change σ (closureEquiv K L (fieldEmbedding K L y)) =
    closureEquiv K L (fieldEmbedding K L y)
  rw [closureEquiv_fieldEmbedding]
  exact σ.commutes _

/-- The image fixing subgroup is open because L/K is finite. -/
def openSubgroup : OpenSubgroup (Field.absoluteGaloisGroup K) :=
  ⟨(imageField K L).fixingSubgroup, (imageField K L).fixingSubgroup_isOpen⟩

/-- The specified absolute restriction, with codomain restricted to its open image. -/
def subgroupMap : Field.absoluteGaloisGroup L →ₜ* openSubgroup K L where
  toFun σ := ⟨Field.absoluteGaloisGroup.mapOfAlgebra K L σ, map_mem_fixingSubgroup K L σ⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ σ τ)
  continuous_toFun := (Field.absoluteGaloisGroup.mapOfAlgebra K L).continuous.subtype_mk _

/-- The field-level commuting square retains the exact supplied algebra map. -/
theorem subgroupMap_commutes (σ : Field.absoluteGaloisGroup L) (x : AlgebraicClosure K) :
    closureEquiv K L ((subgroupMap K L σ).val.toRingEquiv x) =
      σ.toRingEquiv (closureEquiv K L x) :=
  AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) _ x

/-- Conjugation through the closure equivalence gives an automorphism fixing canonical L. -/
def subgroupInverse (σ : openSubgroup K L) : Field.absoluteGaloisGroup L :=
  { ((closureEquiv K L).symm.toRingEquiv.trans σ.val.toRingEquiv).trans
      (closureEquiv K L).toRingEquiv with
    commutes' x := by
      change closureEquiv K L
        (σ.val.toRingEquiv ((closureEquiv K L).symm (algebraMap L (AlgebraicClosure L) x))) = _
      exact (congrArg (closureEquiv K L)
        ((IntermediateField.mem_fixingSubgroup_iff (imageField K L) σ.val).mp σ.property _
          (closureEquiv_symm_mem K L x))).trans ((closureEquiv K L).apply_symm_apply _) }

theorem subgroupMap_left_inverse :
    Function.LeftInverse (subgroupInverse K L) (subgroupMap K L) := by
  intro σ
  apply AlgEquiv.ext
  intro x
  change closureEquiv K L
    ((subgroupMap K L σ).val.toRingEquiv ((closureEquiv K L).symm x)) = σ.toRingEquiv x
  rw [subgroupMap_commutes, AlgEquiv.apply_symm_apply]

theorem subgroupMap_right_inverse :
    Function.RightInverse (subgroupInverse K L) (subgroupMap K L) := by
  intro σ
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply (closureEquiv K L).injective
  exact (subgroupMap_commutes K L (subgroupInverse K L σ) x).trans
    (congrArg (fun y => closureEquiv K L (σ.val.toRingEquiv y))
      ((closureEquiv K L).symm_apply_apply x))

/-- Algebraic identification with the actual open image. -/
def subgroupMulEquiv : Field.absoluteGaloisGroup L ≃* openSubgroup K L :=
  { subgroupMap K L with
    invFun := subgroupInverse K L
    left_inv := subgroupMap_left_inverse K L
    right_inv := subgroupMap_right_inverse K L }

theorem openSubgroup_eq_range :
    (openSubgroup K L).toSubgroup =
      (Field.absoluteGaloisGroup.mapOfAlgebra K L).toMonoidHom.range := by
  ext σ
  constructor
  · intro hσ
    refine ⟨subgroupInverse K L ⟨σ, hσ⟩, ?_⟩
    exact congrArg Subtype.val (subgroupMap_right_inverse K L ⟨σ, hσ⟩)
  · rintro ⟨τ, rfl⟩
    exact map_mem_fixingSubgroup K L τ

theorem map_injective : Function.Injective (Field.absoluteGaloisGroup.mapOfAlgebra K L) := by
  intro σ τ h
  apply (subgroupMulEquiv K L).injective
  exact Subtype.ext h

theorem range_isOpen :
    IsOpen ((Field.absoluteGaloisGroup.mapOfAlgebra K L).toMonoidHom.range :
      Set (Field.absoluteGaloisGroup K)) := by
  rw [← openSubgroup_eq_range]
  exact (openSubgroup K L).isOpen

variable [CharZero K]

/-- Restriction is a continuous multiplicative equivalence onto its open image. -/
def groupEquiv : Field.absoluteGaloisGroup L ≃ₜ* openSubgroup K L := by
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  letI : CompactSpace (Field.absoluteGaloisGroup L) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure L/L))
  letI : T2Space (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (T2Space Gal(AlgebraicClosure K/K))
  exact
    { subgroupMulEquiv K L with
      continuous_toFun := (subgroupMap K L).continuous
      continuous_invFun :=
        Continuous.continuous_symm_of_equiv_compact_to_t2
          (f := (subgroupMulEquiv K L).toEquiv) (subgroupMap K L).continuous }

/-- Inclusion after the equivalence is the specified homomorphism. -/
theorem groupEquiv_subtype :
    (openSubgroup K L).toSubgroup.subtype.comp (groupEquiv K L).toMonoidHom =
      (Field.absoluteGaloisGroup.mapOfAlgebra K L).toMonoidHom := rfl

@[simp] theorem groupEquiv_apply_val (σ : Field.absoluteGaloisGroup L) :
    (groupEquiv K L σ).val = Field.absoluteGaloisGroup.mapOfAlgebra K L σ := rfl

/-- The index equals the degree for every finite extension, including nonnormal ones. -/
theorem index_eq_finrank : (openSubgroup K L).toSubgroup.index = Module.finrank K L := by
  change (imageField K L).fixingSubgroup.index = _
  rw [← IntermediateField.finrank_eq_fixingSubgroup_index, imageField_finrank]

end Langlands.ClassFieldTheory.Local.AbsoluteRestriction

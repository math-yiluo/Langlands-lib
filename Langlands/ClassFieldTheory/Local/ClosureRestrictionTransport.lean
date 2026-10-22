import Langlands.ClassFieldTheory.Local.ClosureCoefficients
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K : Type u) [Field K]
variable (E : IntermediateField K (AlgebraicClosure K))
  [Normal K E]
  [Algebra (AlgebraicClosure K) (AlgebraicClosure E)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure E)]

local instance canonicalClosureAlgebra : Algebra E (AlgebraicClosure E) :=
  AlgebraicClosure.instAlgebra E

/-- The specified closure embedding is an isomorphism over the base field. -/
def suppliedClosureEquiv : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure E := by
  haveI : Algebra.IsIntegral K (AlgebraicClosure E) :=
    Algebra.IsIntegral.trans (R := K) (A := E) (B := AlgebraicClosure E)
  haveI : Algebra.IsIntegral (AlgebraicClosure K) (AlgebraicClosure E) :=
    Algebra.IsIntegral.tower_top (R := K)
  exact AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom K (AlgebraicClosure K) (AlgebraicClosure E))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

omit [Normal K E] in
@[simp] theorem suppliedClosureEquiv_apply (x : AlgebraicClosure K) :
    suppliedClosureEquiv K E x = algebraMap (AlgebraicClosure K) (AlgebraicClosure E) x := rfl

/-- Normality puts the inverse image of the canonical copy of E back in E. -/
theorem suppliedClosureEquiv_symm_mem (x : E) :
    (suppliedClosureEquiv K E).symm (algebraMap E (AlgebraicClosure E) x) ∈ E := by
  let j : E →ₐ[K] AlgebraicClosure K :=
    (suppliedClosureEquiv K E).symm.toAlgHom.comp
      (IsScalarTower.toAlgHom K E (AlgebraicClosure E))
  have h := j.fieldRange_of_normal
  exact (le_of_eq h) (show j x ∈ j.fieldRange from ⟨x, rfl⟩)

/-- The inverse closure embedding permutes E, rather than fixing its chosen embedding. -/
def suppliedClosureTwist : E ≃ₐ[K] E :=
  ((suppliedClosureEquiv K E).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom K E (AlgebraicClosure E))).restrictNormal' E

theorem suppliedClosureTwist_commutes (x : E) :
    ((suppliedClosureTwist K E x : E) : AlgebraicClosure K) =
      (suppliedClosureEquiv K E).symm (algebraMap E (AlgebraicClosure E) x) := by
  exact AlgHom.restrictNormal_commutes _ E x

theorem suppliedClosureEquiv_apply_subtype (x : E) :
    suppliedClosureEquiv K E (x : AlgebraicClosure K) =
      algebraMap E (AlgebraicClosure E) ((suppliedClosureTwist K E).symm x) := by
  apply (suppliedClosureEquiv K E).symm.injective
  rw [(suppliedClosureEquiv K E).symm_apply_apply,
    ← suppliedClosureTwist_commutes, AlgEquiv.apply_symm_apply]

/-- The actual absolute restriction homomorphism fixes E for every supplied embedding. -/
theorem absoluteGalois_map_mem_fixingSubgroup (σ : Field.absoluteGaloisGroup E) :
    Field.absoluteGaloisGroup.mapOfAlgebra K E σ ∈ E.fixingSubgroup := by
  change Gal(AlgebraicClosure E/E) at σ
  change ((σ.restrictScalars K).restrictNormal (AlgebraicClosure K)) ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  apply (suppliedClosureEquiv K E).injective
  change algebraMap (AlgebraicClosure K) (AlgebraicClosure E)
      ((σ.restrictScalars K).restrictNormal (AlgebraicClosure K) x) = _
  rw [AlgEquiv.restrictNormal_commutes]
  change σ (suppliedClosureEquiv K E x) = suppliedClosureEquiv K E x
  rw [suppliedClosureEquiv_apply_subtype K E ⟨x, hx⟩]
  exact σ.commutes _

/-- Absolute restriction with codomain restricted to the actual fixing subgroup. -/
def closureSubgroupMap : Field.absoluteGaloisGroup E →ₜ* E.fixingSubgroup where
  toFun σ := ⟨Field.absoluteGaloisGroup.mapOfAlgebra K E σ,
    absoluteGalois_map_mem_fixingSubgroup K E σ⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ σ τ)
  continuous_toFun := (Field.absoluteGaloisGroup.mapOfAlgebra K E).continuous.subtype_mk _

/-- The field-level commuting square for the subgroup map. -/
theorem closureSubgroupMap_commutes (σ : Field.absoluteGaloisGroup E)
    (x : AlgebraicClosure K) :
    suppliedClosureEquiv K E ((closureSubgroupMap K E σ).val x) =
      σ.toRingEquiv (suppliedClosureEquiv K E x) := by
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) _ x

/-- Conjugation through the supplied closure equivalence, on the fixing subgroup. -/
def closureSubgroupInverse (σ : E.fixingSubgroup) : Field.absoluteGaloisGroup E :=
  { ((suppliedClosureEquiv K E).symm.toRingEquiv.trans σ.val.toRingEquiv).trans
      (suppliedClosureEquiv K E).toRingEquiv with
    commutes' x := by
      change suppliedClosureEquiv K E
        (σ.val ((suppliedClosureEquiv K E).symm (algebraMap E (AlgebraicClosure E) x))) = _
      rw [(IntermediateField.mem_fixingSubgroup_iff E σ.val).mp σ.property _
        (suppliedClosureEquiv_symm_mem K E x)]
      exact (suppliedClosureEquiv K E).apply_symm_apply _ }

theorem closureSubgroupMap_left_inverse :
    Function.LeftInverse (closureSubgroupInverse K E) (closureSubgroupMap K E) := by
  intro σ
  apply AlgEquiv.ext
  intro x
  change suppliedClosureEquiv K E
    ((closureSubgroupMap K E σ).val ((suppliedClosureEquiv K E).symm x)) = σ.toRingEquiv x
  rw [closureSubgroupMap_commutes, AlgEquiv.apply_symm_apply]

theorem closureSubgroupMap_right_inverse :
    Function.RightInverse (closureSubgroupInverse K E) (closureSubgroupMap K E) := by
  intro σ
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply (suppliedClosureEquiv K E).injective
  rw [closureSubgroupMap_commutes]
  change suppliedClosureEquiv K E
    (σ.val ((suppliedClosureEquiv K E).symm (suppliedClosureEquiv K E x))) = _
  rw [AlgEquiv.symm_apply_apply]

/-- Actual absolute restriction identifies the source with the fixing subgroup. -/
def closureSubgroupMulEquiv : Field.absoluteGaloisGroup E ≃* E.fixingSubgroup :=
  { closureSubgroupMap K E with
    invFun := closureSubgroupInverse K E
    left_inv := closureSubgroupMap_left_inverse K E
    right_inv := closureSubgroupMap_right_inverse K E }

variable [CharZero K]

/-- The fixing-subgroup identification is a homeomorphism for the Krull topologies. -/
def closureSubgroupEquiv : Field.absoluteGaloisGroup E ≃ₜ* E.fixingSubgroup := by
  letI : CompactSpace (Field.absoluteGaloisGroup E) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure E/E))
  exact
    { closureSubgroupMulEquiv K E with
      continuous_toFun := (closureSubgroupMap K E).continuous
      continuous_invFun :=
        Continuous.continuous_symm_of_equiv_compact_to_t2
          (f := (closureSubgroupMulEquiv K E).toEquiv)
          (closureSubgroupMap K E).continuous }

/-- Inclusion after the equivalence is the specified absolute Galois map. -/
theorem closureSubgroupEquiv_subtype :
    E.fixingSubgroup.subtype.comp (closureSubgroupEquiv K E).toMonoidHom =
      (Field.absoluteGaloisGroup.mapOfAlgebra K E).toMonoidHom := rfl

@[simp] theorem closureSubgroupEquiv_apply_val (σ : Field.absoluteGaloisGroup E) :
    (closureSubgroupEquiv K E σ).val = Field.absoluteGaloisGroup.mapOfAlgebra K E σ := rfl

end Langlands.ClassFieldTheory.Local

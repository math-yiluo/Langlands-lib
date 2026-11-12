import Langlands.ClassFieldTheory.Local.ReciprocitySystem
import Langlands.ClassFieldTheory.Local.WeilReciprocityExistenceAssembly
import Mathlib.FieldTheory.Normal.Closure

/-! # Actual finite Galois restrictions of common-closure fixing subgroups -/

noncomputable section

namespace Langlands.LocalClassField.FiniteQuotientTransport

universe u

/-- For a discrete group, closure of the commutator adds no elements. -/
def discreteAbelianizationEquiv (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [DiscreteTopology G] :
    TopologicalAbelianization G ≃* Abelianization G :=
  QuotientGroup.quotientMulEquivOfEq (by
    apply SetLike.coe_injective
    change closure (commutator G : Set G) = _
    exact (isClosed_discrete _).closure_eq)

@[simp] theorem discreteAbelianizationEquiv_projection (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] (g : G) :
    discreteAbelianizationEquiv G (abelianizationProjection G g) = Abelianization.of g :=
  QuotientGroup.quotientMulEquivOfEq_mk _ g

variable (K : Type u) [Field K]
  (E : FiniteIntermediateExtension K)
  (M : FiniteGaloisIntermediateField K (AlgebraicClosure K))
  (h : E.field ≤ M.toIntermediateField)

/-- The scalar structure on the finite field induced by the literal intermediate-field inclusion. -/
abbrev finiteRestrictionAlgebra : Algebra E.field M :=
  (IntermediateField.inclusion h).toAlgebra

/-- Restriction of an actual common-closure fixing automorphism to a finite Galois field. -/
def finiteRestrictionHom :
    letI := finiteRestrictionAlgebra K E M h
    E.field.fixingSubgroup →* Gal(M/E.field) := by
  letI := finiteRestrictionAlgebra K E M h
  letI : IsScalarTower K E.field M := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower E.field M (AlgebraicClosure K) := IsScalarTower.of_algebraMap_eq' rfl
  letI : Normal E.field M := Normal.tower_top_of_normal K E.field M
  exact (AlgEquiv.restrictNormalHom (F := E.field) (K₁ := AlgebraicClosure K) M).comp
    (IntermediateField.fixingSubgroupEquiv E.field).toMonoidHom

/-- The restricted automorphism acts by the same ambient automorphism. -/
theorem finiteRestrictionHom_apply (σ : E.field.fixingSubgroup) (x : M) :
    letI := finiteRestrictionAlgebra K E M h
    (finiteRestrictionHom K E M h σ x : AlgebraicClosure K) =
      AlgEquiv.toAlgHom σ.val x := by
  let := finiteRestrictionAlgebra K E M h
  let : IsScalarTower K E.field M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower E.field M (AlgebraicClosure K) := IsScalarTower.of_algebraMap_eq' rfl
  let : Normal E.field M := Normal.tower_top_of_normal K E.field M
  exact AlgEquiv.restrictNormal_commutes
    (IntermediateField.fixingSubgroupEquiv E.field σ) M x

/-- Restriction is trivial exactly when the ambient automorphism fixes the finite field. -/
theorem finiteRestrictionHom_ker :
    letI := finiteRestrictionAlgebra K E M h
    (finiteRestrictionHom K E M h).ker = M.toIntermediateField.fixingSubgroup.subgroupOf
      E.field.fixingSubgroup := by
  let := finiteRestrictionAlgebra K E M h
  ext σ
  change finiteRestrictionHom K E M h σ = 1 ↔ σ.val ∈ M.toIntermediateField.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hσ x hx
    have hh := finiteRestrictionHom_apply K E M h σ ⟨x, hx⟩
    rw [hσ] at hh
    exact hh.symm
  · intro hσ
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change (finiteRestrictionHom K E M h σ x : AlgebraicClosure K) = (x : AlgebraicClosure K)
    rw [finiteRestrictionHom_apply]
    exact hσ x x.property

/-- The actual finite restriction is continuous for the inherited Krull topologies. -/
def finiteRestriction :
    letI := finiteRestrictionAlgebra K E M h
    E.field.fixingSubgroup →ₜ* Gal(M/E.field) := by
  letI := finiteRestrictionAlgebra K E M h
  letI : IsScalarTower K E.field M := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional E.field M := FiniteDimensional.right K E.field M
  exact
    { toMonoidHom := finiteRestrictionHom K E M h
      continuous_toFun := WeilReciprocityExistence.continuous_of_isOpen_ker _ (by
        rw [finiteRestrictionHom_ker]
        exact M.toIntermediateField.fixingSubgroup_isOpen.preimage continuous_subtype_val) }

/-- Every automorphism of the finite field over the intermediate base extends in the closure. -/
theorem finiteRestriction_surjective :
    letI := finiteRestrictionAlgebra K E M h
    Function.Surjective (finiteRestriction K E M h) := by
  let := finiteRestrictionAlgebra K E M h
  let : IsScalarTower K E.field M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower E.field M (AlgebraicClosure K) := IsScalarTower.of_algebraMap_eq' rfl
  let : Normal E.field M := Normal.tower_top_of_normal K E.field M
  exact (AlgEquiv.restrictNormalHom_surjective (F := E.field) (AlgebraicClosure K)).comp
    (IntermediateField.fixingSubgroupEquiv E.field).surjective

/-- Actual finite restriction followed by the algebraic finite Galois abelianization. -/
def finiteAbelianRestriction :
    letI := finiteRestrictionAlgebra K E M h
    TopologicalAbelianization E.field.fixingSubgroup →* Abelianization Gal(M/E.field) := by
  letI := finiteRestrictionAlgebra K E M h
  letI : IsScalarTower K E.field M := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional E.field M := FiniteDimensional.right K E.field M
  exact (discreteAbelianizationEquiv Gal(M/E.field)).toMonoidHom.comp
    (abelianizationMap (finiteRestriction K E M h)).toMonoidHom

@[simp] theorem finiteAbelianRestriction_projection (σ : E.field.fixingSubgroup) :
    letI := finiteRestrictionAlgebra K E M h
    finiteAbelianRestriction K E M h (abelianizationProjection _ σ) =
      Abelianization.of (finiteRestriction K E M h σ) := by
  let := finiteRestrictionAlgebra K E M h
  let : IsScalarTower K E.field M := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional E.field M := FiniteDimensional.right K E.field M
  exact discreteAbelianizationEquiv_projection _ _

end Langlands.LocalClassField.FiniteQuotientTransport

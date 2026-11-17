import Langlands.GroupScheme.SimplyConnected.TypeD4StarOrbits
import Langlands.GroupScheme.SimplyConnected.OuterTypeAQuadraticExtension
import Mathlib.GroupTheory.Index

/-! # A separable cubic field fixing a leaf of a trialitarian D4 diagram -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- The subgroup of the full absolute Galois group fixing one actual simple
vertex under the star action. -/
def starVertexStabilizer (a : d.Vertex) :
    Subgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K) where
  carrier := {σ | d.star σ a = a}
  one_mem' := d.star_one a
  mul_mem' := by
    intro σ τ hσ hτ
    change d.star (σ * τ) a = a
    change d.star σ a = a at hσ
    change d.star τ a = a at hτ
    rw [d.star_mul, hτ, hσ]
  inv_mem' := by
    intro σ hσ
    have h := congrArg (d.star σ⁻¹) hσ
    rw [← d.star_mul, inv_mul_cancel, d.star_one] at h
    exact h.symm

@[simp] theorem mem_starVertexStabilizer (a : d.Vertex)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    σ ∈ d.starVertexStabilizer a ↔ d.star σ a = a :=
  Iff.rfl

theorem starKernel_le_starVertexStabilizer (a : d.Vertex) :
    d.starKernel ≤ d.starVertexStabilizer a :=
  fun _ h => h a

/-- A vertex stabilizer is open because it contains the open star kernel. -/
theorem starVertexStabilizer_isOpen (a : d.Vertex) :
    IsOpen (d.starVertexStabilizer a :
      Set (SeparableClosure K ≃ₐ[K] SeparableClosure K)) :=
  Subgroup.isOpen_mono (d.starKernel_le_starVertexStabilizer a) d.starKernel_isOpen

theorem starVertexStabilizer_isClosed (a : d.Vertex) :
    IsClosed (d.starVertexStabilizer a :
      Set (SeparableClosure K ≃ₐ[K] SeparableClosure K)) :=
  Subgroup.isClosed_of_isOpen _ (d.starVertexStabilizer_isOpen a)

/-- The field of definition of one vertex for the full star action, inside
the separable closure of the original field. -/
def starVertexField (a : d.Vertex) : IntermediateField K (SeparableClosure K) :=
  IntermediateField.fixedField (d.starVertexStabilizer a)

theorem starVertexField_fixingSubgroup (a : d.Vertex) :
    (d.starVertexField a).fixingSubgroup = d.starVertexStabilizer a :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨d.starVertexStabilizer a, d.starVertexStabilizer_isClosed a⟩

/-- Fixing the vertex field pointwise is exactly fixing the original vertex
under the full absolute Galois star action. -/
theorem fixes_starVertexField_iff (a : d.Vertex)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    (∀ x ∈ d.starVertexField a, σ x = x) ↔ d.star σ a = a := by
  rw [← IntermediateField.mem_fixingSubgroup_iff, d.starVertexField_fixingSubgroup]
  rfl

theorem finrank_starVertexField (a : d.Vertex) :
    Module.finrank K (d.starVertexField a) = (d.starVertexStabilizer a).index := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index,
    d.starVertexField_fixingSubgroup]

/-- The vertex field is separable over the original field. -/
theorem isSeparable_starVertexField (a : d.Vertex) :
    Algebra.IsSeparable K (d.starVertexField a) :=
  inferInstance

/-- In type D4, when no leaf is globally fixed, each leaf stabilizer has
index exactly three in the full absolute Galois group. -/
theorem starVertexStabilizer_index_of_D4_no_fixed_leaf
    (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hno : ¬ ∃ a : d.Vertex, e a ≠ 1 ∧
      ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a)
    (a : d.Vertex) (ha : e a ≠ 1) :
    (d.starVertexStabilizer a).index = 3 := by
  classical
  let Γ := SeparableClosure K ≃ₐ[K] SeparableClosure K
  let : MulAction Γ d.Vertex := {
    smul := d.star
    one_smul := d.star_one
    mul_smul := d.star_mul }
  have hstab : d.starVertexStabilizer a = MulAction.stabilizer Γ a := rfl
  have horbit : MulAction.orbit Γ a = {b : d.Vertex | e b ≠ 1} := by
    ext b
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨σ, rfl⟩ hb
      change e (d.star σ a) = 1 at hb
      let c : d.Vertex := e.symm 1
      have hc : d.star σ c = c :=
        d.star_fixes_center_of_D (by decide) e hD σ c (by simp [c])
      have heq : d.star σ a = d.star σ c := by
        apply e.injective
        simpa only [hc, c, Equiv.apply_symm_apply] using hb
      exact ha (by simpa [c] using congrArg e ((d.starPermutation σ).injective heq))
    · intro hb
      exact d.star_transitive_on_D4_leaves_of_no_fixed_leaf e hD hno a b ha hb
  rw [hstab, MulAction.index_stabilizer, horbit]
  change (e ⁻¹' ({1} : Set (Fin 4))ᶜ).ncard = 3
  rw [Set.ncard_preimage_of_injective_subset_range e.injective
    (by rw [e.range_eq_univ]; exact Set.subset_univ _)]
  rw [Set.ncard_compl]
  simp

/-- Every leaf in the no-fixed-leaf D4 case has a separable cubic field of
definition inside the original separable closure. -/
theorem finrank_starVertexField_of_D4_no_fixed_leaf
    (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hno : ¬ ∃ a : d.Vertex, e a ≠ 1 ∧
      ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a)
    (a : d.Vertex) (ha : e a ≠ 1) :
    Module.finrank K (d.starVertexField a) = 3 := by
  rw [d.finrank_starVertexField]
  exact d.starVertexStabilizer_index_of_D4_no_fixed_leaf e hD hno a ha

/-- The cubic field is an actual finite-dimensional separable subextension.
Its pointwise fixers are exactly the absolute Galois elements fixing the
specified original leaf. No Galois or cyclic hypothesis is imposed on it. -/
theorem exists_cubic_leafField_of_D4_no_fixed_leaf
    (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hno : ¬ ∃ a : d.Vertex, e a ≠ 1 ∧
      ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a)
    (a : d.Vertex) (ha : e a ≠ 1) :
    ∃ E : IntermediateField K (SeparableClosure K),
      FiniteDimensional K E ∧ Algebra.IsSeparable K E ∧
      Module.finrank K E = 3 ∧
      ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K,
        (∀ x ∈ E, σ x = x) ↔ d.star σ a = a := by
  have hdim := d.finrank_starVertexField_of_D4_no_fixed_leaf e hD hno a ha
  exact ⟨d.starVertexField a, Module.finite_of_finrank_pos (by omega),
    d.isSeparable_starVertexField a, hdim, d.fixes_starVertexField_iff a⟩

end Langlands.GroupScheme.TitsIndexData

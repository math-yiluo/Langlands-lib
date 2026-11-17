import Langlands.GroupScheme.Reductive.TitsCartanComponentTransport
import Langlands.GroupScheme.Reductive.StarActionContinuityProof
import Mathlib.FieldTheory.Galois.Infinite

/-! # The finite separable field of a full Cartan-component stabilizer -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- A finite intermediate field has pointwise fixer contained in the entire
Cartan-component stabilizer. -/
theorem exists_finiteField_fixingSubgroup_le_cartanComponentStabilizer (a : d.Vertex) :
    ∃ E : IntermediateField k (SeparableClosure k), FiniteDimensional k E ∧
      E.fixingSubgroup ≤ d.cartanComponentStabilizer a := by
  obtain ⟨E, hE, hfix⟩ := starActionContinuity k (SeparableClosure k) G d.pinning
  refine ⟨E, hE, fun σ hσ => ?_⟩
  have hstar := (hfix σ ((mem_fixingSubgroup_iff _).mp hσ)).2
  apply (d.mem_cartanComponentStabilizer a σ).mpr
  have ha : d.star σ a = a := by
    apply Subtype.ext
    change (d.pinning.starAction σ).val.indexEquiv a.val = a.val
    rw [hstar]
    rfl
  rw [ha]
  exact d.cartanConnected_refl a

/-- The stabilizer of an actual Cartan component is open in the Krull topology. -/
theorem isOpen_cartanComponentStabilizer (a : d.Vertex) :
    IsOpen (d.cartanComponentStabilizer a : Set (SeparableClosure k ≃ₐ[k] SeparableClosure k)) := by
  obtain ⟨E, hE, hle⟩ := d.exists_finiteField_fixingSubgroup_le_cartanComponentStabilizer a
  let : FiniteDimensional k E := hE
  exact Subgroup.isOpen_mono hle (IntermediateField.fixingSubgroup_isOpen E)

/-- The stabilizer is closed, since it is an open subgroup of a topological group. -/
theorem isClosed_cartanComponentStabilizer (a : d.Vertex) :
    IsClosed (d.cartanComponentStabilizer a : Set (SeparableClosure k ≃ₐ[k] SeparableClosure k)) :=
  (d.cartanComponentStabilizer a).isClosed_of_isOpen (d.isOpen_cartanComponentStabilizer a)

/-- The actual intermediate field fixed by the full Cartan-component stabilizer. -/
def cartanComponentField (a : d.Vertex) : IntermediateField k (SeparableClosure k) :=
  IntermediateField.fixedField (d.cartanComponentStabilizer a)

/-- Infinite Galois correspondence recovers the entire component stabilizer. -/
theorem fixingSubgroup_cartanComponentField (a : d.Vertex) :
    (d.cartanComponentField a).fixingSubgroup = d.cartanComponentStabilizer a :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨d.cartanComponentStabilizer a, d.isClosed_cartanComponentStabilizer a⟩

instance finiteDimensional_cartanComponentField (a : d.Vertex) :
    FiniteDimensional k (d.cartanComponentField a) := by
  apply (InfiniteGalois.isOpen_iff_finite (d.cartanComponentField a)).mp
  rw [d.fixingSubgroup_cartanComponentField a]
  exact d.isOpen_cartanComponentStabilizer a

instance isSeparable_cartanComponentField (a : d.Vertex) :
    Algebra.IsSeparable k (d.cartanComponentField a) := inferInstance

local instance componentClosureAlgebra (a : d.Vertex) :
    Algebra (d.cartanComponentField a) (SeparableClosure (d.cartanComponentField a)) :=
  (separableClosure (d.cartanComponentField a) (AlgebraicClosure (d.cartanComponentField a))).algebra

/-- The two separable closures over the actual stabilizer field are equivalent. -/
def cartanComponentSeparableClosureEquiv (a : d.Vertex) :
    SeparableClosure (d.cartanComponentField a) ≃ₐ[d.cartanComponentField a] SeparableClosure k := by
  letI : Algebra.IsSeparable (d.cartanComponentField a) (SeparableClosure k) :=
    Algebra.isSeparable_tower_top_of_isSeparable k (d.cartanComponentField a) (SeparableClosure k)
  letI : IsSepClosure (d.cartanComponentField a) (SeparableClosure k) :=
    ⟨inferInstance, inferInstance⟩
  exact IsSepClosure.equiv _ _ _

/-- The absolute Galois group of the component field is the full stabilizer,
through transport of separable closures and the exact infinite Galois correspondence. -/
def cartanComponentAbsoluteGaloisEquiv (a : d.Vertex) :
    (SeparableClosure (d.cartanComponentField a) ≃ₐ[d.cartanComponentField a]
      SeparableClosure (d.cartanComponentField a)) ≃* d.cartanComponentStabilizer a :=
  (AlgEquiv.autCongr (d.cartanComponentSeparableClosureEquiv a)).trans
    ((IntermediateField.fixingSubgroupEquiv (d.cartanComponentField a)).symm.trans
      (MulEquiv.subgroupCongr (d.fixingSubgroup_cartanComponentField a)))

/-- The full simultaneous action of the component field's absolute Galois group
on the original actual Cartan component. -/
def cartanComponentAbsoluteStarRepresentation (a : d.Vertex) :
    (SeparableClosure (d.cartanComponentField a) ≃ₐ[d.cartanComponentField a]
      SeparableClosure (d.cartanComponentField a)) →* Equiv.Perm (d.CartanComponent a) :=
  (d.cartanComponentStarRepresentation a).comp
    (d.cartanComponentAbsoluteGaloisEquiv a).toMonoidHom

@[simp] theorem cartanComponentAbsoluteStarRepresentation_apply_val (a : d.Vertex)
    (τ : SeparableClosure (d.cartanComponentField a) ≃ₐ[d.cartanComponentField a]
      SeparableClosure (d.cartanComponentField a)) (b : d.CartanComponent a) :
    (d.cartanComponentAbsoluteStarRepresentation a τ b).val =
      d.star (d.cartanComponentAbsoluteGaloisEquiv a τ).val b.val := rfl

/-- Every stabilizing absolute Galois element is lifted by a single element over
the component field, with one lift acting on all component vertices. -/
theorem cartanComponentAbsoluteStarRepresentation_stabilizer_lift (a : d.Vertex)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (hσ : d.CartanConnected a (d.star σ a)) :
    ∃ τ : SeparableClosure (d.cartanComponentField a) ≃ₐ[d.cartanComponentField a]
      SeparableClosure (d.cartanComponentField a),
      ∀ b : d.CartanComponent a,
        (d.cartanComponentAbsoluteStarRepresentation a τ b).val = d.star σ b.val := by
  let s : d.cartanComponentStabilizer a :=
    ⟨σ, (d.mem_cartanComponentStabilizer a σ).mpr hσ⟩
  refine ⟨(d.cartanComponentAbsoluteGaloisEquiv a).symm s, fun b => ?_⟩
  rw [d.cartanComponentAbsoluteStarRepresentation_apply_val,
    (d.cartanComponentAbsoluteGaloisEquiv a).apply_symm_apply]

/-- Every element over the component field has one stabilizing absolute lift
acting simultaneously on all vertices of the original component. -/
theorem cartanComponentAbsoluteStarRepresentation_star_lift (a : d.Vertex)
    (τ : SeparableClosure (d.cartanComponentField a) ≃ₐ[d.cartanComponentField a]
      SeparableClosure (d.cartanComponentField a)) :
    ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
      d.CartanConnected a (d.star σ a) ∧
      ∀ b : d.CartanComponent a,
        (d.cartanComponentAbsoluteStarRepresentation a τ b).val = d.star σ b.val := by
  refine ⟨(d.cartanComponentAbsoluteGaloisEquiv a τ).val, ?_, fun _ => rfl⟩
  exact (d.mem_cartanComponentStabilizer a _).mp
    (d.cartanComponentAbsoluteGaloisEquiv a τ).property

end Langlands.GroupScheme.TitsIndexData

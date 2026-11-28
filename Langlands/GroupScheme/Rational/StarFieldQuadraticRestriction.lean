import Langlands.GroupScheme.SimplyConnected.TypeD4CubicLeafField
import Mathlib.FieldTheory.LinearDisjoint

/-! # Restriction of the star kernel to a disjoint quadratic field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

/-- The field defined by the full star action is finite. -/
theorem finiteDimensional_starField : FiniteDimensional k d.starField := by
  apply (InfiniteGalois.isOpen_iff_finite d.starField).mp
  rw [d.starField_fixingSubgroup]
  exact d.starKernel_isOpen

/-- The field defined by the full star action is Galois over the base. -/
theorem isGalois_starField : IsGalois k d.starField := by
  apply (InfiniteGalois.normal_iff_isGalois d.starField).mp
  rw [d.starField_fixingSubgroup]
  let f : (SeparableClosure k ≃ₐ[k] SeparableClosure k) →* Equiv.Perm d.Vertex :=
    { toFun := d.starPermutation
      map_one' := Equiv.ext (fun a => d.star_one a)
      map_mul' := fun σ τ => Equiv.ext (fun a => d.star_mul σ τ a) }
  have h : d.starKernel = f.ker := by
    ext σ
    rw [d.mem_starKernel_iff, MonoidHom.mem_ker]
    constructor
    · intro hfix
      apply Equiv.ext
      exact hfix
    · intro he a
      exact congrArg (fun g : Equiv.Perm d.Vertex => g a) he
  rw [h]
  infer_instance

/-- A nontrivial Galois subextension disjoint from the star field admits an
absolute automorphism with trivial star action but nontrivial restriction. -/
theorem exists_star_trivial_restrictNormal_ne_one
    (Q : IntermediateField k (SeparableClosure k)) [IsGalois k Q]
    (hQ : Q ≠ ⊥) (hdisj : Q.LinearDisjoint d.starField) :
    ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
      (∀ a, d.star σ a = a) ∧ σ.restrictNormal Q ≠ 1 := by
  classical
  by_contra! h
  have hle : Q ≤ d.starField := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup d.starField]
    intro x hx
    apply (IntermediateField.mem_fixedField_iff _ _).mpr
    intro σ hσ
    have hfix := (d.fixes_starField_iff σ).mp ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ)
    exact (AlgEquiv.restrictNormal_eq_one_iff Q σ).mp (h σ hfix) x hx
  apply hQ
  rw [← hdisj.inf_eq_bot, inf_eq_left.mpr hle]

end Langlands.GroupScheme.TitsIndexData

import Langlands.Algebra.GroupLikeReconstruction
import Mathlib.RingTheory.Flat.Basic

/-! # Coalgebras embedded in monomial coalgebras -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.AddMonoidAlgebra

variable {k : Type u} [Field k] {M : Type v}

/-- Contract the second tensor factor against a single monomial coefficient. -/
def coefficientContraction (m : M) :
    _root_.AddMonoidAlgebra k M ⊗[k] _root_.AddMonoidAlgebra k M →ₗ[k]
      _root_.AddMonoidAlgebra k M :=
  (TensorProduct.rid k _).toLinearMap ∘ₗ
    TensorProduct.map (LinearMap.id) ((Finsupp.lapply m).comp
      (_root_.AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap)

@[simp]
theorem coefficientContraction_tmul (m : M) (x y : _root_.AddMonoidAlgebra k M) :
    coefficientContraction m (x ⊗ₜ[k] y) = y.coeff m • x := by
  simp [coefficientContraction]

/-- Contracting the diagonal comultiplication selects one monomial. -/
theorem coefficientContraction_comul (m : M) (x : _root_.AddMonoidAlgebra k M) :
    coefficientContraction m (Coalgebra.comul (R := k) x) =
      _root_.AddMonoidAlgebra.single m (x.coeff m) := by
  classical
  suffices (coefficientContraction (k := k) m).comp Coalgebra.comul =
      (_root_.AddMonoidAlgebra.lsingle m).comp ((Finsupp.lapply m).comp
        (_root_.AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap) by
    exact LinearMap.congr_fun this x
  apply _root_.AddMonoidAlgebra.lhom_ext'
  intro n
  ext r
  by_cases h : n = m
  · subst n
    simp [coefficientContraction]
  · simp [coefficientContraction, h]

variable {C : Type w} [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- A coalgebra map has each nonzero monomial component in its linear range. -/
theorem single_mem_range (f : C →ₗc[k] _root_.AddMonoidAlgebra k M)
    (a : C) (m : M) (hm : (f a).coeff m ≠ 0) :
    _root_.AddMonoidAlgebra.single m 1 ∈ LinearMap.range f.toLinearMap := by
  have h : _root_.AddMonoidAlgebra.single m ((f a).coeff m) ∈
      LinearMap.range f.toLinearMap := by
    rw [← coefficientContraction_comul, ← CoalgHomClass.map_comp_comul_apply f a]
    induction Coalgebra.comul (R := k) a using TensorProduct.inductionOn with
    | tmul x y =>
        simp only [TensorProduct.map_tmul, coefficientContraction_tmul]
        exact ⟨(f y).coeff m • x, map_smul f _ _⟩
    | add x y hx hy =>
        simpa only [map_add] using (LinearMap.range f.toLinearMap).add_mem hx hy
  have hs := (LinearMap.range f.toLinearMap).smul_mem ((f a).coeff m)⁻¹ h
  simpa [smul_smul, _root_.AddMonoidAlgebra.smul_single, hm] using hs

/-- An injective coalgebra map over a field reflects group-like elements. -/
theorem isGroupLikeElem_of_injective (f : C →ₗc[k] _root_.AddMonoidAlgebra k M)
    (hf : Function.Injective f) {a : C} (ha : IsGroupLikeElem k (f a)) :
    IsGroupLikeElem k a := by
  constructor
  · rw [← CoalgHomClass.counit_comp_apply f a]
    exact ha.counit_eq_one
  · apply TensorProduct.map_injective_of_flat_flat f.toLinearMap f.toLinearMap hf hf
    calc
      _ = Coalgebra.comul (R := k) (f a) := LinearMap.congr_fun f.map_comp_comul a
      _ = f a ⊗ₜ[k] f a := ha.comul_eq_tmul_self
      _ = _ := (TensorProduct.map_tmul _ _ _ _).symm

/-- Every coalgebra embedded in a monomial coalgebra over a field is spanned by
its group-like elements. -/
theorem span_isGroupLikeElem_of_injective
    (f : C →ₗc[k] _root_.AddMonoidAlgebra k M) (hf : Function.Injective f) :
    Submodule.span k {a : C | IsGroupLikeElem k a} = ⊤ := by
  classical
  apply top_unique
  intro a _
  let S := Submodule.span k {a : C | IsGroupLikeElem k a}
  suffices h : f a ∈ S.map f.toLinearMap by
    obtain ⟨b, hb, hba⟩ := h
    exact hf hba ▸ hb
  rw [← (f a).sum_coeff_single, Finsupp.sum]
  apply Submodule.sum_mem
  intro m hm
  have hnonzero := Finsupp.mem_support_iff.mp hm
  obtain ⟨b, hb⟩ := single_mem_range f a m hnonzero
  change f b = _ at hb
  have hgroup : IsGroupLikeElem k b := isGroupLikeElem_of_injective f hf (by
    rw [hb]
    exact _root_.AddMonoidAlgebra.isGroupLikeElem_single_one m)
  have hmem : _root_.AddMonoidAlgebra.single m 1 ∈ S.map f.toLinearMap :=
    ⟨b, Submodule.subset_span hgroup, hb⟩
  simpa using (S.map f.toLinearMap).smul_mem ((f a).coeff m) hmem

end Langlands.AddMonoidAlgebra

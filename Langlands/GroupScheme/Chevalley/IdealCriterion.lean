import Langlands.GroupScheme.Chevalley.RegularSubspace
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The ideal criterion for the Chevalley subspace stabilizer -/

noncomputable section

open TensorProduct Coalgebra Module

namespace Langlands.GroupScheme.Chevalley

section Linear

variable {K : Type*} [Field K]
  {B : Type*} [AddCommGroup B] [Module K B]
  {C : Type*} [AddCommGroup C] [Module K C]
  {A : Type*} [AddCommGroup A] [Module K A]

/-- The subspace of `V` consisting of functions killed by a linear restriction map. -/
abbrev idealSubspace (V : Submodule K B) (r : B →ₗ[K] C) : Submodule K B :=
  V ⊓ LinearMap.ker r

/-- Scalar extension commutes with intersecting a subspace with a linear kernel. -/
theorem mem_tensorSubspace_inf_ker (V : Submodule K B) (r : B →ₗ[K] C)
    (t : B ⊗[K] A) :
    t ∈ tensorSubspace (V ⊓ LinearMap.ker r) A ↔
      t ∈ tensorSubspace V A ∧ r.rTensor A t = 0 := by
  let W := V ⊓ LinearMap.ker r
  let s := r ∘ₗ V.subtype
  let j : LinearMap.ker s →ₗ[K] W :=
    { toFun := fun w => ⟨w.1.1, w.1.2, w.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let k : W →ₗ[K] V :=
    { toFun := fun w => ⟨w.1, w.2.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨⟨k.rTensor A u, ?_⟩, ?_⟩
    · have hk : V.subtype ∘ₗ k = W.subtype := rfl
      rw [← LinearMap.rTensor_comp_apply, hk]
    · have hz : r ∘ₗ W.subtype = 0 := by
        ext w
        exact w.2.2
      rw [← LinearMap.rTensor_comp_apply, hz, LinearMap.rTensor_zero, LinearMap.zero_apply]
  · rintro ⟨⟨u, hu⟩, ht⟩
    have hs : s.rTensor A u = 0 := by
      rw [LinearMap.rTensor_comp_apply, hu]
      exact ht
    obtain ⟨z, hz⟩ := (Module.Flat.rTensor_exact A
      (LinearMap.exact_subtype_ker_map s) u).mp hs
    refine ⟨j.rTensor A z, ?_⟩
    have hj : W.subtype ∘ₗ j = V.subtype ∘ₗ (LinearMap.ker s).subtype := rfl
    rw [← LinearMap.rTensor_comp_apply, hj, LinearMap.rTensor_comp_apply, hz, hu]

end Linear

section Bialgebra

variable {K : Type*} [Field K]
  {B : Type*} [CommRing B] [Bialgebra K B]
  {C : Type*} [CommRing C] [Bialgebra K C]
  (r : B →ₐc[K] C)
  {A : Type*} [CommRing A] [Algebra K A]

/-- Applying the counit to the first factor of a translated function recovers its
value at the translating point. -/
theorem counit_translate (f : B →ₐ[K] A) (b : B) :
    TensorProduct.lid K A
      ((counit (R := K) (A := C)).rTensor A
        (r.toLinearMap.rTensor A (translate f.toLinearMap b))) = f b := by
  have ht : ∀ t : B ⊗[K] B,
      TensorProduct.lid K A
        ((counit (R := K) (A := C)).rTensor A
          (r.toLinearMap.rTensor A (f.toLinearMap.lTensor B t))) =
      f (TensorProduct.lid K B ((counit (R := K)).rTensor B t)) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp [CoalgHomClass.counit_comp_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  change _ = f b
  rw [translate, LinearMap.comp_apply, ht]
  rw [← AffineLinearEmbedding.leftAct_apply, AffineLinearEmbedding.leftAct_counit]

/-- A function vanishing on the subgroup still vanishes there after translation
by any point of the subgroup. -/
theorem quotient_translate_eq_zero (ψ : C →ₐ[K] A) {b : B} (hb : r b = 0) :
    r.toLinearMap.rTensor A (translate (ψ.comp r.toAlgHom).toLinearMap b) = 0 := by
  have ht : r.toLinearMap.rTensor A ∘ₗ
        (ψ.comp r.toAlgHom).toLinearMap.lTensor B =
      ψ.toLinearMap.lTensor C ∘ₗ TensorProduct.map r.toLinearMap r.toLinearMap := by
    ext x y
    rfl
  change (r.toLinearMap.rTensor A ∘ₗ
    (ψ.comp r.toAlgHom).toLinearMap.lTensor B) (comul b) = 0
  have hc : TensorProduct.map r.toLinearMap r.toLinearMap (comul b) = comul (r b) :=
    LinearMap.congr_fun r.map_comp_comul b
  rw [ht, LinearMap.comp_apply, hc, hb, map_zero, map_zero]

/-- For a regular subspace containing generators of the subgroup ideal, its intersection
with that ideal is stabilized precisely by the algebra points of the subgroup. -/
theorem stabilizes_iff_factors
    (hr : Function.Surjective r)
    (S : Finset B) (hS : Ideal.span (S : Set B) = RingHom.ker r.toAlgHom.toRingHom)
    (V : Submodule K B) (hSV : (S : Set B) ⊆ V)
    (hV : ∀ (f : Module.Dual K B) (v : B), v ∈ V →
      AffineLinearEmbedding.rightAct f v ∈ V)
    (f : B →ₐ[K] A) :
    (∀ w : B, w ∈ idealSubspace V r.toLinearMap →
      translate f.toLinearMap w ∈
        tensorSubspace (idealSubspace V r.toLinearMap) A) ↔
      ∃ ψ : C →ₐ[K] A, ψ.comp r.toAlgHom = f := by
  constructor
  · intro h
    have hker : RingHom.ker r.toAlgHom.toRingHom ≤ RingHom.ker f.toRingHom := by
      rw [← hS, Ideal.span_le]
      intro b hb
      have hmem : b ∈ RingHom.ker r.toAlgHom.toRingHom :=
        hS ▸ (Ideal.subset_span hb : b ∈ Ideal.span (S : Set B))
      have hrb : r b = 0 := hmem
      have hz := ((mem_tensorSubspace_inf_ker V r.toLinearMap _).mp
        (h b ⟨hSV hb, hrb⟩)).2
      have he := counit_translate r f b
      rw [hz, map_zero, map_zero] at he
      exact he.symm
    exact ⟨AlgHom.liftOfSurjective r.toAlgHom hr f hker,
      AlgHom.liftOfSurjective_comp r.toAlgHom hr f hker⟩
  · rintro ⟨ψ, rfl⟩ b hb
    apply (mem_tensorSubspace_inf_ker V r.toLinearMap _).mpr
    exact ⟨translate_mem_tensorSubspace V hV _ hb.1,
      quotient_translate_eq_zero r ψ hb.2⟩

/-- The regular-span construction supplies the finite-dimensional subspace in the
stabilizer criterion for every finitely generated subgroup ideal. -/
theorem exists_finite_subspace_stabilizer
    (hr : Function.Surjective r)
    (hfg : (RingHom.ker r.toAlgHom.toRingHom).FG) :
    ∃ V : Submodule K B, Module.Finite K V ∧
      (∀ (f : Module.Dual K B) (v : B), v ∈ V →
        AffineLinearEmbedding.rightAct f v ∈ V) ∧
      ∀ (A : Type*) [CommRing A] [Algebra K A] (f : B →ₐ[K] A),
        (∀ w : B, w ∈ idealSubspace V r.toLinearMap →
          translate f.toLinearMap w ∈
            tensorSubspace (idealSubspace V r.toLinearMap) A) ↔
        ∃ ψ : C →ₐ[K] A, ψ.comp r.toAlgHom = f := by
  obtain ⟨S, hS⟩ := hfg
  refine ⟨regularSpan (K := K) S, inferInstance, ?_, ?_⟩
  · exact fun f v hv => rightAct_mem_regularSpan S f hv
  · intro A _ _ f
    exact stabilizes_iff_factors r hr S hS _ (subset_regularSpan S)
      (fun φ v hv => rightAct_mem_regularSpan S φ hv) f

end Bialgebra

end Langlands.GroupScheme.Chevalley

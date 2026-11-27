import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.LinearAlgebra.Span.Basic

/-! # Transport of eigenvectors of inner derivations -/

noncomputable section

open TensorProduct

namespace Langlands.Algebra.LieEigenvectorTransport

section Equiv

variable {R L₁ L₂ : Type*} [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂]
  [LieAlgebra R L₂]

/-- An isomorphism of Lie algebras carries eigenvectors of `ad h` to eigenvectors of the image
of `h`, with the same eigenvalues. -/
theorem lie_eq_smul_iff (e : L₁ ≃ₗ⁅R⁆ L₂) (h X : L₁) (c : R) :
    ⁅e h, e X⁆ = c • e X ↔ ⁅h, X⁆ = c • X := by
  have h1 : e ⁅h, X⁆ = ⁅e h, e X⁆ := LieEquiv.map_lie e h X
  have h2 : e (c • X) = c • e X := e.toLinearEquiv.map_smul c X
  rw [← h1, ← h2]
  exact ⟨fun h => e.injective h, fun h => congrArg e h⟩

/-- The eigenvectors of the image of `h` under an isomorphism of Lie algebras, for eigenvalues
in a given family, are the images of the eigenvectors of `h`. -/
theorem eigenSet_eq_image (e : L₁ ≃ₗ⁅R⁆ L₂) (h : L₁) {ι : Type*} (μ : ι → R) :
    {Y : L₂ | ∃ i, ⁅e h, Y⁆ = μ i • Y} = e '' {X : L₁ | ∃ i, ⁅h, X⁆ = μ i • X} := by
  ext Y
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨e.symm Y, ⟨i, ?_⟩, e.apply_symm_apply Y⟩
    rw [← lie_eq_smul_iff e, e.apply_symm_apply]
    exact hi
  · rintro ⟨X, ⟨i, hi⟩, rfl⟩
    exact ⟨i, (lie_eq_smul_iff e h X _).mpr hi⟩

/-- The span of the eigenvectors of the image of `h` under an isomorphism of Lie algebras is the
image of the span of the eigenvectors of `h`. -/
theorem span_eigenSet_eq_map (e : L₁ ≃ₗ⁅R⁆ L₂) (h : L₁) {ι : Type*} (μ : ι → R) :
    Submodule.span R {Y : L₂ | ∃ i, ⁅e h, Y⁆ = μ i • Y} =
      (Submodule.span R {X : L₁ | ∃ i, ⁅h, X⁆ = μ i • X}).map
        (e.toLinearEquiv : L₁ →ₗ[R] L₂) := by
  rw [Submodule.map_span, eigenSet_eq_image e h μ]
  rfl

end Equiv

section BaseChange

variable {R A L : Type*} [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]

/-- The inner derivation of `1 ⊗ h` on a scalar extension is the scalar extension of the inner
derivation of `h`. -/
theorem one_tmul_lie (h : L) (X : A ⊗[R] L) :
    ⁅(1 : A) ⊗ₜ[R] h, X⁆ = (LieAlgebra.ad R L h).baseChange A X := by
  induction X using TensorProduct.inductionOn with
  | tmul z m =>
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul, LinearMap.baseChange_tmul,
      LieAlgebra.ad_apply]
  | add a b ha hb => rw [lie_add, ha, hb, map_add]

end BaseChange

section RestrictScalars

variable {k F M : Type*} [Field k] [Field F] [Algebra k F] [AddCommGroup M] [Module F M]

/-- For a set of vectors stable under the scalars of an extension field, the span over the
smaller field (after restriction of scalars) consists of the vectors of the span over the larger
field. -/
theorem mem_span_restrictScalars_iff {S : Set M} (hS : ∀ (c : F), ∀ x ∈ S, c • x ∈ S)
    (y : RestrictScalars k F M) :
    y ∈ Submodule.span k ((RestrictScalars.addEquiv k F M).symm '' S) ↔
      RestrictScalars.addEquiv k F M y ∈ Submodule.span F S := by
  set e := RestrictScalars.addEquiv k F M
  set N := Submodule.span k (e.symm '' S)
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      rw [AddEquiv.apply_symm_apply]
      exact Submodule.subset_span hx
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul q a _ ha =>
      rw [RestrictScalars.addEquiv_map_smul]
      exact Submodule.smul_mem _ _ ha
  · have hstable : ∀ (c : F), ∀ y ∈ N, e.symm (c • e y) ∈ N := by
      intro c y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        rw [AddEquiv.apply_symm_apply]
        exact Submodule.subset_span ⟨c • x, hS c x hx, rfl⟩
      | zero => rw [map_zero, smul_zero, map_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb =>
        rw [map_add, smul_add, map_add]
        exact Submodule.add_mem _ ha hb
      | smul q a _ ha =>
        rw [RestrictScalars.addEquiv_map_smul, smul_comm,
          RestrictScalars.addEquiv_symm_map_algebraMap_smul]
        exact Submodule.smul_mem _ _ ha
    intro hy
    have h : ∀ x ∈ Submodule.span F S, e.symm x ∈ N := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
        have := hstable c _ ha
        rwa [AddEquiv.apply_symm_apply] at this
    have := h _ hy
    rwa [AddEquiv.symm_apply_apply] at this

/-- For a set of vectors stable under the scalars of an extension field and spanning over it,
the set also spans over the smaller field after restriction of scalars. -/
theorem span_restrictScalars_eq_top {S : Set M} (hS : ∀ (c : F), ∀ x ∈ S, c • x ∈ S)
    (htop : Submodule.span F S = ⊤) :
    Submodule.span k ((RestrictScalars.addEquiv k F M).symm '' S) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  rw [mem_span_restrictScalars_iff hS, htop]
  exact Submodule.mem_top

end RestrictScalars

end Langlands.Algebra.LieEigenvectorTransport

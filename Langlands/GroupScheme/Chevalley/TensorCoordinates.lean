import Langlands.GroupScheme.Chevalley.SubspaceMatrix
import Langlands.GroupScheme.Chevalley.AdaptedBasis

/-! # Tensor subspaces in adapted matrix coordinates -/

noncomputable section

open Module TensorProduct
open scoped Matrix

namespace Langlands.GroupScheme.Chevalley

variable {K : Type*} [Field K] {B : Type*} [AddCommGroup B] [Module K B]
  (V : Submodule K B) {N d : ℕ} (b : Basis (Fin N) K V) (s : Fin d ↪ Fin N)
  {A : Type*} [AddCommGroup A] [Module K A]

/-- A coordinate vector expressed in the scalar extension of the actual ambient subspace. -/
def basisTensorVector (a : Fin N → A) : B ⊗[K] A :=
  ∑ i, (b i : B) ⊗ₜ[K] a i

/-- Contraction by an extended coordinate recovers the corresponding coefficient. -/
theorem contract_basisTensorVector (a : Fin N → A) (i : Fin N) :
    TensorProduct.lid K A ((extendedCoord V b i).rTensor A (basisTensorVector V b a)) = a i := by
  simp [basisTensorVector, Matrix.one_apply, ite_smul]

/-- Membership in the scalar extension of an adapted subspace is vanishing of the
coordinates outside the selected indices. -/
theorem basisTensorVector_mem_iff
    (W : Submodule K B)
    (hW : W = Submodule.span K (Set.range fun i : Fin d => (b (s i) : B)))
    (a : Fin N → A) :
    basisTensorVector V b a ∈ tensorSubspace W A ↔
      ∀ j : Fin N, j ∉ Set.range s → a j = 0 := by
  constructor
  · rintro ⟨z, hz⟩ j hj
    have hc : ∀ w : W, extendedCoord V b j (w : B) = 0 := by
      have hle : W ≤ LinearMap.ker (extendedCoord V b j) := by
        rw [hW, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        have hne : j ≠ s i := fun he => hj ⟨i, he.symm⟩
        simp [hne]
      exact fun w => hle w.2
    let c := (TensorProduct.lid K A).toLinearMap ∘ₗ (extendedCoord V b j).rTensor A
    have hzero : c ∘ₗ W.subtype.rTensor A = 0 := by
      ext w a
      simp [c, hc]
    have he := congrArg c hz
    change c ((W.subtype.rTensor A) z) = c (basisTensorVector V b a) at he
    rw [← LinearMap.comp_apply, hzero, LinearMap.zero_apply] at he
    exact (he.trans (contract_basisTensorVector V b a j)).symm
  · intro ha
    apply Submodule.sum_mem
    intro j _
    by_cases hj : j ∈ Set.range s
    · obtain ⟨i, rfl⟩ := hj
      have hw : (b (s i) : B) ∈ W := hW ▸ Submodule.subset_span ⟨i, rfl⟩
      exact ⟨(⟨(b (s i) : B), hw⟩ : W) ⊗ₜ[K] a (s i), rfl⟩
    · simp [ha j hj]

section Coalgebra

variable [Coalgebra K B]
  (hV : ∀ (f : Module.Dual K B) (v : B), v ∈ V →
    AffineLinearEmbedding.rightAct f v ∈ V)
  (W : Submodule K B)
  (hW : W = Submodule.span K (Set.range fun i : Fin d => (b (s i) : B)))
  (f : B →ₗ[K] A)

include hV hW in
/-- Subspace preservation by coefficient-valued translation is exactly the vanishing
of the outside entries in the selected columns of its matrix. -/
theorem stabilizes_iff_matrix_columns :
    (∀ w : B, w ∈ W → translate f w ∈ tensorSubspace W A) ↔
      ∀ (i : Fin d) (j : Fin N), j ∉ Set.range s →
        f (subspaceMatrix V b j (s i)) = 0 := by
  have hcol (i : Fin d) :
      translate f (b (s i) : B) ∈ tensorSubspace W A ↔
        ∀ j : Fin N, j ∉ Set.range s → f (subspaceMatrix V b j (s i)) = 0 := by
    rw [translate_basis V b hV]
    exact basisTensorVector_mem_iff V b s W hW _
  constructor
  · intro h i
    apply (hcol i).mp
    apply h
    rw [hW]
    exact Submodule.subset_span ⟨i, rfl⟩
  · intro h w hw
    have hle : W ≤ (tensorSubspace W A).comap (translate f) := by
      conv_lhs => rw [hW]
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (hcol i).mpr (h i)
    exact hle hw

end Coalgebra

section Matrix

variable {R : Type*} [CommRing R]

/-- A matrix preserves a coordinate span exactly when its selected columns have no
entries outside that span. -/
theorem matrix_preserves_coordinateSpan_iff (m : Matrix (Fin N) (Fin N) R) :
    (∀ v : Fin N → R, v ∈ coordinateSpan (Pi.basisFun R (Fin N)) s →
      m *ᵥ v ∈ coordinateSpan (Pi.basisFun R (Fin N)) s) ↔
      ∀ (i : Fin d) (j : Fin N), j ∉ Set.range s → m j (s i) = 0 := by
  constructor
  · intro h i j hj
    have hv := h ((Pi.basisFun R (Fin N)) (s i)) (Submodule.subset_span ⟨i, rfl⟩)
    have he := (mem_coordinateSpan_iff (Pi.basisFun R (Fin N)) s _).mp hv j hj
    simpa [Basis.coord_apply, Pi.basisFun_apply, Matrix.mulVec_single] using he
  · intro h v hv
    have hle : coordinateSpan (Pi.basisFun R (Fin N)) s ≤
        (coordinateSpan (Pi.basisFun R (Fin N)) s).comap (Matrix.mulVecLin m) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply (mem_coordinateSpan_iff (Pi.basisFun R (Fin N)) s _).mpr
      intro j hj
      simpa [Basis.coord_apply, Pi.basisFun_apply, Matrix.mulVec_single] using h i j hj
    exact hle hv

end Matrix

/-- The tensor-image stabilizer condition in an adapted basis is actual preservation
of the corresponding coordinate subspace by the evaluated matrix. -/
theorem stabilizes_iff_matrix_preserves [Coalgebra K B]
    (hV : ∀ (f : Module.Dual K B) (v : B), v ∈ V →
      AffineLinearEmbedding.rightAct f v ∈ V)
    (W : Submodule K B)
    (hW : W = Submodule.span K (Set.range fun i : Fin d => (b (s i) : B)))
    {R : Type*} [CommRing R] [Module K R] (f : B →ₗ[K] R) :
    (∀ w : B, w ∈ W → translate f w ∈ tensorSubspace W R) ↔
      ∀ v : Fin N → R, v ∈ coordinateSpan (Pi.basisFun R (Fin N)) s →
        (subspaceMatrix V b).map f *ᵥ v ∈
          coordinateSpan (Pi.basisFun R (Fin N)) s :=
  (stabilizes_iff_matrix_columns V b s hV W hW f).trans
    (matrix_preserves_coordinateSpan_iff s ((subspaceMatrix V b).map f)).symm

end Langlands.GroupScheme.Chevalley

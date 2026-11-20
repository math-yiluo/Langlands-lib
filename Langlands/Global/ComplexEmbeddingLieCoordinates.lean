import Langlands.Automorphic.RegularAlgebraic
import Langlands.Global.ArchimedeanPlaceEnvelopingTensorRetraction
import Langlands.Representation.Archimedean.ComplexGenericLargeReduction

/-! The actual complexified Lie algebra in its complex embedding coordinates. -/

noncomputable section

open scoped Classical TensorProduct
open NumberField NumberField.InfinitePlace
open Langlands.Archimedean.ComplexGenericLarge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable (F : Type u) [Field F] [NumberField F] [IsTotallyComplex F] (n : ℕ)

local notation "CP" => {v : InfinitePlace F // IsComplex v}
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

/-- At a totally complex field, an embedding index consists of a place and a side. -/
def complexEmbeddingIndex : CP × Fin 2 ≃ EmbeddingIndex F where
  toFun p := .inr (p.1, finTwoEquiv p.2)
  invFun j := match j with
    | .inl w => (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1) w.2).elim
    | .inr (w, b) => (w, finTwoEquiv.symm b)
  left_inv := by rintro ⟨w, s⟩; simp
  right_inv := by
    rintro (w | ⟨w, b⟩)
    · exact (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1) w.2).elim
    · simp

omit [NumberField F] in
@[simp] theorem complexEmbeddingIndex_zero (w : CP) :
    complexEmbeddingIndex F (w, 0) = .inr (w, false) := rfl

omit [NumberField F] in
@[simp] theorem complexEmbeddingIndex_one (w : CP) :
    complexEmbeddingIndex F (w, 1) = .inr (w, true) := rfl

/-- The global complexification is the product of the complex matrix Lie algebras,
with the two embeddings at each place ordered as the coordinate and its conjugate. -/
def complexEmbeddingLieCoordinates : ComplexLieAlgebra F n ≃ₗ⁅ℂ⁆ (EmbeddingIndex F → CM) where
  toFun X j := let p := (complexEmbeddingIndex F).symm j
    tensorLieEquiv (complexPlaceComplexLieProjection F n p.1 X) p.2
  invFun Y := ∑ w : CP, complexPlaceComplexLieInclusion F n w
    (tensorLieEquiv.symm (fun s => Y (complexEmbeddingIndex F (w, s))))
  left_inv X := by
    simp only [Equiv.symm_apply_apply, LieEquiv.symm_apply_apply]
    let : IsEmpty {v : InfinitePlace F // IsReal v} :=
      ⟨fun w => not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1) w.2⟩
    induction X using TensorProduct.inductionOn with
    | tmul z X =>
      simp only [complexPlaceComplexLieProjection_tmul, complexPlaceComplexLieInclusion_tmul,
        ← TensorProduct.tmul_sum]
      have h := sum_placeLieInclusions F n X
      simpa only [Finset.univ_eq_empty, Finset.sum_empty, zero_add] using
        congrArg (fun Y : RealLieAlgebra F n => z ⊗ₜ[ℝ] Y) h
    | add X Y hX hY => simp only [map_add, Finset.sum_add_distrib, hX, hY]
  right_inv Y := by
    funext j
    obtain ⟨⟨w, s⟩, rfl⟩ := (complexEmbeddingIndex F).surjective j
    simp only [Equiv.symm_apply_apply, map_sum]
    rw [Finset.sum_eq_single w]
    · simp
    · intro v _ hv
      rw [complexPlaceComplexLieProjection_otherInclusion F n w v (Ne.symm hv), map_zero]
    · simp
  map_add' _ _ := by
    funext j
    simp only [map_add, Pi.add_apply]
  map_smul' _ _ := by
    funext j
    simp only [map_smul, Pi.smul_apply]
    rfl
  map_lie' := by
    intro X Y
    funext j
    simp only [LieHom.map_lie, LieEquiv.map_lie]
    rfl

@[simp] theorem complexEmbeddingLieCoordinates_apply (X : ComplexLieAlgebra F n)
    (w : CP) (s : Fin 2) :
    complexEmbeddingLieCoordinates F n X (complexEmbeddingIndex F (w, s)) =
      tensorLieEquiv (complexPlaceComplexLieProjection F n w X) s := by
  change tensorLieEquiv (complexPlaceComplexLieProjection F n
    ((complexEmbeddingIndex F).symm (complexEmbeddingIndex F (w, s))).1 X)
    ((complexEmbeddingIndex F).symm (complexEmbeddingIndex F (w, s))).2 = _
  rw [Equiv.symm_apply_apply]

/-- The real generator's matrix entries in the split agree with the weight convention. -/
theorem complexEmbeddingLieCoordinates_complexify (X : ArchimedeanMatrix F n)
    (j : EmbeddingIndex F) (p q : Fin n) :
    complexEmbeddingLieCoordinates F n (complexify F n ((realLieAlgebraToMatrix F n).symm X))
      j p q = embeddingComponent F j (X p q) := by
  obtain ⟨⟨w, s⟩, rfl⟩ := (complexEmbeddingIndex F).surjective j
  rw [complexEmbeddingLieCoordinates_apply, complexify_apply,
    complexPlaceComplexLieProjection_tmul]
  change tensorEquiv ((1 : ℂ) ⊗ₜ[ℝ]
    complexPlaceLieProjection F n w ((realLieAlgebraToMatrix F n).symm X)) s p q = _
  rw [tensorEquiv_tmul, one_smul]
  fin_cases s <;> rfl

end Langlands.Global.ArchimedeanGL

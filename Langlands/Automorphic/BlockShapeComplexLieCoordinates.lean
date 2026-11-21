import Langlands.Automorphic.BlockShapeLeviSliceDifferential
import Langlands.Global.ArchimedeanComplexLieCoordinates

/-! # The single-block Lie inclusion in actual archimedean coordinates -/

noncomputable section

universe u v

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open NumberField Langlands.Algebra Langlands.Archimedean Langlands.Archimedean.Kostant
  Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GeneralLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} (B : BlockShape n) (i : Fin B.length)

private def blockPad {R : Type v} [Zero R] (X : Matrix (Fin (B.size i)) (Fin (B.size i)) R) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.reindex B.indexEquiv B.indexEquiv (Matrix.blockDiagonal'
    (Pi.single i X : ∀ j, Matrix (Fin (B.size j)) (Fin (B.size j)) R))

private theorem blockPad_map {R : Type*} {S : Type*} [Zero R] [Zero S] (φ : R → S) (hφ : φ 0 = 0)
    (X : Matrix (Fin (B.size i)) (Fin (B.size i)) R) :
    (blockPad B i X).map φ = blockPad B i (X.map φ) := by
  change Matrix.reindex _ _ ((Matrix.blockDiagonal'
    (Pi.single i X : ∀ j, Matrix (Fin (B.size j)) (Fin (B.size j)) R)).map φ) = _
  rw [Matrix.blockDiagonal'_map _ _ hφ]
  refine congrArg (fun M => Matrix.reindex _ _ (Matrix.blockDiagonal' M)) ?_
  funext j
  by_cases h : j = i
  · subst j
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h]
    ext a b
    simp [hφ]

private theorem blockPad_smul (z : ℂ) (X : Matrix (Fin (B.size i)) (Fin (B.size i)) ℂ) :
    blockPad B i (z • X) = z • blockPad B i X := by
  have h : Pi.single i (z • X) = z • (Pi.single i X :
      ∀ j, Matrix (Fin (B.size j)) (Fin (B.size j)) ℂ) := by
    funext j
    by_cases hj : j = i
    · subst j
      rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.smul_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, smul_zero]
  unfold blockPad
  rw [h, Matrix.blockDiagonal'_smul]
  rfl

section MatrixProduct

variable (ι : Type u)

/-- Insert one block at every matrix place, with zero in the other blocks. -/
def blockMatrixFactorInclusion : GLProd ℂ (fun _ : ι => B.size i) →ₗ⁅ℂ⁆ GLProd ℂ (blockRanks B ι) :=
  { LinearMap.pi (fun a => (LinearMap.proj a.2).comp
      ((LinearMap.single ℂ (fun j => Matrix (Fin (B.size j)) (Fin (B.size j)) ℂ) i).comp
        (LinearMap.proj a.1))) with
    map_lie' := by
      intro X Y
      funext a
      change (Pi.single i ⁅X a.1, Y a.1⁆ : ∀ j, Matrix (Fin (B.size j)) (Fin (B.size j)) ℂ) a.2 = _
      change _ = ⁅(Pi.single i (X a.1) : ∀ j, Matrix (Fin (B.size j)) (Fin (B.size j)) ℂ) a.2,
        (Pi.single i (Y a.1) : ∀ j, Matrix (Fin (B.size j)) (Fin (B.size j)) ℂ) a.2⁆
      by_cases ha : a.2 = i
      · obtain ⟨p, j⟩ := a
        change j = i at ha
        subst j
        simp only [Pi.single_eq_same]
      · simp only [Pi.single_eq_of_ne ha, zero_lie] }

@[simp]
theorem blockMatrixFactorInclusion_apply (X : GLProd ℂ (fun _ : ι => B.size i)) (p : ι) (j : Fin B.length) :
    blockMatrixFactorInclusion B i ι X (p, j) =
      (Pi.single i (X p) : ∀ j, Matrix (Fin (B.size j)) (Fin (B.size j)) ℂ) j := rfl

private theorem blockMatrixInclusion_factor (X : GLProd ℂ (fun _ : ι => B.size i)) (p : ι) :
    blockMatrixInclusion B (blockMatrixFactorInclusion B i ι X) p = blockPad B i (X p) := rfl

open Langlands.Algebra.UniversalEnveloping

local notation "L" => GLProd ℂ (blockRanks B ι)
local notation "M" => GLProd ℂ (fun _ : ι => B.size i)
local notation "U" => UniversalEnvelopingAlgebra ℂ (GLProd ℂ (blockRanks B ι))
local notation "A" => UniversalEnvelopingAlgebra ℂ (GLProd ℂ (fun _ : ι => B.size i))
local notation "j" => blockMatrixFactorInclusion B i ι
local notation "J" => LieEnvelopingEquiv.map (blockMatrixFactorInclusion B i ι)

private theorem blockComplement_commutes (X : L) (hX : ∀ p : ι, X (p, i) = 0) (a : A) :
    Commute (UniversalEnvelopingAlgebra.ι ℂ X) (J a) := by
  have hbr (Y : M) : ⁅X, j Y⁆ = 0 := by
    funext ⟨p, k⟩
    change X (p, k) * (j Y) (p, k) - (j Y) (p, k) * X (p, k) = 0
    by_cases hk : k = i
    · subst k
      simp only [hX, zero_mul, mul_zero, sub_zero]
    · simp [blockMatrixFactorInclusion_apply, Pi.single_eq_of_ne hk]
  obtain ⟨N, hN⟩ := exists_mem_degreeFiltration ℂ M a
  replace hN := degreeFiltration_le_wordSpan ℂ M N hN
  induction hN using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, -, rfl⟩ := ha
    induction l with
    | nil => rw [word_nil, map_one]; exact Commute.one_right _
    | cons y l ih =>
      rw [word_cons, map_mul, LieEnvelopingEquiv.map_generator]
      apply Commute.mul_right _ ih
      have h := (UniversalEnvelopingAlgebra.ι ℂ).map_lie X (j y)
      rw [hbr, map_zero, Ring.lie_def] at h
      exact sub_eq_zero.mp h.symm
  | zero => rw [map_zero]; exact Commute.zero_right _
  | add x y _ _ hx hy => rw [map_add]; exact hx.add_right hy
  | smul c x _ hx =>
    rw [map_smul, Algebra.smul_def]
    exact (Algebra.commute_algebraMap_right _ _).mul_right hx

private theorem blockMatrixFactor_map_mem_center (z : Subalgebra.center ℂ A) :
    J z.val ∈ Subalgebra.center ℂ U := by
  apply mem_center_of_commute
  intro X
  let Y : M := fun p => X (p, i)
  have hpart : Commute (UniversalEnvelopingAlgebra.ι ℂ (j Y)) (J z.val) := by
    rw [← LieEnvelopingEquiv.map_generator]
    exact (show Commute (UniversalEnvelopingAlgebra.ι ℂ Y) z.val from
      Subalgebra.mem_center_iff.mp z.property _).map J
  have hrest : Commute (UniversalEnvelopingAlgebra.ι ℂ (X - j Y)) (J z.val) := by
    apply blockComplement_commutes B i ι
    intro p
    simp [Y]
  have h := hpart.add_left hrest
  rw [← map_add, add_sub_cancel] at h
  exact h

/-- An individual block centre maps into the enveloping centre of the full matrix Levi. -/
def blockMatrixFactorCenterInclusion : Subalgebra.center ℂ A →ₐ[ℂ] Subalgebra.center ℂ U :=
  ((J).comp (Subalgebra.center ℂ A).val).codRestrict _ (blockMatrixFactor_map_mem_center B i ι)

@[simp]
theorem blockMatrixFactorCenterInclusion_val (z : Subalgebra.center ℂ A) :
    (blockMatrixFactorCenterInclusion B i ι z).val = J z.val := rfl

end MatrixProduct

section Archimedean

variable (F : Type u) [Field F] [NumberField F]

omit [NumberField F] in
private theorem realPlaceLieProjection_blockInclusion (X : RealLieAlgebra F (B.size i))
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}) :
    realPlaceLieProjection F n v (blockShapeRealLieInclusion F B i X) =
      blockPad B i (realPlaceLieProjection F (B.size i) v X) := by
  change (realLieAlgebraToMatrix F n (blockShapeRealLieInclusion F B i X)).map
    (realPlaceScalarProjection F v) = _
  rw [blockShapeRealLieInclusion_matrix]
  exact blockPad_map B i _ (map_zero (realPlaceScalarProjection F v)) _

omit [NumberField F] in
private theorem complexPlaceLieProjection_blockInclusion (X : RealLieAlgebra F (B.size i))
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}) :
    complexPlaceLieProjection F n v (blockShapeRealLieInclusion F B i X) =
      blockPad B i (complexPlaceLieProjection F (B.size i) v X) := by
  change (realLieAlgebraToMatrix F n (blockShapeRealLieInclusion F B i X)).map
    (complexPlaceScalarProjection F v) = _
  rw [blockShapeRealLieInclusion_matrix]
  exact blockPad_map B i _ (map_zero (complexPlaceScalarProjection F v)) _

/-- The actual block Lie inclusion becomes the block diagonal matrix inclusion in complex
archimedean coordinates. -/
theorem complexLieProductMatrixCoordinates_blockShapeInclusion (Y : ComplexLieAlgebra F (B.size i)) :
    complexLieProductMatrixCoordinates F n (blockShapeComplexLieInclusion F B i Y) =
      blockMatrixInclusion B (blockMatrixFactorInclusion B i (ComplexLieMatrixPlace F)
        (complexLieProductMatrixCoordinates F (B.size i) Y)) := by
  induction Y using TensorProduct.inductionOn with
  | add X Y hx hy => simp only [map_add, hx, hy]
  | tmul z X =>
    rw [show blockShapeComplexLieInclusion F B i (z ⊗ₜ[ℝ] X) =
      z ⊗ₜ[ℝ] blockShapeRealLieInclusion F B i X from rfl]
    funext p
    rw [blockMatrixInclusion_factor]
    cases p with
    | inl v =>
      rw [complexLieProductMatrixCoordinates_tmul_real, complexLieProductMatrixCoordinates_tmul_real,
        realPlaceLieProjection_blockInclusion, blockPad_smul,
        blockPad_map B i _ (map_zero (algebraMap ℝ ℂ))]
    | inr p =>
      obtain ⟨v, a⟩ := p
      rw [complexLieProductMatrixCoordinates_tmul_complex, complexLieProductMatrixCoordinates_tmul_complex,
        complexPlaceLieProjection_blockInclusion, blockPad_smul]
      obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
      · rw [ComplexGenericLarge.pairHom_zero, ComplexGenericLarge.pairHom_zero]
      · rw [ComplexGenericLarge.pairHom_one, ComplexGenericLarge.pairHom_one]
        exact congrArg (z • ·) (blockPad_map B i _ (map_zero (starRingEnd ℂ)) _)

/-- The corresponding comparison for all block enveloping operators. -/
theorem enveloping_complexLieMatrixCoordinates_blockShapeInclusion :
    (LieEnvelopingEquiv.enveloping (complexLieProductMatrixCoordinates F n)).toAlgHom.comp
        (blockShapeEnvelopingInclusion F B i) =
      (LieEnvelopingEquiv.map (blockMatrixInclusion B).toLieHom).comp
        ((LieEnvelopingEquiv.map (blockMatrixFactorInclusion B i (ComplexLieMatrixPlace F))).comp
          (LieEnvelopingEquiv.enveloping (complexLieProductMatrixCoordinates F (B.size i))).toAlgHom) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro Y
  simp only [LieHom.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply, blockShapeEnvelopingInclusion,
    LieEnvelopingEquiv.map_generator, AlgEquiv.coe_toAlgHom, LieEnvelopingEquiv.enveloping_generator]
  exact congrArg (UniversalEnvelopingAlgebra.ι ℂ)
    (complexLieProductMatrixCoordinates_blockShapeInclusion B i F Y)

end Archimedean

end Langlands.Automorphic

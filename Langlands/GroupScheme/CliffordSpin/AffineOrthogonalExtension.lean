import Langlands.GroupScheme.CliffordSpin.AffineModel
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-! # Orthogonal block extension of affine Clifford lift schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix CliffordAlgebra
open scoped TensorProduct

namespace Langlands.GroupScheme.CliffordSpin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

section Matrix

variable {F V W : Type u} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] {m n : ℕ}

/-- The concatenated basis of the orthogonal sum. -/
def orthogonalProductBasis (b : Module.Basis (Fin m) F V) (d : Module.Basis (Fin n) F W) :
    Module.Basis (Fin (m + n)) F (V × W) :=
  (b.prod d).reindex finSumFinEquiv

@[simp] theorem orthogonalProductBasis_inl (b : Module.Basis (Fin m) F V)
    (d : Module.Basis (Fin n) F W) (i : Fin m) :
    orthogonalProductBasis b d (finSumFinEquiv (Sum.inl i)) = (b i, 0) := by
  simp [orthogonalProductBasis, Module.Basis.prod_apply]

@[simp] theorem orthogonalProductBasis_inr (b : Module.Basis (Fin m) F V)
    (d : Module.Basis (Fin n) F W) (i : Fin n) :
    orthogonalProductBasis b d (finSumFinEquiv (Sum.inr i)) = (0, d i) := by
  simp [orthogonalProductBasis, Module.Basis.prod_apply]

variable (n) (A : Type u) [CommRing A]

private def blockMatrix : Matrix (Fin m) (Fin m) A →* Matrix (Fin (m + n)) (Fin (m + n)) A :=
  (Matrix.reindexRingEquiv A finSumFinEquiv).toMonoidHom.comp
    { toFun := fun x => Matrix.fromBlocks x 0 0 (1 : Matrix (Fin n) (Fin n) A)
      map_one' := Matrix.fromBlocks_one
      map_mul' := fun x y => by
        rw [Matrix.fromBlocks_multiply]
        simp }

/-- Extend an invertible matrix by the identity on the second block. -/
def orthogonalBlockMatrix : GL (Fin m) A →* GL (Fin (m + n)) A :=
  Units.map (blockMatrix n A)

variable {A}

theorem orthogonalBlockMatrix_coe (g : GL (Fin m) A) :
    (orthogonalBlockMatrix n A g : Matrix (Fin (m + n)) (Fin (m + n)) A) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (g : Matrix (Fin m) (Fin m) A) 0 0 (1 : Matrix (Fin n) (Fin n) A)) :=
  rfl

@[simp] theorem det_orthogonalBlockMatrix (g : GL (Fin m) A) :
    Matrix.GeneralLinearGroup.det (orthogonalBlockMatrix n A g) = Matrix.GeneralLinearGroup.det g := by
  apply Units.ext
  change (orthogonalBlockMatrix n A g : Matrix (Fin (m + n)) (Fin (m + n)) A).det = _
  rw [orthogonalBlockMatrix_coe, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]
  rfl

theorem orthogonalBlockMatrix_map {B : Type u} [CommRing B] (f : A →+* B) (g : GL (Fin m) A) :
    Matrix.GeneralLinearGroup.map f (orthogonalBlockMatrix n A g) =
      orthogonalBlockMatrix n B (Matrix.GeneralLinearGroup.map f g) := by
  apply Units.ext
  change (orthogonalBlockMatrix n A g : Matrix (Fin (m + n)) (Fin (m + n)) A).map f =
    (orthogonalBlockMatrix n B (Matrix.GeneralLinearGroup.map f g) :
      Matrix (Fin (m + n)) (Fin (m + n)) B)
  rw [orthogonalBlockMatrix_coe, orthogonalBlockMatrix_coe]
  change Matrix.reindex finSumFinEquiv finSumFinEquiv
    ((Matrix.fromBlocks (g : Matrix (Fin m) (Fin m) A) 0 0 (1 : Matrix (Fin n) (Fin n) A)).map f) = _
  rw [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f), Matrix.map_zero _ (map_zero f),
    Matrix.map_one _ (map_zero f) (map_one f)]
  rfl

end Matrix

variable {F V W : Type u} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] {m n : ℕ}
  (Q : QuadraticForm F V) (P : QuadraticForm F W)

local notation "j" => CliffordAlgebra.map (QuadraticMap.Isometry.inl Q P)
local notation "Qₛ" => Q.prod P

/-- The coefficient extension of the Clifford inclusion for the first summand. -/
abbrev orthogonalTensorMap (A : Type u) [CommRing A] [Algebra F A] :
    A ⊗[F] CliffordAlgebra Q →ₐ[F] A ⊗[F] CliffordAlgebra Qₛ :=
  Algebra.TensorProduct.map (AlgHom.id F A) j

omit [Invertible (2 : F)] in
private theorem inclusion_grade_reverse (c : CliffordAlgebra Q) :
    involute (j c) = j (involute c) ∧ reverse (j c) = j (reverse c) := by
  induction c using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι x => simp
  | mul x y hx hy => simp only [map_mul, reverse.map_mul, hx.1, hx.2, hy.1, hy.2, and_self]
  | add x y hx hy => simp only [map_add, hx.1, hx.2, hy.1, hy.2, and_self]

omit [Invertible (2 : F)] in
private theorem inclusion_commute_right (y : W) (c : CliffordAlgebra Q) :
    ι Qₛ (0, y) * j c = j (involute c) * ι Qₛ (0, y) := by
  induction c using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [involute.commutes, (j).commutes]
    exact (Algebra.commutes r _).symm
  | ι x =>
    have h : QuadraticMap.polar Qₛ (0, y) (x, 0) = 0 := by
      simp [QuadraticMap.polar, add_comm]
    simp only [CliffordAlgebra.map_apply_ι, involute_ι, map_neg, QuadraticMap.Isometry.inl_apply]
    rw [CliffordAlgebra.ι_mul_ι_comm, h, map_zero, zero_sub, neg_mul]
  | mul x y hx hy => rw [map_mul, ← mul_assoc, hx, mul_assoc, hy, ← mul_assoc, ← map_mul, ← map_mul]
  | add x y hx hy => simp only [map_add, mul_add, add_mul, hx, hy]

variable {A : Type u} [CommRing A] [Algebra F A]

local notation "J" => orthogonalTensorMap Q P A

omit [Invertible (2 : F)] in
private theorem tensor_grade_reverse (a : A ⊗[F] CliffordAlgebra Q) :
    TensorProduct.map LinearMap.id involute.toLinearMap (J a) =
        J (TensorProduct.map LinearMap.id involute.toLinearMap a) ∧
      TensorProduct.map LinearMap.id reverse (J a) =
        J (TensorProduct.map LinearMap.id reverse a) := by
  induction a using TensorProduct.inductionOn with
  | tmul s c =>
    obtain ⟨hg, hr⟩ := inclusion_grade_reverse Q P c
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, AlgHom.toLinearMap_apply, hg, hr, and_self]
  | add a c ha hc => simp only [map_add, ha.1, ha.2, hc.1, hc.2, and_self]

omit [Invertible (2 : F)] in
private theorem tensor_commute_right (y : W) (a : A ⊗[F] CliffordAlgebra Q) :
    (1 ⊗ₜ[F] ι Qₛ (0, y)) * J a =
      J (TensorProduct.map LinearMap.id involute.toLinearMap a) * (1 ⊗ₜ[F] ι Qₛ (0, y)) := by
  induction a using TensorProduct.inductionOn with
  | tmul s c =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, AlgHom.toLinearMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, inclusion_commute_right]
  | add a c ha hc => simp only [map_add, mul_add, add_mul, ha, hc]

variable (b : Module.Basis (Fin m) F V) (d : Module.Basis (Fin n) F W)

omit [Invertible (2 : F)] in
private theorem actionDefect_block_inl
    (a : A ⊗[F] CliffordAlgebra Q) (g : GL (Fin m) A) (i : Fin m) :
    actionDefect Qₛ (orthogonalProductBasis b d) A (J a) (orthogonalBlockMatrix n A g)
      (finSumFinEquiv (Sum.inl i)) = J (actionDefect Q b A a g i) := by
  rw [actionDefect, orthogonalProductBasis_inl, ← Equiv.sum_comp finSumFinEquiv,
    Fintype.sum_sum_type, actionDefect, map_sub, map_mul, map_mul, map_sum]
  simp only [orthogonalBlockMatrix_coe, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁,
    Matrix.zero_apply, orthogonalProductBasis_inl, orthogonalProductBasis_inr,
    TensorProduct.zero_tmul, Finset.sum_const_zero, add_zero, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, CliffordAlgebra.map_apply_ι, QuadraticMap.Isometry.inl_apply]

omit [Invertible (2 : F)] in
private theorem actionDefect_block_inr
    (a : A ⊗[F] CliffordAlgebra Q) (g : GL (Fin m) A) (i : Fin n)
    (ha : gradeDefect Q A a = 0) :
    actionDefect Qₛ (orthogonalProductBasis b d) A (J a) (orthogonalBlockMatrix n A g)
      (finSumFinEquiv (Sum.inr i)) = 0 := by
  rw [actionDefect, orthogonalProductBasis_inr, ← Equiv.sum_comp finSumFinEquiv,
    Fintype.sum_sum_type]
  simp only [orthogonalBlockMatrix_coe, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, orthogonalProductBasis_inl, orthogonalProductBasis_inr,
    TensorProduct.zero_tmul, Finset.sum_const_zero, zero_add]
  rw [show (∑ k : Fin n, ((1 : Matrix (Fin n) (Fin n) A) k i) ⊗ₜ[F] ι Qₛ (0, d k)) =
    (1 : A) ⊗ₜ[F] ι Qₛ (0, d i) by simp [Matrix.one_apply, TensorProduct.ite_tmul]]
  rw [sub_eq_zero, tensor_commute_right, sub_eq_zero.mp ha]

private def blockPair (A : Type u) [CommRing A] [Algebra F A] :
    ((A ⊗[F] CliffordAlgebra Q)ˣ × GL (Fin m) A) →*
      ((A ⊗[F] CliffordAlgebra Qₛ)ˣ × GL (Fin (m + n)) A) :=
  (Units.map (orthogonalTensorMap Q P A).toMonoidHom).prodMap (orthogonalBlockMatrix n A)

private theorem blockPair_mem (x : coefficientSubgroup Q b A) :
    blockPair (n := n) Q P A x.val ∈ coefficientSubgroup Qₛ (orthogonalProductBasis b d) A := by
  obtain ⟨hg, hn, hd, ha⟩ := (mem_coefficientSubgroup_iff Q b x.val.1 x.val.2).mp x.property
  rw [mem_coefficientSubgroup_iff]
  change gradeDefect Qₛ A (J x.val.1) = 0 ∧ normDefect Qₛ A (J x.val.1) = 0 ∧
    Matrix.GeneralLinearGroup.det (orthogonalBlockMatrix n A x.val.2) = 1 ∧
    ∀ i, actionDefect Qₛ (orthogonalProductBasis b d) A (J x.val.1) (orthogonalBlockMatrix n A x.val.2) i = 0
  refine ⟨?_, ?_, (det_orthogonalBlockMatrix n x.val.2).trans hd, ?_⟩
  · rw [gradeDefect, (tensor_grade_reverse Q P (x.val.1 : A ⊗[F] CliffordAlgebra Q)).1, ← map_sub]
    exact (congrArg J hg).trans (map_zero J)
  · rw [normDefect, (tensor_grade_reverse Q P (x.val.1 : A ⊗[F] CliffordAlgebra Q)).2,
      ← map_mul, ← map_one J, ← map_sub]
    exact (congrArg J hn).trans (map_zero J)
  · intro i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    cases i with
    | inl i => rw [actionDefect_block_inl, ha i, map_zero]
    | inr i => exact actionDefect_block_inr Q P b d _ _ i hg

/-- Extend the coefficient spin lift by the identity on the complementary block. -/
def orthogonalBlockPair (A : Type u) [CommRing A] [Algebra F A] :
    coefficientSubgroup Q b A →* coefficientSubgroup Qₛ (orthogonalProductBasis b d) A :=
  ((blockPair (n := n) Q P A).comp (coefficientSubgroup Q b A).subtype).codRestrict _
    (blockPair_mem Q P b d)

theorem orthogonalBlockPair_val (x : coefficientSubgroup Q b A) :
    (orthogonalBlockPair Q P b d A x).val =
      (Units.map (orthogonalTensorMap Q P A).toMonoidHom x.val.1, orthogonalBlockMatrix n A x.val.2) :=
  rfl

omit [Invertible (2 : F)] in
private theorem tensorMap_orthogonalTensorMap {B : Type u} [CommRing B] [Algebra F B] (f : A →ₐ[F] B)
    (c : A ⊗[F] CliffordAlgebra Q) :
    tensorMap Qₛ f (orthogonalTensorMap Q P A c) =
      orthogonalTensorMap Q P B (tensorMap Q f c) := by
  induction c using TensorProduct.inductionOn with
  | tmul a c => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  | add a c ha hc => simp only [map_add, ha, hc]

private def orthogonalExtensionNat : Corepresented.cutFunctor (isCutOutBy Q b) ⟶
    Corepresented.cutFunctor (isCutOutBy Qₛ (orthogonalProductBasis b d)) where
  app A := GrpCat.ofHom (orthogonalBlockPair Q P b d A)
  naturality {A B} f := by
    ext x
    apply Subtype.ext
    apply Prod.ext
    · apply Units.ext
      exact (tensorMap_orthogonalTensorMap Q P f.hom _).symm
    · exact (orthogonalBlockMatrix_map n f.hom.toRingHom _).symm

/-- The homomorphism of affine Clifford lift schemes induced by the first orthogonal summand. -/
def orthogonalExtension : groupScheme Q b ⟶ groupScheme Qₛ (orthogonalProductBasis b d) :=
  Corepresented.groupSchemeMap (Corepresented.cutCorepresentableBy (isCutOutBy Q b))
    (Corepresented.cutCorepresentableBy (isCutOutBy Qₛ (orthogonalProductBasis b d)))
    (orthogonalExtensionNat Q P b d)

/-- The affine scheme map extends both the Clifford unit and its vector-action matrix. -/
theorem affinePairEquiv_orthogonalExtension (A : CommAlgCat.{u} (CommRingCat.of F))
    (x : (groupScheme Q b).affinePoints A) :
    affinePairEquiv Qₛ (orthogonalProductBasis b d) A (x ≫ (orthogonalExtension Q P b d).hom.hom) =
      orthogonalBlockPair Q P b d A (affinePairEquiv Q b A x) :=
  Corepresented.groupSchemeMap_affinePoints (Corepresented.cutCorepresentableBy (isCutOutBy Q b))
    (Corepresented.cutCorepresentableBy (isCutOutBy Qₛ (orthogonalProductBasis b d)))
    (orthogonalExtensionNat Q P b d) x

/-- Orthogonal block extension is realized by an affine group-scheme morphism
  with its stated Clifford and matrix coordinates over every coefficient algebra. -/
def CliffordSpinAffineBlockExtensionStatement : Prop :=
  ∀ (F : Type u) [Field F] [Invertible (2 : F)]
    (V W : Type u) [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (Q : QuadraticForm F V) (P : QuadraticForm F W) (m n : ℕ)
    (b : Module.Basis (Fin m) F V) (d : Module.Basis (Fin n) F W),
    ∃ e : groupScheme Q b ⟶ groupScheme (Q.prod P) (orthogonalProductBasis b d),
      ∀ (A : CommAlgCat.{u} (CommRingCat.of F)) (x : (groupScheme Q b).affinePoints A),
        (affinePairEquiv (Q.prod P) (orthogonalProductBasis b d) A (x ≫ e.hom.hom)).val =
          (Units.map (orthogonalTensorMap Q P A).toMonoidHom (affinePairEquiv Q b A x).val.1,
            orthogonalBlockMatrix n A (affinePairEquiv Q b A x).val.2)

theorem cliffordSpinAffineBlockExtension : CliffordSpinAffineBlockExtensionStatement.{u} := by
  intro F _ _ V W _ _ _ _ Q P m n b d
  refine ⟨orthogonalExtension Q P b d, fun A x => ?_⟩
  rw [affinePairEquiv_orthogonalExtension, orthogonalBlockPair_val]

end Langlands.GroupScheme.CliffordSpin

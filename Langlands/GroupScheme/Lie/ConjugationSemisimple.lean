import Langlands.GroupScheme.Lie.ConjugationDerivation
import Langlands.GroupScheme.Lie.TangentSemisimplicity
import Langlands.GroupScheme.AffineLinearEmbedding.Comodule
import Langlands.GroupScheme.Chevalley.ActualLineStabilizer

/-! # Finite coefficient spaces for actual conjugation -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix TensorProduct

namespace Langlands.GroupScheme.Lie

private theorem matrix_fst_mul {A : Type u} [CommRing A]
    {n : Type} [Fintype n] (M N : Matrix n n (DualNumber A)) :
    (M * N).map TrivSqZeroExt.fst =
      M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.fst :=
  Matrix.map_mul (f := (TrivSqZeroExt.fstHom A A A).toRingHom)

private theorem matrix_snd_mul {A : Type u} [CommRing A]
    {n : Type} [Fintype n] (M N : Matrix n n (DualNumber A)) :
    (M * N).map TrivSqZeroExt.snd =
      M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.snd +
        M.map TrivSqZeroExt.snd * N.map TrivSqZeroExt.fst := by
  ext i j
  simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul,
    Finset.sum_add_distrib, smul_eq_mul, mul_comm]

private theorem matrix_snd_infinitesimalConjugate {A : Type u} [CommRing A]
    {n : Type} [Fintype n] [DecidableEq n] (T : Matrix n n A) (M : GL n A) :
    GeneralLinear.DualNumber.coefficients
      (GeneralLinear.DualNumber.matrixUnit T *
        Matrix.GeneralLinearGroup.map (TrivSqZeroExt.inlHom A A) M *
          (GeneralLinear.DualNumber.matrixUnit T)⁻¹) =
      T * (M : Matrix n n A) - (M : Matrix n n A) * T := by
  have hfst : ((GeneralLinear.DualNumber.matrixUnit T : GL n (DualNumber A)) :
      Matrix n n (DualNumber A)).map TrivSqZeroExt.fst = 1 := by
    ext i j
    by_cases h : i = j <;>
      simp [GeneralLinear.DualNumber.matrixUnit_val,
        GeneralLinear.DualNumber.epsilonMatrix, Matrix.one_apply, h]
  have hfstinv : (((GeneralLinear.DualNumber.matrixUnit T)⁻¹ : GL n (DualNumber A)) :
      Matrix n n (DualNumber A)).map TrivSqZeroExt.fst = 1 := by
    rw [GeneralLinear.DualNumber.matrixUnit_inv_val]
    ext i j
    by_cases h : i = j <;>
      simp [GeneralLinear.DualNumber.epsilonMatrix, Matrix.one_apply, h]
  have hsndinv : (((GeneralLinear.DualNumber.matrixUnit T)⁻¹ : GL n (DualNumber A)) :
      Matrix n n (DualNumber A)).map TrivSqZeroExt.snd = -T := by
    rw [GeneralLinear.DualNumber.matrixUnit_inv_val]
    ext i j
    by_cases h : i = j <;>
      simp [GeneralLinear.DualNumber.epsilonMatrix, h]
  have hsnd : (GeneralLinear.DualNumber.matrixUnit T :
      Matrix n n (DualNumber A)).map TrivSqZeroExt.snd = T :=
    GeneralLinear.DualNumber.coefficients_matrixUnit T
  change ((GeneralLinear.DualNumber.matrixUnit T : Matrix n n (DualNumber A)) *
    (Matrix.GeneralLinearGroup.map (TrivSqZeroExt.inlHom A A) M : Matrix n n (DualNumber A)) *
      ((GeneralLinear.DualNumber.matrixUnit T)⁻¹ : GL n (DualNumber A))).map
        TrivSqZeroExt.snd = _
  rw [matrix_snd_mul, matrix_snd_mul]
  rw [matrix_fst_mul, hfst, hfstinv, hsndinv]
  have hc : ((Matrix.GeneralLinearGroup.map (TrivSqZeroExt.inlHom A A) M :
      GL n (DualNumber A)) : Matrix n n (DualNumber A)).map TrivSqZeroExt.fst = M := by
    ext i j
    rfl
  have hz : ((Matrix.GeneralLinearGroup.map (TrivSqZeroExt.inlHom A A) M :
      GL n (DualNumber A)) : Matrix n n (DualNumber A)).map TrivSqZeroExt.snd = 0 := by
    ext i j
    rfl
  rw [hc, hz, hsnd]
  change 1 * (M : Matrix n n A) * -T +
    (1 * 0 + T * (M : Matrix n n A)) * 1 = _
  simp [sub_eq_add_neg, add_comm]

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- Universal matrix coefficients of an actual finite representation. -/
def representationCoefficients (ρ : MatrixRepresentation G n) :
    Matrix n n (coordinateAlgebra G) :=
  ρ.affineMatrix (coordinateAlgebra G) (universalPoint G)

/-- Every actual point matrix is evaluation of the universal coefficients. -/
theorem affineMatrix_eq_coefficients (ρ : MatrixRepresentation G n)
    {A : Type u} [CommRing A] [Algebra k A] (g : AffinePoints G A) :
    (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A) g : Matrix n n A) =
      (representationCoefficients G ρ).map (pointCoordinates G g) := by
  have h := ρ.affineMatrix_naturality (CommAlgCat.ofHom (pointCoordinates G g))
    (universalPoint G)
  change ρ.affineMatrix _ (affineMap G (pointCoordinates G g) (universalPoint G)) = _ at h
  rw [affineMap_universalPoint, Equiv.symm_apply_apply] at h
  exact congrArg Units.val h

/-- The actual coordinate derivation differentiates conjugation of coefficient matrices. -/
theorem conjugationDerivation_coefficients (ρ : MatrixRepresentation G n)
    (X : lieKernel G k) :
    (representationCoefficients G ρ).map (conjugationDerivation G X) =
      (ρ.tangentMatrix k X).map (algebraMap k (coordinateAlgebra G)) *
          representationCoefficients G ρ -
        representationCoefficients G ρ *
          (ρ.tangentMatrix k X).map (algebraMap k (coordinateAlgebra G)) := by
  have he := affineMatrix_eq_coefficients G ρ
    (infinitesimalConjugate G X (universalPoint G))
  have hcoeff : (representationCoefficients G ρ).map (conjugationDerivation G X) =
      (ρ.affineMatrix _ (infinitesimalConjugate G X (universalPoint G)) :
        Matrix n n (DualNumber (coordinateAlgebra G))).map TrivSqZeroExt.snd := by
    rw [he]
    ext i j
    rfl
  rw [hcoeff]
  have hx : ρ.affineMatrix
      (CommAlgCat.of (CommRingCat.of k) (DualNumber (coordinateAlgebra G)))
      (lieKernelMap G (Algebra.ofId k (coordinateAlgebra G)) X).val =
      GeneralLinear.DualNumber.matrixUnit
        ((ρ.tangentMatrix k X).map (algebraMap k (coordinateAlgebra G))) := by
    change ρ.affineMatrix _ (affineMap G _ X.val) = _
    rw [affineMap_apply, ρ.affineMatrix_naturality, MatrixRepresentation.affineMatrix_eq_matrixUnit]
    exact GeneralLinear.DualNumber.matrixUnit_map _ _
  have hc : ρ.affineMatrix _ (constant G (universalPoint G)) =
      Matrix.GeneralLinearGroup.map
        (TrivSqZeroExt.inlHom (coordinateAlgebra G) (coordinateAlgebra G))
        (ρ.affineMatrix (coordinateAlgebra G) (universalPoint G)) := by
    exact ρ.affineMatrix_naturality
      (CommAlgCat.ofHom (TrivSqZeroExt.inlAlgHom k (coordinateAlgebra G) (coordinateAlgebra G)))
      (universalPoint G)
  simp only [infinitesimalConjugate, map_mul, map_inv, hx, hc]
  exact matrix_snd_infinitesimalConjugate _ _

/-- Every coordinate lies in the coefficient span of an actual finite representation. -/
theorem exists_representation_coefficient_span (c : coordinateAlgebra G) :
    ∃ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)),
      c ∈ Submodule.span k
        (Set.range fun p : Fin N × Fin N => representationCoefficients G ρ p.1 p.2) := by
  classical
  let e := AffineLinearEmbedding.corepresentableBy G (coordinateIso G)
  let := (AffineLinearEmbedding.bialgebra e).toCoalgebra
  obtain ⟨N, M, hcomul, hcounit, hspan⟩ :=
    AffineLinearEmbedding.exists_matrix_coefficients (K := k) ({c} : Finset (coordinateAlgebra G))
  let ρ₀ : MatrixRepresentation (AffineLinearEmbedding.model G (coordinateIso G)) (Fin N) :=
    AffineLinearEmbedding.toGLHom e M hcomul hcounit
  let ρ := MatrixRepresentation.restrict ρ₀
    (AffineLinearEmbedding.modelIso G (coordinateIso G)).inv
  have hM : representationCoefficients G ρ = M := by
    ext i j
    change ρ.affineMatrix (coordinateAlgebra G) (universalPoint G) i j = M i j
    rw [MatrixRepresentation.affineMatrix_restrict,
      Chevalley.modelIso_inv_hom_hom (coordinateIso G)]
    have hu : universalPoint G = (coordinateIso G).hom := by
      simp [universalPoint, pointCoordinates]
    rw [hu, Iso.hom_inv_id]
    change GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
      (coordinateAlgebra G) ((𝟙 _) ≫ ρ₀.hom.hom) i j = _
    erw [Corepresented.groupSchemeMap_affinePoints,
      Corepresented.affinePointsEquiv_apply, algSpec.fullyFaithful.preimage_id]
    change (e.homEquiv.symm (e.homEquiv (𝟙 (coordinateAlgebra G)))).hom (M i j) = _
    rw [Equiv.symm_apply_apply]
    rfl
  refine ⟨N, ρ, ?_⟩
  rw [hM]
  exact hspan (Finset.mem_singleton_self c)

/-- The linear map from formal coefficient coordinates to the coordinate algebra. -/
def coefficientLinearMap (ρ : MatrixRepresentation G n) :
    (n × n → k) →ₗ[k] coordinateAlgebra G :=
  Fintype.linearCombination k (fun p : n × n => representationCoefficients G ρ p.1 p.2)

/-- The coefficient map intertwines conjugation with the negative dual-tensor differential. -/
theorem coefficientLinearMap_intertwines (ρ : MatrixRepresentation G n) (X : lieKernel G k) :
    coefficientLinearMap G ρ ∘ₗ
        (-Matrix.toLin' ((ρ.dual.tensor ρ).tangentMatrix k X)) =
      (conjugationDerivation G X).toLinearMap ∘ₗ coefficientLinearMap G ρ := by
  apply (Pi.basisFun k (n × n)).ext
  rintro ⟨l, s⟩
  have hD := congrArg (fun M : Matrix n n (coordinateAlgebra G) => M l s)
    (conjugationDerivation_coefficients G ρ X)
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply] at hD
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, Pi.basisFun_apply,
    Matrix.toLin'_apply, Matrix.mulVec_single_one,
    coefficientLinearMap, Fintype.linearCombination_apply_single, one_smul]
  refine Eq.trans ?_ hD.symm
  change (∑ p : n × n, (-((ρ.dual.tensor ρ).tangentMatrix k X p (l, s))) •
    representationCoefficients G ρ p.1 p.2) = _
  simp only [Fintype.sum_prod_type, MatrixRepresentation.tangentMatrix_tensor_entry,
    MatrixRepresentation.tangentMatrix_dual, Matrix.neg_apply, Matrix.transpose_apply,
    Matrix.one_apply, neg_add, add_smul, neg_smul,
    ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero, ite_smul, zero_smul,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]
  simp [Finset.sum_ite_eq', Algebra.smul_def, ← Finset.sum_neg_distrib,
    mul_comm, sub_eq_add_neg, add_comm]

/-- A coefficient range is invariant under the actual conjugation derivation. -/
theorem coefficientLinearMap_range_invariant
    (ρ : MatrixRepresentation G n) (X : lieKernel G k) :
    ∀ y ∈ LinearMap.range (coefficientLinearMap G ρ), conjugationDerivation G X y ∈
      LinearMap.range (coefficientLinearMap G ρ) := by
  rintro _ ⟨v, rfl⟩
  exact ⟨(-Matrix.toLin' ((ρ.dual.tensor ρ).tangentMatrix k X)) v,
    LinearMap.congr_fun (coefficientLinearMap_intertwines G ρ X) v⟩

/-- Over an algebraically closed field, every coefficient range has semisimple
conjugation differential when the Lie element is representation-semisimple. -/
theorem IsSemisimpleElement.isSemisimple_coefficient_range [IsAlgClosed k]
    {X : lieKernel G k} (hX : IsSemisimpleElement G X) (ρ : MatrixRepresentation G n) :
    Module.End.IsSemisimple ((conjugationDerivation G X).toLinearMap.restrict
      (coefficientLinearMap_range_invariant G ρ X)) := by
  apply isSemisimple_of_surjective_intertwiner
    (coefficientLinearMap G ρ).rangeRestrict
    (coefficientLinearMap G ρ).surjective_rangeRestrict
    (a := -Matrix.toLin' ((ρ.dual.tensor ρ).tangentMatrix k X))
  · apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (coefficientLinearMap_intertwines G ρ X) v
  · exact Module.End.isSemisimple_neg.mpr
      (hX.isSemisimple_tangentMatrix (ρ.dual.tensor ρ))

/-- The coordinate conjugation derivation of a semisimple Lie element is locally
semisimple over an algebraically closed field. -/
theorem IsSemisimpleElement.locallySemisimple_conjugationDerivation [IsAlgClosed k]
    {X : lieKernel G k} (hX : IsSemisimpleElement G X) :
    Langlands.Algebra.SemisimpleDerivation.LocallySemisimple
      (conjugationDerivation G X).toLinearMap := by
  intro c
  obtain ⟨N, ρ, hc⟩ := exists_representation_coefficient_span G c
  refine ⟨LinearMap.range (coefficientLinearMap G ρ),
    coefficientLinearMap_range_invariant G ρ X, ?_, inferInstance,
    hX.isSemisimple_coefficient_range G ρ⟩
  simpa only [coefficientLinearMap, Fintype.range_linearCombination] using hc

end Langlands.GroupScheme.Lie

import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.GroupScheme.MatrixRepresentationTensor
import Langlands.GroupScheme.Unipotent.CoordinateBialgebra

/-! # Coefficient embeddings into finite regular representations -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.Chevalley

open AffineLinearEmbedding MatrixRepresentation

section Coordinates

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B] [Coalgebra k B]
  (V : Submodule k B) {d : ℕ} (b : Basis (Fin d) k V)
  {n : Type} [Fintype n] [DecidableEq n]

/-- Coordinates of a finite family in a chosen regular subspace. -/
def coactionCoordinates (a : n → B) : Matrix (Fin d) n k :=
  Matrix.of fun i j => extendedCoord V b i (a j)

omit [DecidableEq n] in
/-- The coaction equation for a family becomes an actual matrix intertwining
equation in regular-subspace coordinates. -/
theorem coactionCoordinates_mul (a : n → B) (M : Matrix n n B)
    (ha : ∀ j, a j ∈ V)
    (hΔ : ∀ j, comul (R := k) (a j) = ∑ l, a l ⊗ₜ[k] M l j) :
    (coactionCoordinates V b a).map (algebraMap k B) * M =
      subspaceMatrix V b * (coactionCoordinates V b a).map (algebraMap k B) := by
  ext i j
  have h₁ : leftAct (extendedCoord V b i) (a j) =
      ∑ l, extendedCoord V b i (a l) • M l j := by
    rw [leftAct_apply, hΔ, map_sum, map_sum]
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
  have h₂ : leftAct (extendedCoord V b i) (a j) =
      ∑ l, extendedCoord V b l (a j) • subspaceMatrix V b i l := by
    conv_lhs => rw [← basis_expand V b (ha j)]
    rw [map_sum]
    simp only [map_smul]
    rfl
  calc
    _ = ∑ l, extendedCoord V b i (a l) • M l j := by
      simp only [Matrix.mul_apply, Matrix.map_apply, coactionCoordinates,
        Matrix.of_apply, Algebra.smul_def]
    _ = leftAct (extendedCoord V b i) (a j) := h₁.symm
    _ = ∑ l, extendedCoord V b l (a j) • subspaceMatrix V b i l := h₂
    _ = _ := by
      simp only [Matrix.mul_apply, Matrix.map_apply, coactionCoordinates,
        Matrix.of_apply, Algebra.smul_def]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end Coordinates

section Copies

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m I : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype I] [DecidableEq I]

/-- A family of equivariant maps is an equivariant map into finitely many copies. -/
theorem intertwines_tensor_trivial
    (ρ : MatrixRepresentation G n) (τ : MatrixRepresentation G m)
    (C : I → Matrix m n k) (hC : ∀ i, Intertwines ρ τ (C i)) :
    Intertwines ρ (τ.tensor (trivial G I))
      (Matrix.of fun (ji : m × I) a => C ji.2 ji.1 a) := by
  intro S x
  ext ⟨i, t⟩ j
  have ht : ((τ.tensor (trivial G I)).affineMatrix S x : Matrix (m × I) (m × I) S) =
      Matrix.of (fun ab cd => (τ.affineMatrix S x : Matrix m m S) ab.1 cd.1 *
        (1 : Matrix I I S) ab.2 cd.2) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    calc
      _ = τ.affineMatrix S x a c * (trivial G I).affineMatrix S x b d :=
        tensor_affineMatrix_entry τ (trivial G I) S x a c b d
      _ = _ := by rw [trivial_affineMatrix]; rfl
  rw [ht]
  have h := congrArg (fun M : Matrix m n S => M i j) (hC t S x)
  simpa [Matrix.mul_apply, Matrix.map_apply, tensor_affineMatrix,
    GeneralLinear.kroneckerHom_coe, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.one_apply] using h

end Copies

section Actual

variable {k : Type u} [Field k]
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Equivariance of a constant matrix can be checked at the universal affine
point; naturality then gives every affine algebra test. -/
theorem intertwines_of_universalMatrix
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n)
    (σ : MatrixRepresentation (Corepresented.groupScheme F e) m)
    (C : Matrix m n k)
    (hC : C.map (algebraMap k B) * Unipotent.universalMatrix e ρ =
      Unipotent.universalMatrix e σ * C.map (algebraMap k B)) :
    Intertwines (k := k) ρ σ C := by
  intro S x
  let f : B ⟶ S := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage x).unop
  have hx : Unipotent.classifiedPoint e f = x :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage x
  have hρ := Unipotent.affineMatrix_classifiedPoint e ρ S f
  have hσ := Unipotent.affineMatrix_classifiedPoint e σ S f
  rw [hx] at hρ hσ
  rw [hρ, hσ]
  ext i j
  have hij := congrArg (fun M : Matrix m n B => f.hom (M i j)) hC
  simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul,
    AlgHom.commutes] using hij

/-- The universal matrix of the actual regular representation is its
constructed coaction matrix. -/
theorem regularRepresentation_universalMatrix
    (V : Submodule k B) {d : ℕ} (b : Basis (Fin d) k V)
    (hV : letI := (bialgebra e).toCoalgebra
      ∀ (f : Module.Dual k B) (v : B), v ∈ V → rightAct f v ∈ V) :
    letI := (bialgebra e).toCoalgebra
    Unipotent.universalMatrix e
        (regularRepresentation e (Field.toIsField k) V b hV) =
      subspaceMatrix V b := by
  let := (bialgebra e).toCoalgebra
  ext i j
  change GeneralLinear.affinePointsEquiv (Fin d) (CommRingCat.of k) B
    ((𝟙 _) ≫ (toGLHom e (subspaceMatrix V b)
      (comul_subspaceMatrix V b hV) (counit_subspaceMatrix V b)).hom.hom) i j = _
  erw [Corepresented.groupSchemeMap_affinePoints,
    Corepresented.affinePointsEquiv_apply, algSpec.fullyFaithful.preimage_id]
  change (e.homEquiv.symm (e.homEquiv (𝟙 B))).hom (subspaceMatrix V b i j) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- All rows of the universal coefficient matrix, in finite regular coordinates. -/
def coefficientEmbedding (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n)
    (V : Submodule k B) {d : ℕ} (b : Basis (Fin d) k V) :
    Matrix (Fin d × n) n k :=
  Matrix.of fun ij j => extendedCoord V b ij.1 (Unipotent.universalMatrix e ρ ij.2 j)

/-- Matrix coefficients give an actual equivariant map into regular copies. -/
theorem intertwines_coefficientEmbedding
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n)
    (V : Submodule k B) {d : ℕ} (b : Basis (Fin d) k V)
    (hV : letI := (bialgebra e).toCoalgebra
      ∀ (f : Module.Dual k B) (v : B), v ∈ V → rightAct f v ∈ V)
    (hN : ∀ i j, Unipotent.universalMatrix e ρ i j ∈ V) :
    Intertwines ρ
      ((regularRepresentation e (Field.toIsField k) V b hV).tensor
        (trivial (Corepresented.groupScheme F e) n))
      (coefficientEmbedding e ρ V b) := by
  let := (bialgebra e).toCoalgebra
  refine intertwines_tensor_trivial ρ
    (regularRepresentation e (Field.toIsField k) V b hV)
    (fun i => coactionCoordinates V b (Unipotent.universalMatrix e ρ i)) ?_
  intro i
  apply intertwines_of_universalMatrix e
  rw [regularRepresentation_universalMatrix]
  exact coactionCoordinates_mul V b (Unipotent.universalMatrix e ρ i)
    (Unipotent.universalMatrix e ρ) (hN i) (Unipotent.comul_universalMatrix e ρ i)

/-- The counit recovers every original coordinate, so the coefficient map is injective. -/
theorem coefficientEmbedding_injective
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n)
    (V : Submodule k B) {d : ℕ} (b : Basis (Fin d) k V)
    (hN : ∀ i j, Unipotent.universalMatrix e ρ i j ∈ V) :
    Function.Injective (coefficientEmbedding e ρ V b).mulVecLin := by
  classical
  apply (coefficientEmbedding e ρ V b).mulVecLin.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  funext i
  have hz : ∑ j, v j • Unipotent.universalMatrix e ρ i j = 0 := by
    calc
      _ = ∑ j, v j • ∑ l, extendedCoord V b l
            (Unipotent.universalMatrix e ρ i j) • (b l : B) := by
        congr 1
        ext j
        rw [basis_expand V b (hN i j)]
      _ = ∑ l, (∑ j, extendedCoord V b l
            (Unipotent.universalMatrix e ρ i j) * v j) • (b l : B) := by
        simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
        congr 1
        ext l
        congr 1
        ext j
        rw [mul_comm]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        have h := congrFun hv (l, i)
        change (∑ j, extendedCoord V b l
          (Unipotent.universalMatrix e ρ i j) * v j) = 0 at h
        rw [h, zero_smul]
  have hc := congrArg (AffineLinearEmbedding.counit e) hz
  simpa [map_sum, map_smul, Unipotent.counit_universalMatrix e ρ,
    Matrix.one_apply] using hc

/-- Every actual finite-dimensional representation embeds equivariantly into
finitely many copies of a finite regular representation. -/
theorem exists_finite_regular_embedding
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n) :
    ∃ (V : Submodule k B) (d : ℕ) (b : Basis (Fin d) k V)
      (hV : letI := (bialgebra e).toCoalgebra
        ∀ (f : Module.Dual k B) (v : B), v ∈ V → rightAct f v ∈ V),
      Intertwines ρ
        ((regularRepresentation e (Field.toIsField k) V b hV).tensor
          (trivial (Corepresented.groupScheme F e) n))
        (coefficientEmbedding e ρ V b) ∧
      Function.Injective (coefficientEmbedding e ρ V b).mulVecLin := by
  classical
  let := (bialgebra e).toCoalgebra
  let S : Finset B := Finset.univ.image
    (fun ij : n × n => Unipotent.universalMatrix e ρ ij.1 ij.2)
  let V := regularSpan (K := k) S
  have hV : ∀ (f : Module.Dual k B) (v : B), v ∈ V → rightAct f v ∈ V :=
    fun f _ hv => rightAct_mem_regularSpan S f hv
  have hN : ∀ i j, Unipotent.universalMatrix e ρ i j ∈ V := by
    intro i j
    apply subset_regularSpan S
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩
  exact ⟨V, Module.finrank k V, Module.finBasis k V, hV,
    intertwines_coefficientEmbedding e ρ V (Module.finBasis k V) hV hN,
    coefficientEmbedding_injective e ρ V (Module.finBasis k V) hN⟩

end Actual

end Langlands.GroupScheme.Chevalley

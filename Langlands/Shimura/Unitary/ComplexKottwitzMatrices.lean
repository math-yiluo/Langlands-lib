import Langlands.Shimura.Unitary.ComplexCocharacterMatrices

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra Module
open scoped CategoryTheory.MonObj TensorProduct Classical
attribute [local instance 1100] Algebra.toModule

namespace Langlands.Shimura.ComplexMatrix

variable (S : Type*) [CommRing S] (n r : ℕ)

/-- The ordered split diagonal is an algebra homomorphism. -/
def splitDiagonalAlgHom : S × S →ₐ[S]
    Matrix (Fin n) (Fin n) S × Matrix (Fin n) (Fin n) S :=
  ((Matrix.diagonalAlgHom (n := Fin n) (α := S) S).comp
    (AlgHom.pi (fun i : Fin n => if i.val < r then AlgHom.snd S S S else
      AlgHom.fst S S S))).prod
    ((Matrix.diagonalAlgHom (n := Fin n) (α := S) S).comp
      (AlgHom.pi (fun i : Fin n => if i.val < r then AlgHom.fst S S S else
        AlgHom.snd S S S)))

@[simp] theorem splitDiagonalAlgHom_apply (p : S × S) :
    splitDiagonalAlgHom S n r p = splitDiagonal S n r p := by
  simp only [splitDiagonalAlgHom, splitDiagonal, AlgHom.prod_apply, AlgHom.comp_apply,
    Matrix.diagonalAlgHom_apply]
  apply Prod.ext <;> change Matrix.diagonal _ = Matrix.diagonal _
  all_goals congr 1; funext i; simp only [AlgHom.pi_apply]
  all_goals split_ifs <;> rfl

/-- Two scalar units give the corresponding pair of invertible diagonal matrices. -/
def splitDiagonalUnits : Sˣ × Sˣ →*
    (Matrix (Fin n) (Fin n) S × Matrix (Fin n) (Fin n) S)ˣ :=
  (Units.map (splitDiagonalAlgHom S n r).toMonoidHom).comp
    MulEquiv.prodUnits.symm.toMonoidHom

@[simp] theorem splitDiagonalUnits_val (p : Sˣ × Sˣ) :
    (splitDiagonalUnits S n r p : Matrix (Fin n) (Fin n) S ×
      Matrix (Fin n) (Fin n) S) = splitDiagonal S n r ((p.1 : S), (p.2 : S)) :=
  splitDiagonalAlgHom_apply S n r _

end Langlands.Shimura.ComplexMatrix

namespace Langlands.Shimura.AlgebraInvolution.ComplexHom

variable {A : Type*} [Ring A] [Algebra ℝ A] {σ : AlgebraInvolution ℝ A}
  (h : ComplexHom σ) (S : Type*) [CommRing S] [Algebra ℝ S]

/-- Conjugating the original complex homomorphism conjugates the quadratic variable only. -/
theorem conj_deligneAlgebraMap (q : DeligneTorus.Complexification S) :
    h.conj.deligneAlgebraMap S q = h.deligneAlgebraMap S (star q) := by
  simp [deligneAlgebraMap_apply, Complex.conj_I, TensorProduct.tmul_neg,
    TensorProduct.neg_tmul]

end Langlands.Shimura.AlgebraInvolution.ComplexHom

namespace Langlands.Shimura.HarrisSignatureCharts

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {σ : SecondKindInvolution E K A} {n : ℕ}
  {Φ : (E →+* ℝ) → (K →+* ℂ)} (C : HarrisSignatureCharts σ n Φ)
  {κ : Type} [Fintype κ] (b : Basis κ E A)
  (S : Type*) [CommRing S] [Algebra ℂ S] [Algebra ℝ S] [IsScalarTower ℝ ℂ S]

/-- The conjugate Harris homomorphism interchanges the two split scalar coordinates. -/
theorem conj_delignePoints_matrix (q : DeligneTorus.Points S) (τ : E →+* ℝ) :
    C.iteratedScalarMatrixEquiv b S
        ((((C.realComplexHom b).conj.delignePoints S q).val.1) :
          S ⊗[ℝ] (ℝ ⊗[ℚ] A)) τ =
      ComplexMatrix.splitDiagonal S n (if τ = C.distinguished then n - 1 else n)
        (((DeligneTorus.splitPointsEquiv S q).2 : S),
         ((DeligneTorus.splitPointsEquiv S q).1 : S)) := by
  change C.iteratedScalarMatrixEquiv b S
    ((C.realComplexHom b).conj.deligneAlgebraMap S q) τ = _
  rw [AlgebraInvolution.ComplexHom.conj_deligneAlgebraMap,
    C.deligneAlgebraMap_matrix, DeligneTorus.splitEquiv_star]
  rfl

/-- Inversion after conjugation gives the inverse units in the opposite split order. -/
theorem conj_inverse_delignePoints_matrix (q : DeligneTorus.Points S) (τ : E →+* ℝ) :
    C.iteratedScalarMatrixEquiv b S
        ((((C.realComplexHom b).conj.delignePoints S q)⁻¹).val.1 :
          S ⊗[ℝ] (ℝ ⊗[ℚ] A)) τ =
      ComplexMatrix.splitDiagonal S n (if τ = C.distinguished then n - 1 else n)
        (↑((DeligneTorus.splitPointsEquiv S q).2⁻¹),
         ↑((DeligneTorus.splitPointsEquiv S q).1⁻¹)) := by
  rw [← map_inv, C.conj_delignePoints_matrix, map_inv]
  rfl

/-- For the first factor, conjugation followed by inversion gives the pair `(1,u⁻¹)`. -/
theorem conj_inverse_delignePoints_firstFactor (u : Sˣ) (τ : E →+* ℝ) :
    C.iteratedScalarMatrixEquiv b S
        ((((C.realComplexHom b).conj.delignePoints S
          ((DeligneTorus.splitPointsEquiv S).symm (u, 1)))⁻¹).val.1 :
          S ⊗[ℝ] (ℝ ⊗[ℚ] A)) τ =
      ComplexMatrix.splitDiagonal S n (if τ = C.distinguished then n - 1 else n)
        (1, ↑(u⁻¹)) := by
  rw [C.conj_inverse_delignePoints_matrix, MulEquiv.apply_symm_apply]
  simp only [inv_one, Units.val_one]

/-- For the second factor, conjugation followed by inversion gives the pair `(u⁻¹,1)`. -/
theorem conj_inverse_delignePoints_secondFactor (u : Sˣ) (τ : E →+* ℝ) :
    C.iteratedScalarMatrixEquiv b S
        ((((C.realComplexHom b).conj.delignePoints S
          ((DeligneTorus.splitPointsEquiv S).symm (1, u)))⁻¹).val.1 :
          S ⊗[ℝ] (ℝ ⊗[ℚ] A)) τ =
      ComplexMatrix.splitDiagonal S n (if τ = C.distinguished then n - 1 else n)
        (↑(u⁻¹), 1) := by
  rw [C.conj_inverse_delignePoints_matrix, MulEquiv.apply_symm_apply]
  simp only [inv_one, Units.val_one]

end Langlands.Shimura.HarrisSignatureCharts

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

set_option backward.isDefEq.respectTransparency false in
/-- The Kottwitz cocharacter retains conjugation before inversion on every complex test scheme. -/
theorem kottwitzCocharacter_matrices (first : Bool) (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).X) (τ : E →+* ℝ) :
    D.complexPointMatrices C T (x ≫ (D.kottwitzCocharacter C first).hom.hom) τ =
      ComplexMatrix.splitDiagonal (AlgebraInvolution.complexTestAlgebra T) n
        (if τ = C.distinguished then n - 1 else n)
        (if first then (1, (↑((GroupScheme.Gm.pointsEquiv _ T x : Γ(T.left, ⊤)ˣ)⁻¹) : Γ(T.left, ⊤)))
          else ((↑((GroupScheme.Gm.pointsEquiv _ T x : Γ(T.left, ⊤)ˣ)⁻¹) : Γ(T.left, ⊤)), 1)) := by
  unfold complexPointMatrices
  rw [Category.assoc, ← Grp.comp_hom_hom, D.kottwitzCocharacter_comparison,
    AlgebraInvolution.ComplexHom.inverseCocharacter_points,
    DeligneTorus.factorCocharacter_quadratic]
  cases first
  · exact C.conj_inverse_delignePoints_secondFactor D.totallyRealBasis _ _ τ
  · exact C.conj_inverse_delignePoints_firstFactor D.totallyRealBasis _ _ τ

end Langlands.Shimura.CentralSimpleUnitaryData

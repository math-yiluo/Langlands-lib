import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal
import Langlands.GroupScheme.CorepresentedClosedSubgroup

/-! # Diagonalizing an upper triangular cocharacter by an upper triangular matrix -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Matrix Module
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

set_option backward.isDefEq.respectTransparency false

namespace CocharacterDiagonal

variable {k : Type u} [Field k] {N : ℕ} (I : Type u) [Fintype I] [DecidableEq I]

/-- If the universal matrix of a split-torus representation is upper triangular, a single
upper triangular invertible matrix diagonalizes the representation on every test algebra. -/
theorem exists_triangular_diagonalizingMatrix
    (ρ : MatrixRepresentation (splitTorus (Spec (CommRingCat.of k)) I) (Fin N))
    (hρ : (universalMatrix I ρ).val.IsUpperTriangular) :
    ∃ (B : GL (Fin N) k) (w : Fin N → (I → ℤ)),
      B ∈ blockParabolicSubgroup k (fun i => -(i.val : ℤ)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ),
        (Matrix.GeneralLinearGroup.map (algebraMap k A) B)⁻¹ *
            matrixAt I ρ t * Matrix.GeneralLinearGroup.map (algebraMap k A) B =
          diagonalMatrix
            (fun j => splitTorus.exponentValue I t (Multiplicative.ofAdd (w j))) := by
  classical
  let U : Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ)) := universalMatrix I ρ
  have hU : U.IsUpperTriangular := hρ
  have hdiag (j : Fin N) : U j j ≠ 0 := by
    have h := Matrix.isUnits_det_units (universalMatrix I ρ)
    rw [det_of_isUpperTriangular hρ] at h
    exact (IsUnit.prod_iff.1 h j (Finset.mem_univ j)).ne_zero
  have hm (j : Fin N) : ∃ m : I → ℤ, (U j j).coeff m ≠ 0 := by
    by_contra h
    push Not at h
    apply hdiag j
    have h0 : (U j j).coeff = 0 := Finsupp.ext h
    exact AddMonoidAlgebra.coeff_injective (h0.trans (AddMonoidAlgebra.coeff_zero).symm)
  choose m hm using hm
  let M : Matrix (Fin N) (Fin N) k := fun a j => coefficientColumn I ρ (m j) j a
  have hMtri : M.IsUpperTriangular := by
    intro a j hja
    change ((U a j).coeff (m j)) = 0
    rw [hU hja]
    simp
  have hMdet : M.det ≠ 0 := by
    rw [det_of_isUpperTriangular hMtri]
    exact Finset.prod_ne_zero_iff.2 fun j _ => hm j
  let B : GL (Fin N) k := Matrix.GeneralLinearGroup.mkOfDetNeZero M hMdet
  have hB (a j : Fin N) : (B : Matrix (Fin N) (Fin N) k) a j = coefficientColumn I ρ (m j) j a :=
    rfl
  refine ⟨B, m, (mem_blockParabolicSubgroup k _).2 fun a j haj => ?_, ?_⟩
  · apply hMtri
    change (j : ℕ) < a
    simp only [neg_lt_neg_iff, Nat.cast_lt] at haj
    exact haj
  intro A _ _ t
  let C := Matrix.GeneralLinearGroup.map (algebraMap k A) B
  let D := diagonalMatrix
    (fun j => splitTorus.exponentValue I t (Multiplicative.ofAdd (m j)))
  have hc : matrixAt I ρ t * C = C * D := by
    apply Units.ext
    ext a j
    have hj := congrFun (coefficientColumn_weight I ρ t (m j) j) a
    change ((matrixAt I ρ t : Matrix (Fin N) (Fin N) A) * (C : Matrix (Fin N) (Fin N) A)) a j =
      ((C : Matrix (Fin N) (Fin N) A) * Matrix.diagonal
        (fun r => (splitTorus.exponentValue I t (Multiplicative.ofAdd (m r)) : A))) a j
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, C, Matrix.GeneralLinearGroup.map_apply, hB]
    simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_comm] using hj
  change C⁻¹ * matrixAt I ρ t * C = D
  rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]

variable {R : CommRingCat.{u}} {n : Type} [Fintype n] [DecidableEq n]

/-- The entries of a point of `GL_n` over an affine test vanish exactly where those of its
affine matrix do. -/
theorem affinePointsEquiv_apply_eq_zero {S : CommAlgCat.{u} R}
    (x : (algSpec R).obj (op S) ⟶ (groupScheme n R).X) {i j : n}
    (h : (pointsEquiv n R _ x : Matrix n n Γ(((algSpec R).obj (op S)).left, ⊤)) i j = 0) :
    (affinePointsEquiv n R S x : Matrix n n S) i j = 0 := by
  have hinv : ∀ a : S, (Corepresented.affineSectionsIso S).hom.hom
      ((Corepresented.affineSectionsIso S).inv.hom a) = a := fun a =>
    congrArg (fun f : S ⟶ S => f.hom a) (Corepresented.affineSectionsIso S).inv_hom_id
  rw [pointsEquiv_eq_affinePointsEquiv, Matrix.GeneralLinearGroup.map_apply] at h
  rw [← hinv ((affinePointsEquiv n R S x : Matrix n n S) i j)]
  change (Corepresented.affineSectionsIso S).hom.hom
    ((Corepresented.affineSectionsIso S).inv.hom.toRingHom
      ((affinePointsEquiv n R S x : Matrix n n S) i j)) = 0
  rw [h, map_zero]

/-- The rational point attached to a matrix of the block parabolic subgroup lies in the block
parabolic subgroup functor. -/
theorem rationalMatrixPoint_mem_blockParabolic (e : n → ℤ) {B : GL n R}
    (hB : B ∈ blockParabolicSubgroup R e) :
    rationalMatrixPoint B ∈ (blockParabolic n R e).carrier (Over.mk (𝟙 (Spec R))) := by
  rw [mem_blockParabolic]
  intro i j hij
  rw [rationalMatrixPoint, pointsEquiv_naturality, pointsEquiv_eq_affinePointsEquiv,
    MulEquiv.apply_symm_apply, Matrix.GeneralLinearGroup.map_apply,
    Matrix.GeneralLinearGroup.map_apply]
  rw [(mem_blockParabolicSubgroup R e).1 hB i j hij, map_zero, map_zero]

end CocharacterDiagonal

/-- **Triangular diagonalization of cocharacters.** A cocharacter of `GL_N` over a field whose
points are all upper triangular is conjugate, by an upper triangular rational point, to a
diagonal cocharacter. -/
theorem exists_triangular_innerIso_comp_eq_diagonalCocharacter (k : Type u) [Field k] {N : ℕ}
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme (Fin N) (CommRingCat.of k))
    (hχ : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ (Gm (Spec (CommRingCat.of k))).X),
      t ≫ χ.hom.hom ∈ (blockParabolic (Fin N) (CommRingCat.of k)
        (fun i => -(i.val : ℤ))).carrier T) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
        (groupScheme (Fin N) (CommRingCat.of k)).X) (e : Fin N → ℤ),
      g ∈ (blockParabolic (Fin N) (CommRingCat.of k) (fun i => -(i.val : ℤ))).carrier _ ∧
      χ ≫ ((groupScheme (Fin N) (CommRingCat.of k)).innerIso g).hom =
        diagonalCocharacter (Fin N) (CommRingCat.of k) e := by
  classical
  let R := CommRingCat.of k
  let ρ : MatrixRepresentation (splitTorus (Spec R) PUnit) (Fin N) :=
    (splitTorus.gmIso (Spec R)).inv ≫ χ
  have hρ : (splitTorus.gmIso (Spec R)).hom ≫ ρ = χ := by
    dsimp only [ρ]
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have htri : (CocharacterDiagonal.universalMatrix PUnit ρ).val.IsUpperTriangular := by
    intro i j hij
    rw [CocharacterDiagonal.universalMatrix, MatrixRepresentation.affineMatrix_apply]
    apply CocharacterDiagonal.affinePointsEquiv_apply_eq_zero
    have hmem := hχ _ (splitTorus.universalPoint PUnit ≫
      (splitTorus.gmIso (Spec R)).inv.hom.hom)
    rw [Category.assoc, ← Grp.comp_hom_hom, mem_blockParabolic] at hmem
    refine hmem i j ?_
    have : (j : ℕ) < i := hij
    omega
  obtain ⟨B, w, hBtri, hw⟩ :=
    CocharacterDiagonal.exists_triangular_diagonalizingMatrix PUnit ρ htri
  refine ⟨CocharacterDiagonal.rationalMatrixPoint B⁻¹, fun j => w j PUnit.unit,
    CocharacterDiagonal.rationalMatrixPoint_mem_blockParabolic _
      (Subgroup.inv_mem _ hBtri), ?_⟩
  apply Gm.hom_ext_universalPoint R
  let A : CommAlgCat R := CommAlgCat.of R (LaurentPolynomial k)
  let x : (algSpec R).obj (op A) ⟶ (Gm (Spec R)).X := Gm.universalPoint R
  let t := splitTorus.algebraPointsEquiv PUnit (LaurentPolynomial k)
    (x ≫ (splitTorus.gmIso (Spec R)).hom.hom.hom)
  have hm : CocharacterDiagonal.matrixAt PUnit ρ t =
      affinePointsEquiv (Fin N) R A (x ≫ χ.hom.hom) := by
    dsimp only [CocharacterDiagonal.matrixAt, t]
    rw [MulEquiv.symm_apply_apply, MatrixRepresentation.affineMatrix_apply, Category.assoc]
    change affinePointsEquiv (Fin N) R A
      (x ≫ ((splitTorus.gmIso (Spec R)).hom ≫ ρ).hom.hom) = _
    rw [hρ]
  have ht : t = fun _ => Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom x :=
    CocharacterDiagonal.algebraPointsEquiv_comp_gmIso x
  apply (affinePointsEquiv (Fin N) R A).injective
  change affinePointsEquiv (Fin N) R A
      ((x ≫ χ.hom.hom) ≫
        ((groupScheme (Fin N) R).innerIso
          (CocharacterDiagonal.rationalMatrixPoint B⁻¹)).hom.hom.hom) = _
  rw [comp_innerIso_hom, map_mul, map_mul, map_inv,
    CocharacterDiagonal.affinePointsEquiv_constant_rationalMatrixPoint,
    CocharacterDiagonal.affinePointsEquiv_diagonalCocharacter]
  simp only [map_inv, inv_inv]
  have h := hw (LaurentPolynomial k) t
  rw [hm] at h
  rw [ht] at h
  simpa [A, x, R, splitTorus.exponentValue, CocharacterDiagonal.diagonalMatrix,
    diagonalUnits, MonoidHom.pi] using h

end Langlands.GroupScheme.GeneralLinear

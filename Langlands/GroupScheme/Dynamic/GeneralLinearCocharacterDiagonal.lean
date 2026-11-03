import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.Torus.TranslatedUniversalPoint
import Langlands.GroupScheme.Dynamic.GeneralLinear
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.AffineTestComparison
import Langlands.GroupScheme.Torus.GmEndomorphismsProof
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Basis

/-! # Diagonalization of cocharacters of the general linear group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Matrix Module
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace CocharacterDiagonal

variable {R : CommRingCat.{u}} {n : Type} [Fintype n] [DecidableEq n]
variable (I : Type u) [Fintype I] [DecidableEq I]
variable (ρ : MatrixRepresentation (splitTorus (Spec R) I) n)

/-- Matrix of a split-torus representation at its universal point. -/
def universalMatrix : GL n (AddMonoidAlgebra R (I → ℤ)) :=
  ρ.affineMatrix _ (splitTorus.universalPoint I)

/-- The column vector at one exponent in the universal matrix. -/
def coefficientColumn (m : I → ℤ) (j : n) : n → R :=
  fun i => ((universalMatrix I ρ : Matrix n n (AddMonoidAlgebra R (I → ℤ))) i j).coeff m

variable {A : Type u} [CommRing A] [Algebra R A]

omit [DecidableEq I] in
private theorem affineMatrix_map {B : Type u} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B)
    (x : (algSpec R).obj (op (CommAlgCat.of R A)) ⟶ (splitTorus (Spec R) I).X) :
    ρ.affineMatrix _ (Lie.affineMap _ f x) =
      Matrix.GeneralLinearGroup.map f.toRingHom (ρ.affineMatrix _ x) :=
  ρ.affineMatrix_naturality (CommAlgCat.ofHom f) x

/-- The matrix of a representation at the torus point with specified unit coordinates. -/
def matrixAt (t : I → Aˣ) : GL n A :=
  ρ.affineMatrix (CommAlgCat.of R A) ((splitTorus.algebraPointsEquiv I A).symm t)

/-- The universal matrix under translation by an arbitrary algebra-valued point. -/
theorem universalMatrix_translated (t : I → Aˣ) :
    Matrix.GeneralLinearGroup.map (splitTorus.translatedEvaluation I t).toRingHom
        (universalMatrix I ρ) =
      Matrix.GeneralLinearGroup.map (algebraMap A (AddMonoidAlgebra A (I → ℤ)))
          (matrixAt I ρ t) *
        Matrix.GeneralLinearGroup.map
          (AddMonoidAlgebra.mapAlgHom (I → ℤ) (Algebra.ofId R A)).toRingHom
          (universalMatrix I ρ) := by
  rw [universalMatrix, ← affineMatrix_map]
  rw [splitTorus.universalPoint_translatedEvaluation, map_mul]
  rw [affineMatrix_map, affineMatrix_map]
  rfl

omit [Fintype I] [DecidableEq I] in
private theorem coeff_constant_mul (a : A) (p : AddMonoidAlgebra A (I → ℤ))
    (m : I → ℤ) :
    (algebraMap A (AddMonoidAlgebra A (I → ℤ)) a * p).coeff m = a * p.coeff m :=
  AddMonoidAlgebra.coeff_single_zero_mul p a m

omit [Fintype I] [DecidableEq I] [DecidableEq n] in
private theorem coeff_sum_univ (f : n → AddMonoidAlgebra A (I → ℤ)) (m : I → ℤ) :
    (∑ b, f b).coeff m = ∑ b, (f b).coeff m := by
  change (AddMonoidAlgebra.coeffAddEquiv (∑ b, f b)) m = _
  simp only [map_sum, AddMonoidAlgebra.coeffAddEquiv_apply]
  exact Finsupp.finsetSum_apply _ _ _

/-- Every universal coefficient column is a weight vector after every coefficient extension. -/
theorem coefficientColumn_weight (t : I → Aˣ) (m : I → ℤ) (j : n) :
    (matrixAt I ρ t : Matrix n n A) *ᵥ
        (fun a => algebraMap R A (coefficientColumn I ρ m j a)) =
      (splitTorus.exponentValue I t (Multiplicative.ofAdd m) : A) •
        (fun a => algebraMap R A (coefficientColumn I ρ m j a)) := by
  funext a
  have h := congrArg
    (fun M : GL n (AddMonoidAlgebra A (I → ℤ)) => (M.val a j).coeff m)
    (universalMatrix_translated I ρ t)
  change (splitTorus.translatedEvaluation I t
      ((universalMatrix I ρ : Matrix n n (AddMonoidAlgebra R (I → ℤ))) a j)).coeff m =
    (∑ b, algebraMap A (AddMonoidAlgebra A (I → ℤ)) ((matrixAt I ρ t : Matrix n n A) a b) *
      AddMonoidAlgebra.mapAlgHom (I → ℤ) (Algebra.ofId R A)
        ((universalMatrix I ρ : Matrix n n (AddMonoidAlgebra R (I → ℤ))) b j)).coeff m at h
  simp only [coeff_sum_univ, coeff_constant_mul,
    AddMonoidAlgebra.coeff_mapAlgHom, splitTorus.coeff_translatedEvaluation] at h
  change (∑ b, (matrixAt I ρ t : Matrix n n A) a b *
      algebraMap R A
        (((universalMatrix I ρ : Matrix n n (AddMonoidAlgebra R (I → ℤ))) b j).coeff m)) =
    (splitTorus.exponentValue I t (Multiplicative.ofAdd m) : A) *
      algebraMap R A
        (((universalMatrix I ρ : Matrix n n (AddMonoidAlgebra R (I → ℤ))) a j).coeff m)
  exact h.symm.trans (mul_comm _ _)

/-- The universal matrix evaluates at the identity torus point to the identity matrix. -/
theorem universalMatrix_evaluateOne :
    Matrix.GeneralLinearGroup.map
        (splitTorus.evaluateUnits (R := R) I (fun _ => (1 : Rˣ))).toRingHom
        (universalMatrix I ρ) = 1 := by
  rw [universalMatrix, ← affineMatrix_map]
  rw [splitTorus.universalPoint_evaluateUnits]
  have ht : (splitTorus.algebraPointsEquiv (R := R) I R).symm
      (fun _ => (1 : Rˣ)) = 1 := map_one _
  rw [ht, map_one]

omit [DecidableEq I] in
private theorem evaluateOne_eq_sum (p : AddMonoidAlgebra R (I → ℤ)) :
    splitTorus.evaluateUnits (R := R) I (fun _ => (1 : Rˣ)) p =
      ∑ m ∈ p.coeff.support, p.coeff m := by
  simp [splitTorus.evaluateUnits, AddMonoidAlgebra.lift_apply', Finsupp.sum,
    splitTorus.exponentValue]

/-- Universal coefficient columns span the original finite free module. -/
theorem span_coefficientColumn :
    Submodule.span R (Set.range (fun q : (I → ℤ) × n => coefficientColumn I ρ q.1 q.2)) =
      ⊤ := by
  classical
  apply top_unique
  rw [← (Pi.basisFun R n).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  let U : Matrix n n (AddMonoidAlgebra R (I → ℤ)) := universalMatrix I ρ
  let s : Finset (I → ℤ) := Finset.univ.biUnion (fun a : n => (U a j).coeff.support)
  have hsum : ∑ m ∈ s, coefficientColumn I ρ m j = Pi.basisFun R n j := by
    funext a
    have h := congrArg (fun M : GL n R => (M : Matrix n n R) a j)
      (universalMatrix_evaluateOne I ρ)
    change splitTorus.evaluateUnits (R := R) I (fun _ => (1 : Rˣ)) (U a j) =
      (1 : Matrix n n R) a j at h
    rw [evaluateOne_eq_sum] at h
    simp only [Finset.sum_apply, coefficientColumn]
    change ∑ m ∈ s, (U a j).coeff m = (Pi.basisFun R n j) a
    have hs : (U a j).coeff.support ⊆ s := by
      intro m hm
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hm⟩
    calc
      ∑ m ∈ s, (U a j).coeff m = ∑ m ∈ (U a j).coeff.support, (U a j).coeff m := by
        symm
        apply Finset.sum_subset hs
        intro m _ hm
        exact Finsupp.notMem_support_iff.mp hm
      _ = (Pi.basisFun R n j) a := by
        simpa only [Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm] using h
  rw [← hsum]
  exact Submodule.sum_mem _ (fun m _ =>
    Submodule.subset_span (Set.mem_range_self (m, j)))

variable {k : Type u} [Field k]

/-- The invertible diagonal matrix with the specified diagonal units. -/
def diagonalMatrix (t : n → Aˣ) : GL n A :=
  Units.map (Matrix.diagonalRingHom n A).toMonoidHom (MulEquiv.piUnits.symm t)

@[simp] theorem coe_diagonalMatrix (t : n → Aˣ) :
    (diagonalMatrix t : Matrix n n A) = Matrix.diagonal (fun j => (t j : A)) := rfl

/-- Over a field one can select a basis consisting of universal coefficient columns. -/
theorem exists_coefficientBasis
    (ρ : MatrixRepresentation (splitTorus (Spec (CommRingCat.of k)) I) n) :
    ∃ (b : Basis n k (n → k)) (q : n → ((I → ℤ) × n)),
      ∀ j, b j = coefficientColumn I ρ (q j).1 (q j).2 := by
  classical
  let S := Set.range (fun q : (I → ℤ) × n => coefficientColumn I ρ q.1 q.2)
  have hs : ⊤ ≤ Submodule.span k S := by
    rw [show Submodule.span k S = ⊤ from span_coefficientColumn I ρ]
  let b' := Basis.ofSpan hs
  let e := b'.indexEquiv (Pi.basisFun k n)
  let b := b'.reindex e
  have hb (j : n) : b j ∈ S := by
    apply Basis.ofSpan_subset hs
    exact ⟨e.symm j, (b'.reindex_apply e j).symm⟩
  choose q hq using hb
  exact ⟨b, q, fun j => (hq j).symm⟩

/-- A single invertible matrix diagonalizes the representation on every test algebra. -/
theorem exists_diagonalizingMatrix
    (ρ : MatrixRepresentation (splitTorus (Spec (CommRingCat.of k)) I) n) :
    ∃ (B : GL n k) (w : n → (I → ℤ)),
      ∀ (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ),
        (Matrix.GeneralLinearGroup.map (algebraMap k A) B)⁻¹ *
            matrixAt I ρ t * Matrix.GeneralLinearGroup.map (algebraMap k A) B =
          diagonalMatrix
            (fun j => splitTorus.exponentValue I t (Multiplicative.ofAdd (w j))) := by
  classical
  obtain ⟨b, q, hb⟩ := exists_coefficientBasis I ρ
  let std := Pi.basisFun k n
  let B : GL n k :=
    ⟨std.toMatrix b, b.toMatrix std,
      std.toMatrix_mul_toMatrix_flip b, b.toMatrix_mul_toMatrix_flip std⟩
  have hB (a j : n) : (B : Matrix n n k) a j = b j a := by
    simp [B, Basis.toMatrix_apply, std]
  refine ⟨B, fun j => (q j).1, ?_⟩
  intro A _ _ t
  let C := Matrix.GeneralLinearGroup.map (algebraMap k A) B
  let D := diagonalMatrix
    (fun j => splitTorus.exponentValue I t (Multiplicative.ofAdd (q j).1))
  have hc : matrixAt I ρ t * C = C * D := by
    apply Units.ext
    ext a j
    have hj := congrFun (coefficientColumn_weight I ρ t (q j).1 (q j).2) a
    simp only [← hb j] at hj
    change ((matrixAt I ρ t : Matrix n n A) * (C : Matrix n n A)) a j =
      ((C : Matrix n n A) * Matrix.diagonal
        (fun r => (splitTorus.exponentValue I t (Multiplicative.ofAdd (q r).1) : A))) a j
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, C, Matrix.GeneralLinearGroup.map_apply, hB]
    change (∑ r, (matrixAt I ρ t : Matrix n n A) a r *
        algebraMap k A (b j r)) =
      algebraMap k A (b j a) *
        (splitTorus.exponentValue I t (Multiplicative.ofAdd (q j).1) : A)
    simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_comm] using hj
  change C⁻¹ * matrixAt I ρ t * C = D
  rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]

end CocharacterDiagonal

namespace CocharacterDiagonal

variable {R : CommRingCat.{u}} {n : Type} [Fintype n] [DecidableEq n]

private def baseTestIso :
    Over.mk (𝟙 (Spec R)) ≅ (algSpec R).obj (op (CommAlgCat.of R R)) :=
  Gm.affineTestIso _ _ (by
    change 𝟙 (Spec R) = Spec.map (𝟙 R)
    exact (Spec.map_id R).symm)

/-- The actual base point associated to an invertible matrix over the base ring. -/
def rationalMatrixPoint (B : GL n R) : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme n R).X :=
  baseTestIso.hom ≫ (affinePointsEquiv n R (CommAlgCat.of R R)).symm B

theorem affinePointsEquiv_constant_rationalMatrixPoint
    (B : GL n R) (A : CommAlgCat.{u} R) :
    affinePointsEquiv n R A
        ((groupScheme n R).constantPoint (rationalMatrixPoint B) ((algSpec R).obj (op A))) =
      Matrix.GeneralLinearGroup.map (algebraMap R A) B := by
  have hb : Over.homMk ((algSpec R).obj (op A)).hom (by simp) ≫ baseTestIso.hom =
      (algSpec R).map (CommAlgCat.ofHom (Algebra.ofId R A)).op := by
    apply Over.OverMorphism.ext
    simp [baseTestIso, Gm.affineTestIso]
    rfl
  rw [constantPoint, rationalMatrixPoint, ← Category.assoc, hb,
    affinePointsEquiv_naturality, MulEquiv.apply_symm_apply]
  rfl

private theorem map_pointsEquiv (A : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op A) ⟶ (groupScheme n R).X) :
    Matrix.GeneralLinearGroup.map (Corepresented.affineSectionsIso A).hom.hom.toRingHom
        (pointsEquiv n R _ x) = affinePointsEquiv n R A x := by
  rw [pointsEquiv_eq_affinePointsEquiv]
  apply Units.ext
  ext i j
  exact congrArg (fun f : A ⟶ A => f.hom ((affinePointsEquiv n R A x : Matrix n n A) i j))
    (Corepresented.affineSectionsIso A).inv_hom_id

theorem affinePointsEquiv_diagonalCocharacter (e : n → ℤ) (A : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op A) ⟶ (Gm (Spec R)).X) :
    affinePointsEquiv n R A (x ≫ (diagonalCocharacter n R e).hom.hom) =
      diagonalUnits A e (Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom x) := by
  rw [← map_pointsEquiv, pointsEquiv_diagonalCocharacter]
  rw [Corepresented.affineSectionsIso_hom_ringHom]
  erw [map_diagonalUnits]
  rfl

theorem algebraPointsEquiv_comp_gmIso
    {A : Type u} [CommRing A] [Algebra R A]
    (x : Lie.AffinePoints (Gm (Spec R)).toGrp A) :
    splitTorus.algebraPointsEquiv PUnit A
        (x ≫ (splitTorus.gmIso (Spec R)).hom.hom.hom) =
      fun _ => Gm.affinePointsEquiv ((algSpec R).obj (op (CommAlgCat.of R A))).hom x := by
  funext j
  apply Units.ext
  have hp : splitTorus.pointsEquiv PUnit _ (x ≫ (splitTorus.gmIso (Spec R)).hom.hom.hom) j =
      Gm.pointsEquiv (Spec R) _ x := by
    rw [splitTorus.gmIso, isoOfPointModels_hom]
    · rfl
    · intro T T' a y
      funext i
      change Gm.pointsEquiv (Spec R) _ (a ≫ y) = _
      rw [Gm.pointsEquiv_naturality]
      rfl
    · exact fun a y => splitTorus.pointsEquiv_naturality PUnit a y
  exact congrArg
    (fun a : Γ(Spec (CommRingCat.of A), ⊤)ˣ =>
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom a.val) hp

end CocharacterDiagonal

/-- Every cocharacter of a general linear group over a field is conjugate by a point over
that field to a diagonal cocharacter. -/
theorem exists_innerIso_comp_eq_diagonalCocharacter (k : Type u) [Field k]
    {n : Type} [Fintype n] [DecidableEq n]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme n (CommRingCat.of k)) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
        (groupScheme n (CommRingCat.of k)).X) (e : n → ℤ),
      χ ≫ ((groupScheme n (CommRingCat.of k)).innerIso g).hom =
        diagonalCocharacter n (CommRingCat.of k) e := by
  classical
  let R := CommRingCat.of k
  let ρ : MatrixRepresentation (splitTorus (Spec R) PUnit) n :=
    (splitTorus.gmIso (Spec R)).inv ≫ χ
  have hρ : (splitTorus.gmIso (Spec R)).hom ≫ ρ = χ := by
    dsimp only [ρ]
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  obtain ⟨B, w, hw⟩ := CocharacterDiagonal.exists_diagonalizingMatrix PUnit ρ
  refine ⟨CocharacterDiagonal.rationalMatrixPoint B⁻¹, fun j => w j PUnit.unit, ?_⟩
  apply Gm.hom_ext_universalPoint R
  let A : CommAlgCat R := CommAlgCat.of R (LaurentPolynomial k)
  let x : (algSpec R).obj (op A) ⟶ (Gm (Spec R)).X := Gm.universalPoint R
  let t := splitTorus.algebraPointsEquiv PUnit (LaurentPolynomial k)
    (x ≫ (splitTorus.gmIso (Spec R)).hom.hom.hom)
  have hm : CocharacterDiagonal.matrixAt PUnit ρ t =
      affinePointsEquiv n R A (x ≫ χ.hom.hom) := by
    dsimp only [CocharacterDiagonal.matrixAt, t]
    rw [MulEquiv.symm_apply_apply, MatrixRepresentation.affineMatrix_apply, Category.assoc]
    change affinePointsEquiv n R A
      (x ≫ ((splitTorus.gmIso (Spec R)).hom ≫ ρ).hom.hom) = _
    rw [hρ]
  have ht : t = fun _ => Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom x :=
    CocharacterDiagonal.algebraPointsEquiv_comp_gmIso x
  apply (affinePointsEquiv n R A).injective
  change affinePointsEquiv n R A
      ((x ≫ χ.hom.hom) ≫
        ((groupScheme n R).innerIso
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

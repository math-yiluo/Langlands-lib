import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaRepresentationProof
import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaWeightMultiplicity
import Langlands.GroupScheme.SimplyConnected.NormOneMatrixRepresentation
import Langlands.GroupScheme.MatrixRepresentation.Reindex

/-! # The norm-one chart of the orthogonal Morita comparison -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Matrix
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 1000

namespace Langlands.GroupScheme.Quaternionic.OrthogonalMorita

open DegreeSplitting Langlands.CentralSimple Langlands.ReducedNorm
open CentralSimpleUnits.SplitRepresentation

variable {K D L : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [Field L] [Algebra K L]
  {I κ : Type} [Fintype I] [DecidableEq I] [Fintype κ] [DecidableEq κ]
  (e : L ⊗[K] D ≃ₐ[L] Matrix I I L)
  {n : ℕ} (P : Matrix (Fin n ⊕ Fin n) (κ × I) L)
  (P' : Matrix (κ × I) (Fin n ⊕ Fin n) L)
  (hPP' : P * P' = 1) (hP'P : P' * P = 1)

/-- The algebra splitting chart obtained by the same change of basis as the
orthogonal Morita comparison. -/
def conjugatedChart : L ⊗[K] Matrix κ κ D ≃ₐ[L]
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L := by
  let C : Matrix (κ × I) (κ × I) L ≃ₐ[L] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L :=
    { toFun := fun x => P * x * P'
      invFun := fun x => P' * x * P
      left_inv := fun x => by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P' P, hP'P, Matrix.one_mul, Matrix.mul_one]
      right_inv := fun x => by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P P', hPP', Matrix.one_mul, Matrix.mul_one]
      map_mul' := fun x y => by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P' P, hP'P, Matrix.one_mul]
      map_add' := fun x y => by rw [Matrix.mul_add, Matrix.add_mul]
      commutes' := fun l => by
        simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.mul_one, hPP'] }
  exact (matrixChartL e).trans C

@[simp] theorem conjugatedChart_apply (x : L ⊗[K] Matrix κ κ D) :
    conjugatedChart e P P' hPP' hP'P x = P * matrixChartL e x * P' := rfl

/-- Extending the conjugated chart gives the original Morita matrix on all
coefficient algebras, with the indicated reindexing. -/
theorem splittingMap_conjugatedChart {J : Type} [Fintype J] [DecidableEq J]
    (r : (Fin n ⊕ Fin n) ≃ J)
    (R : Type u) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]
    (x : R ⊗[K] Matrix κ κ D) :
    splittingMap ((conjugatedChart e P P' hPP' hP'P).trans (Matrix.reindexAlgEquiv L L r)) R x =
      (conjugatedMatrix e R P P' x).submatrix r.symm r.symm := by
  induction x using TensorProduct.inductionOn with
  | tmul s a =>
    rw [splittingMap_tmul]
    change s • ((P * matrixChartL e ((1 : L) ⊗ₜ[K] a) * P').submatrix r.symm r.symm).map
      (algebraMap L R) = _
    rw [conjugatedMatrix, ← splittingMap_matrixChartL, splittingMap_tmul]
    change s • ((P * matrixChartL e ((1 : L) ⊗ₜ[K] a) * P').map
      (algebraMap L R)).submatrix r.symm r.symm = _
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  | add x y hx hy =>
    rw [_root_.map_add, hx, hy]
    simp only [conjugatedMatrix, _root_.map_add, Matrix.mul_add, Matrix.add_mul]
    rfl

end Langlands.GroupScheme.Quaternionic.OrthogonalMorita

namespace Langlands.GroupScheme.CentralSimpleUnits.SplitRepresentation

open Langlands.AlgebraicGeometry.PointTopology Langlands.CentralSimple Langlands.ReducedNorm

attribute [local instance] Splitting.sectionsAlgebra Splitting.sectionsScalarTower

variable {K A L : Type u} [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
  [Algebra.IsCentral K A] [IsSimpleRing A] [Field L] [Algebra K L]
  (e : L ⊗[K] A ≃ₐ[L]
    Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L)

/-- The split norm-one column matrix on an affine test is the extended chart
of the original algebra unit. -/
theorem representation_affineMatrix_val (R : Type u) [CommRing R] [Algebra K R]
    [Algebra L R] [IsScalarTower K L R]
    (x : ((GroupScheme.baseChange (Spec.algebraMap K L)).obj
      (normOne K A)).affinePoints (CommAlgCat.of (CommRingCat.of L) R)) :
    ((representation K A e).affineMatrix (CommAlgCat.of (CommRingCat.of L) R) x :
      Matrix _ _ R) = splittingMap e R
        (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K A)
          (CommAlgCat.of (CommRingCat.of K) R)
          ((affinePointsBaseChangeMulEquiv K L R (normOne K A)).symm x ≫
            (normOneι K A).hom.hom)).val := by
  let S := CommAlgCat.of (CommRingCat.of L) R
  let U := CommAlgCat.of (CommRingCat.of K) R
  let T := ringTest L R
  let x₀ := (affinePointsBaseChangeMulEquiv K L R (normOne K A)).symm x
  let y : ringTest K R ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K A)).X :=
    x₀ ≫ (normOneι K A).hom.hom
  let I := ringTestRestrictScalarsIso K L R
  have hx : baseChangePointsEquiv (Spec.algebraMap K L) (normOne K A) T x = I.hom ≫ x₀ := by
    apply Over.OverMorphism.ext
    simp only [baseChangePointsEquiv_left, x₀, affinePointsBaseChangeMulEquiv_symm_left,
      I, Over.comp_left, ringTestRestrictScalarsIso_hom_left]
    exact (Category.id_comp _).symm
  let a : Splitting.coefficients (K := K) T →ₐ[K] R :=
    (Corepresented.affineSectionsIso U).hom.hom.comp ((algΓ (CommRingCat.of K)).map I.inv).unop.hom
  have ha : ∀ l : L, a (algebraMap L _ l) = algebraMap L R l := by
    intro l
    change (Corepresented.affineSectionsIso U).hom.hom
      (I.inv.left.appTop (algebraMap L (Splitting.coefficients (K := K) T) l)) = _
    rw [show I.inv.left = 𝟙 _ from ringTestRestrictScalarsIso_inv_left K L R, Scheme.Hom.id_appTop]
    have hl := (Corepresented.affineSectionsIso S).hom.hom.commutes l
    change (Corepresented.affineSectionsIso S).hom.hom.toRingHom
      (algebraMap L (Splitting.coefficients (K := K) T) l) = _ at hl
    change (Corepresented.affineSectionsIso U).hom.hom.toRingHom _ = _
    rw [Corepresented.affineSectionsIso_hom_ringHom] at hl ⊢
    exact hl
  have hy := Corepresented.map_affineSectionsIso_pointsEquiv
    (FiniteAlgebraUnits.functor K A)
    (FiniteAlgebraUnits.corepresentableBy (Module.finBasis K A)) U y
  have hcoef : Algebra.TensorProduct.map a (AlgHom.id K A)
      (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) _ (I.hom ≫ y)).val =
        (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K A) U y).val := by
    have h₀ := FiniteAlgebraUnits.pointsEquiv_naturality (Module.finBasis K A) I.inv (I.hom ≫ y)
    rw [Iso.inv_hom_id_assoc] at h₀
    have h₁ := congrArg Units.val h₀
    change (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) _ y).val =
      Algebra.TensorProduct.map ((algΓ (CommRingCat.of K)).map I.inv).unop.hom
        (AlgHom.id K A) (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) _ (I.hom ≫ y)).val at h₁
    let g := Algebra.TensorProduct.map (Corepresented.affineSectionsIso U).hom.hom (AlgHom.id K A)
    let u := (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) _ (I.hom ≫ y)).val
    have hcomp : Algebra.TensorProduct.map a (AlgHom.id K A) =
        g.comp (Algebra.TensorProduct.map ((algΓ (CommRingCat.of K)).map I.inv).unop.hom
          (AlgHom.id K A)) :=
      Algebra.TensorProduct.map_comp (Corepresented.affineSectionsIso U).hom.hom
        ((algΓ (CommRingCat.of K)).map I.inv).unop.hom (AlgHom.id K A) (AlgHom.id K A)
    have hcomp' := DFunLike.congr_fun hcomp u
    exact hcomp'.trans ((congrArg g h₁.symm).trans (congrArg Units.val hy))
  have hmatrix := representation_pointMatrix_val K A e T x
  rw [hx, normOnePointsEquiv_val, Category.assoc] at hmatrix
  change ((representation K A e).pointMatrix T x : Matrix _ _ Γ(T.left, ⊤)) =
    splittingMap e _ (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) _ (I.hom ≫ y)).val at hmatrix
  rw [← hcoef, Splitting.splittingMap_naturality K A e a ha, ← hmatrix]
  have hpm := MatrixRepresentation.pointMatrix_eq_affineMatrix (representation K A e) S x
  erw [hpm]
  ext i j
  change _ = a ((Corepresented.affineSectionsIso S).inv.hom
    (((representation K A e).affineMatrix S x : Matrix _ _ R) i j))
  change _ = (Corepresented.affineSectionsIso U).hom.hom
    ((ringTestRestrictScalarsIso K L R).inv.left.appTop
      ((Corepresented.affineSectionsIso S).inv.hom
        (((representation K A e).affineMatrix S x : Matrix _ _ R) i j)))
  rw [ringTestRestrictScalarsIso_inv_left, Scheme.Hom.id_appTop]
  change _ = (Corepresented.affineSectionsIso U).hom.hom.toRingHom
    ((Corepresented.affineSectionsIso S).inv.hom.toRingHom _)
  rw [Corepresented.affineSectionsIso_hom_ringHom, Corepresented.affineSectionsIso_inv_ringHom]
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id _).symm

end Langlands.GroupScheme.CentralSimpleUnits.SplitRepresentation

namespace Langlands.GroupScheme.Quaternionic.OrthogonalMorita

open Langlands.CentralSimple CentralSimpleUnits.SplitRepresentation

variable {K D L : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D] [Field L] [Algebra K L]
  {m degree n : ℕ} [NeZero m]
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin degree) (Fin degree) L)
  (σ : FirstKindInvolution K D)
  (hσ : Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2)
  (q : σ.QuadraticForms (Fin m))
  (P : Matrix (Fin n ⊕ Fin n) (Fin m × Fin degree) L)
  (P' : Matrix (Fin m × Fin degree) (Fin n ⊕ Fin n) L)
  (hPP' : P * P' = 1) (hP'P : P' * P = 1)
  (hPQ : OrthogonalMatrix.IsAlt (P * DegreeSplitting.splitGram e σ (Quotient.out q) * Pᵀ -
    OrthogonalMatrix.formMatrix (Fin n) L))
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]

local notation "A" => Matrix (Fin m) (Fin m) D
local notation "b" => Spec.algebraMap K L

/-- An orthogonal morphism factored through the norm-one group of the underlying
matrix algebra has the split orthogonal column representation in the same
hyperbolic basis. -/
def NormOneChartOrthogonalStatement
    (r : (Fin n ⊕ Fin n) ≃ Fin (reducedDegree K A))
    (j : G ⟶ σ.isometryGroup q) (f : G ⟶ CentralSimpleUnits.normOne K A)
    : Prop :=
    f ≫ CentralSimpleUnits.normOneι K A = j ≫ σ.isometryGroupι q →
    (representation K A ((conjugatedChart e P P' hPP' hP'P).trans
      (Matrix.reindexAlgEquiv L L r))).restrict ((GroupScheme.baseChange b).map f) =
    ((MatrixRepresentation.restrict (OrthogonalMatrix.inclusion (Fin n) (CommRingCat.of L))
      ((GroupScheme.baseChange b).map j ≫
        (splittingUnitComparison e σ hσ q P P' hPP' hP'P hPQ).groupIso.hom)).reindex r)

theorem normOneChart_eq_orthogonal
    (r : (Fin n ⊕ Fin n) ≃ Fin (reducedDegree K A))
    (j : G ⟶ σ.isometryGroup q) (f : G ⟶ CentralSimpleUnits.normOne K A) :
    NormOneChartOrthogonalStatement e σ hσ q P P' hPP' hP'P hPQ r j f := by
  intro hf
  let G_L := (GroupScheme.baseChange b).obj G
  let : IsAffine G_L.X.left := by
    change IsAffine (Limits.pullback G.X.hom b)
    infer_instance
  apply AffinePointComparison.hom_ext G_L
  intro S x
  let : Algebra K S := Algebra.compHom S (algebraMap K L)
  let : IsScalarTower K L S := IsScalarTower.of_algebraMap_eq' rfl
  apply (GeneralLinear.affinePointsEquiv _ _ S).injective
  apply Units.ext
  let z := (affinePointsBaseChangeMulEquiv K L S G).symm x
  let c := splittingUnitComparison e σ hσ q P P' hPP' hP'P hPQ
  let x' := x ≫ ((GroupScheme.baseChange b).map f).hom.hom
  let chart := (conjugatedChart e P P' hPP' hP'P).trans (Matrix.reindexAlgEquiv L L r)
  change ((MatrixRepresentation.affineMatrix (representation K A chart) S x' :
    Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) S)) =
    ((MatrixRepresentation.reindex (MatrixRepresentation.restrict
      (OrthogonalMatrix.inclusion (Fin n) (CommRingCat.of L))
      ((GroupScheme.baseChange b).map j ≫ c.groupIso.hom)) r).affineMatrix S x : Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) S)
  have hxf : x' = affinePointsBaseChangeMulEquiv K L S _ (z ≫ f.hom.hom) := by
    rw [affinePointsBaseChangeMulEquiv_comp, MulEquiv.apply_symm_apply]
  have hxj : x ≫ ((GroupScheme.baseChange b).map j).hom.hom =
      affinePointsBaseChangeMulEquiv K L S _ (z ≫ j.hom.hom) := by
    rw [affinePointsBaseChangeMulEquiv_comp, MulEquiv.apply_symm_apply]
  have hy : (z ≫ f.hom.hom) ≫ (CentralSimpleUnits.normOneι K A).hom.hom =
      (z ≫ j.hom.hom) ≫ (σ.isometryGroupι q).hom.hom := by
    simp only [Category.assoc, ← Grp.comp_hom_hom, hf]
  rw [representation_affineMatrix_val, hxf, MulEquiv.symm_apply_apply, hy,
    MatrixRepresentation.reindex_affineMatrix, MatrixRepresentation.reindexGL_val,
    MatrixRepresentation.affineMatrix_restrict, Grp.comp_hom_hom, ← Category.assoc, hxj]
  change Langlands.ReducedNorm.splittingMap chart S _ =
    (MatrixRepresentation.affineMatrix (OrthogonalMatrix.inclusion (Fin n) (CommRingCat.of L))
      S (splitPoint σ q c.groupIso S (z ≫ j.hom.hom)) : Matrix _ _ S).submatrix r.symm r.symm
  rw [c.affineMatrix_splitPoint, OrthogonalMatrix.coe_toGL]
  let S₀ := CommAlgCat.of (CommRingCat.of K) S
  let a := z ≫ j.hom.hom
  let v := isometryAffineUnitsEquiv σ q S₀ a
  have hv : (c.equiv S v : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) S) =
      conjugatedMatrix e S P P' v.val :=
    coe_splitUnitsEquiv e σ (by simpa using hσ) S P P' (Quotient.out q) hPP' hP'P hPQ v
  rw [hv]
  have hu : v.val = σ.isometryAffineUnitsOver q S₀ a := coe_isometryAffineUnitsEquiv σ q S₀ a
  rw [hu]
  exact splittingMap_conjugatedChart e P P' hPP' hP'P r S _

end Langlands.GroupScheme.Quaternionic.OrthogonalMorita

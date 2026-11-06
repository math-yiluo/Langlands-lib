import Langlands.GroupScheme.SpecialLinearBinaryCovariant
import Langlands.GroupScheme.Reductive.BinaryHomogeneousSteinberg
import Langlands.GroupScheme.Reductive.InvariantLinearForm
import Langlands.GroupScheme.FlagCoreTorus
import Langlands.Representation.CuspidalSupport.AssociationReduction

/-! # The actual regular representation on the entire binary covariant space -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.SpecialLinear.BinaryUpper

variable {k : Type u} [Field k]

local instance : IsAffine (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X.left :=
  SpecialLinear.isAffine_groupScheme _ _

local instance : IsAffineHom (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X.hom :=
  SpecialLinear.isAffineHom_groupScheme _ _

local instance : IsAffine (groupScheme (CommRingCat.of k)).X.left :=
  isAffine_groupScheme _

local instance : IsAffineHom (groupScheme (CommRingCat.of k)).X.hom :=
  isAffineHom_groupScheme _

/-- Affine matrix points commute with extension of the test algebra. -/
theorem matrixPoint_map {S T : Type u} [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (φ : S →ₐ[k] T)
    (g : Matrix.SpecialLinearGroup (Fin 2) S) :
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom φ).op ≫ matrixPoint g =
      matrixPoint (Matrix.SpecialLinearGroup.map φ.toRingHom g) := by
  apply (affinePointsEquiv (Fin 2) (CommRingCat.of k) (CommAlgCat.of _ T)).injective
  unfold SpecialLinear.affinePointsEquiv
  erw [Corepresented.affinePointsEquiv_naturality]
  exact congrArg (Matrix.SpecialLinearGroup.map φ.toRingHom)
    ((affinePointsEquiv (Fin 2) (CommRingCat.of k) (CommAlgCat.of _ S)).apply_symm_apply g)
    |>.trans ((affinePointsEquiv (Fin 2) (CommRingCat.of k) (CommAlgCat.of _ T)).apply_symm_apply _).symm

open HomogeneousPolynomial

/-- The monomial basis, transported to the entire actual covariant coordinate space. -/
def covariantBasis (m : ℕ) : Module.Basis (Fin (m + 1)) k
    (AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
      (characterCoordinate k ^ m)) :=
  (binaryBasis m).map (covariantRowEquiv m)

@[simp] theorem covariantBasis_coe (m : ℕ) (c : Fin (m + 1)) :
    (covariantBasis (k := k) m c : AffineCoordinates.algebra
      (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k))) =
      coordinateAlgEquiv (Fin 2) k (homogeneousRowMap m 1 (binaryBasis m c)) := rfl

/-- The actual finite regular representation on the entire covariant space. -/
def covariantRegularRepresentation (m : ℕ) :
    MatrixRepresentation (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k))
      (Fin (m + 1)) :=
  Chevalley.affineRegularRepresentation _ _ (covariantBasis m)
    (fun ψ _ hb => AffineCoordinates.rightAct_mem_leftCovariantSubspace
      (inclusion (CommRingCat.of k)) (characterCoordinate k ^ m) ψ hb)

/-- Matrix multiplication classifies multiplication of affine scheme points. -/
theorem matrixPoint_mul {S : Type u} [CommRing S] [Algebra k S]
    (g h : Matrix.SpecialLinearGroup (Fin 2) S) :
    matrixPoint (k := k) (g * h) = matrixPoint g * matrixPoint h :=
  map_mul (affinePointsEquiv (Fin 2) (CommRingCat.of k) (CommAlgCat.of _ S)).symm g h

/-- The point matrix at a scalar extension is the scalar extension of the base matrix. -/
theorem covariantRegularRepresentation_pointMatrix_map (m : ℕ)
    {S : Type u} [CommRing S] [Algebra k S]
    (g : Matrix.SpecialLinearGroup (Fin 2) k) (i j : Fin (m + 1)) :
    ((covariantRegularRepresentation m).pointMatrix _
        (matrixPoint (k := k) (Matrix.SpecialLinearGroup.map (algebraMap k S) g)) :
      Matrix (Fin (m + 1)) (Fin (m + 1))
        Γ(((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) S))).left, ⊤))
        i j =
      (Corepresented.affineSectionsIso (CommAlgCat.of (CommRingCat.of k) S)).inv.hom
        (algebraMap k S
          (((covariantRegularRepresentation m).affineMatrix
            (CommAlgCat.of (CommRingCat.of k) k) (matrixPoint g) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) k) i j)) := by
  rw [MatrixRepresentation.pointMatrix_eq_affineMatrix]
  change (Corepresented.affineSectionsIso (CommAlgCat.of (CommRingCat.of k) S)).inv.hom
      ((((covariantRegularRepresentation m).affineMatrix
        (CommAlgCat.of (CommRingCat.of k) S)
        (matrixPoint (Matrix.SpecialLinearGroup.map (algebraMap k S) g))) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) S) i j) = _
  erw [← matrixPoint_map (Algebra.ofId k S),
    MatrixRepresentation.affineMatrix_naturality]
  rfl

set_option maxHeartbeats 800000 in
/-- The actual finite regular matrix expands right translation of each row monomial. -/
theorem rightTranslation_binaryBasis (m : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) k) (j : Fin (m + 1)) :
    rightTranslation g (homogeneousRowMap m 1 (binaryBasis m j)) =
      ∑ i, (((covariantRegularRepresentation m).affineMatrix
        (CommAlgCat.of (CommRingCat.of k) k) (matrixPoint (k := k) g) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) k) i j) •
        homogeneousRowMap m 1 (binaryBasis m i) := by
  let C := CoordinateRing (Fin 2) k
  let S := CommAlgCat.of (CommRingCat.of k) C
  let T := (algSpec (CommRingCat.of k)).obj (op S)
  let ε := (Corepresented.affineSectionsAlgEquiv S).symm
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) ((algΓ (CommRingCat.of k)).obj T).unop :=
    ((covariantRegularRepresentation m).pointMatrix T
      (matrixPoint (k := k) (Matrix.SpecialLinearGroup.map (algebraMap k C) g)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T.left, ⊤))
  have he := Chevalley.affineRegularRepresentation_mul_basis
    (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k))
    _ (covariantBasis m)
    (fun ψ _ hb => AffineCoordinates.rightAct_mem_leftCovariantSubspace
      (inclusion (CommRingCat.of k)) (characterCoordinate k ^ m) ψ hb)
    T (matrixPoint (k := k) (universal (Fin 2) k))
    (matrixPoint (k := k) (Matrix.SpecialLinearGroup.map (algebraMap k C) g)) j
  rw [← matrixPoint_mul] at he
  dsimp only [T, S] at he
  simp only [covariantBasis_coe] at he
  change AffineCoordinates.pointAlgebraHom
      (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) T
      (matrixPoint (k := k) (universal (Fin 2) k *
        Matrix.SpecialLinearGroup.map (algebraMap k C) g))
      (coordinateAlgEquiv (Fin 2) k (homogeneousRowMap m 1 (binaryBasis m j))) =
    ∑ i, AffineCoordinates.pointAlgebraHom
        (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) T
        (matrixPoint (k := k) (universal (Fin 2) k))
        (coordinateAlgEquiv (Fin 2) k (homogeneousRowMap m 1 (binaryBasis m i))) *
      M i j at he
  erw [pointAlgebraHom_matrixPoint] at he
  have hsum :
      (∑ i, AffineCoordinates.pointAlgebraHom
        (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) T
        (matrixPoint (k := k) (universal (Fin 2) k))
        (coordinateAlgEquiv (Fin 2) k (homogeneousRowMap m 1 (binaryBasis m i))) *
      M i j) =
      ∑ i, ε (homogeneousRowMap m 1 (binaryBasis m i)) *
        ε (algebraMap k C (((covariantRegularRepresentation m).affineMatrix
          (CommAlgCat.of (CommRingCat.of k) k) (matrixPoint (k := k) g) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) k) i j)) := by
    apply Finset.sum_congr rfl
    intro i _
    erw [pointAlgebraHom_matrixPoint]
    change ε ((classify (universal (Fin 2) k))
      (homogeneousRowMap m 1 (binaryBasis m i))) * M i j = _
    have hM : M i j = ε (algebraMap k C
        (((covariantRegularRepresentation m).affineMatrix
          (CommAlgCat.of (CommRingCat.of k) k) (matrixPoint (k := k) g) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) k) i j)) :=
      covariantRegularRepresentation_pointMatrix_map m g i j
    rw [hM]
    rw [classify_universal]
    rfl
  rw [hsum] at he
  apply ε.injective
  change ε (classify (universal (Fin 2) k *
    Matrix.SpecialLinearGroup.map (algebraMap k C) g)
      (homogeneousRowMap m 1 (binaryBasis m j))) = _
  rw [map_sum]
  simp only [map_smul, Algebra.smul_def]
  calc
    _ = ∑ i, ε (homogeneousRowMap m 1 (binaryBasis m i)) *
        ε (algebraMap k C (((covariantRegularRepresentation m).affineMatrix
          (CommAlgCat.of (CommRingCat.of k) k) (matrixPoint (k := k) g) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) k) i j)) := he
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [ε.commutes]
      exact mul_comm _ _

/-- The actual regular matrix on the full covariant space is the binary substitution matrix. -/
theorem covariantRegularRepresentation_affineMatrix (m : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) k) :
    ((covariantRegularRepresentation m).affineMatrix
      (CommAlgCat.of (CommRingCat.of k) k) (matrixPoint (k := k) g) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      binaryMatrixRepresentation m g := by
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
    (covariantRegularRepresentation m).affineMatrix
      (CommAlgCat.of (CommRingCat.of k) k) (matrixPoint (k := k) g)
  have h (j : Fin (m + 1)) :
      specialLinearRepresentation m g (binaryBasis m j) =
        ∑ i, M i j • binaryBasis m i := by
    apply binaryHomogeneousRowMap_injective m
    rw [homogeneousRowMap_intertwining, rightTranslation_binaryBasis]
    simp only [map_sum, map_smul]
    rfl
  ext i j
  rw [binaryMatrixRepresentation_apply]
  change M i j = (binaryBasis m).repr
    (specialLinearRepresentation m g (binaryBasis m j)) i
  rw [h]
  simp [Finsupp.single_apply]

/-- Rational points of the actual binary special-linear scheme are determinant-one matrices. -/
def rationalPointsEquiv :
    (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X) ≃*
        Matrix.SpecialLinearGroup (Fin 2) k where
  toFun x := affinePointsEquiv (Fin 2) (CommRingCat.of k) (CommAlgCat.of _ k)
    (FlagCore.baseAffineTestIso.inv ≫ x)
  invFun g := FlagCore.baseAffineTestIso.hom ≫ matrixPoint (k := k) g
  left_inv x := by
    simp only [matrixPoint, MulEquiv.symm_apply_apply, Iso.hom_inv_id_assoc]
  right_inv g := by
    simp only [Iso.inv_hom_id_assoc, matrixPoint, MulEquiv.apply_symm_apply]
  map_mul' x y := by
    rw [MonObj.comp_mul, map_mul]

/-- The rational matrix is the binary substitution matrix under the actual point equivalence. -/
theorem covariantRegularRepresentation_rationalMatrix (m : ℕ)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X) :
    ((covariantRegularRepresentation m).rationalMatrix x :
      Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
        binaryMatrixRepresentation m (rationalPointsEquiv x) := by
  obtain ⟨g, rfl⟩ := (rationalPointsEquiv (k := k)).symm.surjective x
  rw [MulEquiv.apply_symm_apply]
  change ((covariantRegularRepresentation m).rationalMatrix
    (FlagCore.baseAffineTestIso.hom ≫ matrixPoint (k := k) g) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) k) = _
  rw [
    FlagCore.rationalMatrix_baseAffineTestIso, covariantRegularRepresentation_affineMatrix]

/-- The regular representation at rational points agrees with the full binary action. -/
theorem covariantRegularRepresentation_rationalRepresentation (m : ℕ) :
    (covariantRegularRepresentation (k := k) m).rationalRepresentation =
      (binaryRepresentation m).comp (rationalPointsEquiv (k := k)).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  apply LinearMap.ext
  intro v
  change ((covariantRegularRepresentation m).rationalMatrix x :
    Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ v =
      binaryMatrixRepresentation m (rationalPointsEquiv x) *ᵥ v
  rw [covariantRegularRepresentation_rationalMatrix]

/-- Steinberg irreducibility holds on the entire actual upper-covariant coordinate space. -/
theorem covariantRegularRepresentation_isIrreducible (p : ℕ) [Fact p.Prime]
    [CharP k p] [Infinite k] (s : ℕ) :
    (covariantRegularRepresentation (k := k) (p ^ s - 1)).rationalRepresentation.IsIrreducible := by
  rw [covariantRegularRepresentation_rationalRepresentation]
  exact (Langlands.CuspidalSupport.isIrreducible_comp_mulEquiv_iff
    (binaryRepresentation (R := k) (p ^ s - 1)) (rationalPointsEquiv (k := k))).2
      (binaryRepresentation_isIrreducible (k := k) p s)

end Langlands.GroupScheme.SpecialLinear.BinaryUpper

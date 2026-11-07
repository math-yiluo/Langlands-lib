import Langlands.GroupScheme.Rational.RootActionWeights
import Langlands.GroupScheme.Rational.TraceClassFunctions
import Langlands.GroupScheme.Rational.SteinbergRestriction
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Finite polynomial matrices of actual Steinberg products -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Polynomial

namespace Langlands.GroupScheme

namespace MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) n)

/-- A common strict degree bound for all entries of the actual additive matrix. -/
def degreeBound : ℕ :=
  (Finset.univ.sup fun i : n =>
    Finset.univ.sup fun j : n => (univariateMatrix ρ i j).natDegree) + 1

theorem natDegree_lt_degreeBound (i j : n) :
    (univariateMatrix ρ i j).natDegree < degreeBound ρ := by
  apply Nat.lt_succ_of_le
  exact (Finset.le_sup (f := fun j : n => (univariateMatrix ρ i j).natDegree)
    (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun i : n =>
        Finset.univ.sup fun j : n => (univariateMatrix ρ i j).natDegree)
          (Finset.mem_univ i))

/-- The actual additive matrix is its finite coefficient expansion over every algebra. -/
theorem affineMatrix_eq_sum (A : CommAlgCat.{u} k) (c : A) :
    (ρ.affineMatrix A
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => c)) :
      Matrix n n A) =
        ∑ m ∈ Finset.range (degreeBound ρ),
          c ^ m • (coefficientMatrix ρ m).map (algebraMap k A) := by
  rw [← univariateMatrix_aeval]
  ext i j
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    coefficientMatrix]
  change Polynomial.eval₂ (algebraMap k A) c (univariateMatrix ρ i j) = _
  rw [Polynomial.eval₂_eq_sum_range' (algebraMap k A)
    (natDegree_lt_degreeBound ρ i j) c]
  apply Finset.sum_congr rfl
  intro m hm
  exact mul_comm _ _

/-- The actual action on a scalar-extended vector is the finite divided-power sum. -/
theorem affineMatrix_mulVec_eq_sum (A : CommAlgCat.{u} k) (c : A) (v : n → k) :
    (ρ.affineMatrix A
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => c)) :
      Matrix n n A) *ᵥ (fun i => algebraMap k A (v i)) =
        ∑ m ∈ Finset.range (degreeBound ρ),
          c ^ m • (fun i => algebraMap k A (dividedPower ρ m v i)) := by
  rw [affineMatrix_eq_sum, Matrix.sum_mulVec]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Matrix.smul_mulVec, dividedPower_eq_toLin]
  congr 1
  funext i
  exact ((algebraMap k A).map_mulVec (coefficientMatrix ρ m) v i).symm

/-- All coefficients beyond the common degree bound vanish. -/
theorem coefficientMatrix_eq_zero_of_degreeBound_le {m : ℕ}
    (hm : degreeBound ρ ≤ m) : coefficientMatrix ρ m = 0 := by
  ext i j
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    ((natDegree_lt_degreeBound ρ i j).trans_le hm)

end MatrixRepresentation.AdditiveDividedPowers

namespace VectorGroup

variable {R : CommRingCat.{u}} {r : ℕ}

/-- Affine parameters agree with global-section coordinates in every dimension. -/
theorem coordinates_affinePoint (A : CommAlgCat.{u} R) (c : Fin r → A) :
    (coordinates R r ((algSpec R).obj (op A)) (affinePoint A c)).toAdd =
      fun j => (Scheme.ΓSpecIso (CommRingCat.of A)).inv (c j) := by
  change (Corepresented.pointsEquiv (functor R r) (corepresentableBy R r) _ _).toAdd = _
  rw [Corepresented.pointsEquiv_eq_affinePointsEquiv, affinePointsEquiv_affinePoint]
  rfl

/-- The universal affine parameter is the identity point of affine space. -/
@[simp] theorem affinePoint_X :
    affinePoint (coordinateAlgebra R r) (fun j => MvPolynomial.X j) = 𝟙 _ := by
  apply points_ext
  intro j
  rw [coordinates_affinePoint, coordinates_apply]
  rfl

end VectorGroup

namespace SplitPinning

open MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {r : ℕ}
    (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations)
    (s : p.SimpleReflectionRepresentatives)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)

/-- The ordered product of the actual root polynomial matrices and representative matrices. -/
def steinbergPolynomialMatrix : Matrix n n (MvPolynomial (Fin r) k) :=
  (List.ofFn fun j : Fin r =>
    ((univariateMatrix (ρ.restrict (x (e j)).hom)).map
        (Polynomial.aeval (MvPolynomial.X j))) *
      ((ρ.rationalMatrix (s (e j)).point : Matrix n n k).map MvPolynomial.C)).prod

/-- The actual matrix at an affine Steinberg point has the ordered root-factor formula. -/
theorem affineMatrix_steinbergProduct (A : CommAlgCat.{u} k) (c : Fin r → A) :
    (ρ.affineMatrix A
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := r) A c ≫
          steinbergProduct e x s) :
      Matrix n n A) =
      (List.ofFn fun j : Fin r =>
        ((ρ.restrict (x (e j)).hom).affineMatrix A
            (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A
              (fun _ => c j)) : Matrix n n A) *
          ((ρ.rationalMatrix (s (e j)).point : Matrix n n k).map (algebraMap k A))).prod := by
  let F := (Units.coeHom (Matrix n n A)).comp (ρ.affineMatrix A)
  change F _ = _
  rw [comp_steinbergProduct, map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  dsimp only [Function.comp_def, F, MonoidHom.comp_apply, Units.coeHom_apply]
  rw [map_mul, Units.val_mul]
  rw [congrFun (VectorGroup.coordinates_affinePoint
    (R := CommRingCat.of k) A c) j]
  have hn : CategoryTheory.SemiCartesianMonoidalCategory.toUnit
      ((algSpec (CommRingCat.of k)).obj (op A)) ≫ (s (e j)).point =
        G.constantPoint (s (e j)).point ((algSpec (CommRingCat.of k)).obj (op A)) := rfl
  rw [hn, ρ.affineMatrix_constantPoint]
  congr 1
  rw [NormalizedRootParametrization.point, ← VectorGroup.affinePoint_eq_scalarPoint]
  rfl

/-- Polynomial evaluation recovers the actual ordered-product matrix over every algebra. -/
theorem steinbergPolynomialMatrix_aeval (A : CommAlgCat.{u} k) (c : Fin r → A) :
    (steinbergPolynomialMatrix e x s ρ).map (MvPolynomial.aeval c) =
      (ρ.affineMatrix A
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := r) A c ≫
          steinbergProduct e x s) : Matrix n n A) := by
  rw [affineMatrix_steinbergProduct, steinbergPolynomialMatrix]
  change (MvPolynomial.aeval c).mapMatrix (List.ofFn _).prod = _
  rw [map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  dsimp only [Function.comp_def]
  rw [map_mul]
  congr 1
  · rw [← univariateMatrix_aeval]
    ext i l
    change (MvPolynomial.aeval c)
      (Polynomial.aeval (MvPolynomial.X j)
        (univariateMatrix (ρ.restrict (x (e j)).hom) i l)) =
      Polynomial.aeval (c j) (univariateMatrix (ρ.restrict (x (e j)).hom) i l)
    rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
  · ext i l
    exact MvPolynomial.aeval_C c _

/-- The polynomial matrix is the actual matrix on the universal Steinberg point. -/
theorem steinbergPolynomialMatrix_eq_affineMatrix :
    steinbergPolynomialMatrix e x s ρ =
      (ρ.affineMatrix (VectorGroup.coordinateAlgebra (CommRingCat.of k) r)
        (steinbergProduct e x s) :
          Matrix n n (MvPolynomial (Fin r) k)) := by
  have h := steinbergPolynomialMatrix_aeval e x s ρ
    (VectorGroup.coordinateAlgebra (CommRingCat.of k) r) MvPolynomial.X
  rw [VectorGroup.affinePoint_X (R := CommRingCat.of k) (r := r),
    Category.id_comp] at h
  simpa only [MvPolynomial.aeval_X_left, AlgHom.coe_id, Matrix.map_id] using h

/-- Restriction of the actual trace class function is the trace of the ordered polynomial matrix. -/
theorem steinbergRestriction_traceClassFunction :
    steinbergRestriction e x s (ρ.traceClassFunction) =
      Matrix.trace (steinbergPolynomialMatrix e x s ρ) := by
  change Lie.pointCoordinates G (steinbergProduct e x s) (ρ.traceClassFunction).val = _
  rw [ρ.traceClassFunction_evaluate, steinbergPolynomialMatrix_eq_affineMatrix]

end SplitPinning
end Langlands.GroupScheme

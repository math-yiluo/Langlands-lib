import Langlands.GroupScheme.SpecialLinearBinaryUpper
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Affine chart restrictions of binary upper-covariant coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.SpecialLinear.BinaryUpper

local instance slAffine (k : Type u) [Field k] :
    IsAffine (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X.left :=
  SpecialLinear.isAffine_groupScheme _ _

local instance slAffineHom (k : Type u) [Field k] :
    IsAffineHom (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X.hom :=
  SpecialLinear.isAffineHom_groupScheme _ _

local instance upperAffine (k : Type u) [Field k] :
    IsAffine (groupScheme (CommRingCat.of k)).X.left :=
  isAffine_groupScheme _

local instance upperAffineHom (k : Type u) [Field k] :
    IsAffineHom (groupScheme (CommRingCat.of k)).X.hom :=
  isAffineHom_groupScheme _

section AffineEvaluation

variable {k : Type u} [Field k]
variable {S : Type u} [CommRing S] [Algebra k S]

/-- The affine scheme point classified by an ordinary determinant-one matrix. -/
def matrixPoint (g : Matrix.SpecialLinearGroup (Fin 2) S) :
    (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) S)) ⟶
      (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X :=
  (affinePointsEquiv (Fin 2) (CommRingCat.of k) (CommAlgCat.of _ S)).symm g

/-- The matrix over actual global sections is the original matrix transported by the counit. -/
theorem pointsEquiv_matrixPoint (g : Matrix.SpecialLinearGroup (Fin 2) S) :
    SpecialLinear.pointsEquiv (Fin 2) (CommRingCat.of k) _ (matrixPoint (k := k) g) =
      Matrix.SpecialLinearGroup.map
        (Corepresented.affineSectionsIso (CommAlgCat.of (CommRingCat.of k) S)).inv.hom.toRingHom
        g := by
  unfold SpecialLinear.pointsEquiv
  erw [Corepresented.pointsEquiv_eq_affinePointsEquiv]
  change Matrix.SpecialLinearGroup.map _
    ((affinePointsEquiv (Fin 2) (CommRingCat.of k) (CommAlgCat.of _ S))
      ((affinePointsEquiv (Fin 2) (CommRingCat.of k) (CommAlgCat.of _ S)).symm g)) = _
  rw [MulEquiv.apply_symm_apply]


/-- Actual coordinate evaluation on an affine matrix point is ordinary specialization,
followed by the spectrum counit. -/
theorem pointAlgebraHom_matrixPoint (g : Matrix.SpecialLinearGroup (Fin 2) S)
    (F : CoordinateRing (Fin 2) k) :
    AffineCoordinates.pointAlgebraHom
        (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) _
        (matrixPoint (k := k) g) (coordinateAlgEquiv (Fin 2) k F) =
      (Corepresented.affineSectionsIso (CommAlgCat.of (CommRingCat.of k) S)).inv.hom
        (classify g F) := by
  rw [pointAlgebraHom_coordinateAlgEquiv, matrixPoint, affinePointsEquiv_symm_apply]
  rw [Adjunction.homEquiv_counit]
  change ((Corepresented.affineSectionsIso (coordinateAlgebra (Fin 2) (CommRingCat.of k))).inv ≫
    ((algΓ (CommRingCat.of k)).map
      ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (classify g)).op)).unop).hom F = _
  rw [Corepresented.affineSectionsIso_inv_naturality]
  rfl

/-- Tensor covariance for the actual subgroup implies the corresponding identity over
every commutative test algebra, without reducedness assumptions. -/
theorem classify_leftCovariant (m : ℕ) (F : CoordinateRing (Fin 2) k)
    (hF : coordinateAlgEquiv (Fin 2) k F ∈
      AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
        (characterCoordinate k ^ m))
    (a g : Matrix.SpecialLinearGroup (Fin 2) S) (ha : a 1 0 = 0) :
    classify (a * g) F = a 1 1 ^ m * classify g F := by
  let T := (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) S))
  have ha' : matrixPoint (k := k) a ∈
      (SubgroupFunctor.range (inclusion (CommRingCat.of k))).carrier T := by
    rw [mem_range_inclusion, pointsEquiv_matrixPoint]
    change (Corepresented.affineSectionsIso (CommAlgCat.of (CommRingCat.of k) S)).inv.hom
      (a 1 0) = 0
    rw [ha, map_zero]
  obtain ⟨h, hh⟩ := SubgroupFunctor.mem_range.mp ha'
  have e := AffineCoordinates.pointAlgebraHom_leftCovariant
    (inclusion (CommRingCat.of k)) (characterCoordinate k ^ m) hF T h
      (matrixPoint (k := k) g)
  rw [hh] at e
  have hmul : matrixPoint (k := k) (a * g) = matrixPoint a * matrixPoint g :=
    map_mul (affinePointsEquiv (Fin 2) (CommRingCat.of k) (CommAlgCat.of _ S)).symm a g
  rw [← hmul, pointAlgebraHom_matrixPoint, map_pow,
    pointAlgebraHom_characterCoordinate, hh, pointsEquiv_matrixPoint,
    pointAlgebraHom_matrixPoint] at e
  apply AffineCoordinates.counit_unop_injective (CommAlgCat.of (CommRingCat.of k) S)
  exact e.trans (by simp only [map_mul, map_pow]; rfl)

end AffineEvaluation

section ChartMatrices

variable {S : Type u} [CommRing S]

/-- The determinant-one section above the bottom row `(t,1)`. -/
def lowerChart (t : S) : Matrix.SpecialLinearGroup (Fin 2) S :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

/-- The determinant-one section above the bottom row `(1,t)`. -/
def otherChart (t : S) : Matrix.SpecialLinearGroup (Fin 2) S :=
  ⟨!![0, -1; 1, t], by simp [Matrix.det_fin_two]⟩

end ChartMatrices

section Restriction

variable {k : Type u} [Field k]

/-- Restriction of determinant-one coordinates to the affine chart `(t,1)`. -/
def lowerRestriction : CoordinateRing (Fin 2) k →ₐ[k] Polynomial k :=
  classify (lowerChart Polynomial.X)

/-- Restriction of determinant-one coordinates to the affine chart `(1,t)`. -/
def otherRestriction : CoordinateRing (Fin 2) k →ₐ[k] Polynomial k :=
  classify (otherChart Polynomial.X)

variable {S : Type u} [CommRing S] [Algebra k S]

/-- Specialization of the chart restriction commutes with evaluation over every algebra. -/
theorem classify_lowerChart (t : S) (F : CoordinateRing (Fin 2) k) :
    classify (lowerChart t) F = Polynomial.aeval t (lowerRestriction F) := by
  have h : Matrix.SpecialLinearGroup.map (Polynomial.aeval t).toRingHom
      (lowerChart (Polynomial.X : Polynomial k)) = lowerChart t := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerChart]
  exact AlgHom.congr_fun (h ▸ classify_map (lowerChart (Polynomial.X : Polynomial k))
    (Polynomial.aeval t)) F

/-- Specialization of the other chart restriction commutes with evaluation over every algebra. -/
theorem classify_otherChart (t : S) (F : CoordinateRing (Fin 2) k) :
    classify (otherChart t) F = Polynomial.aeval t (otherRestriction F) := by
  have h : Matrix.SpecialLinearGroup.map (Polynomial.aeval t).toRingHom
      (otherChart (Polynomial.X : Polynomial k)) = otherChart t := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [otherChart]
  exact AlgHom.congr_fun (h ▸ classify_map (otherChart (Polynomial.X : Polynomial k))
    (Polynomial.aeval t)) F

/-- A covariant coordinate is determined on the open chart where the last entry is a unit. -/
theorem classify_eq_lowerRestriction (m : ℕ) (F : CoordinateRing (Fin 2) k)
    (hF : coordinateAlgEquiv (Fin 2) k F ∈
      AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
        (characterCoordinate k ^ m))
    (g : Matrix.SpecialLinearGroup (Fin 2) S) (v : Sˣ) (hv : (v : S) = g 1 1) :
    classify g F = (v : S) ^ m *
      Polynomial.aeval ((↑v⁻¹ : S) * g 1 0) (lowerRestriction F) := by
  let t : S := (↑v⁻¹ : S) * g 1 0
  let a := g * (lowerChart t)⁻¹
  have ha : a 1 0 = 0 := by
    change (g * (lowerChart t)⁻¹) 1 0 = 0
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      lowerChart, ← hv, t]
  have hd : a 1 1 = (v : S) := by
    change (g * (lowerChart t)⁻¹) 1 1 = _
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      lowerChart] using hv.symm
  have e := classify_leftCovariant m F hF a (lowerChart t) ha
  rw [show a * lowerChart t = g by dsimp [a]; simp, hd, classify_lowerChart] at e
  exact e

/-- The complementary open chart is controlled by restriction to `(1,t)`. -/
theorem classify_eq_otherRestriction (m : ℕ) (F : CoordinateRing (Fin 2) k)
    (hF : coordinateAlgEquiv (Fin 2) k F ∈
      AffineCoordinates.leftCovariantSubspace (inclusion (CommRingCat.of k))
        (characterCoordinate k ^ m))
    (g : Matrix.SpecialLinearGroup (Fin 2) S) (v : Sˣ) (hv : (v : S) = g 1 0) :
    classify g F = (v : S) ^ m *
      Polynomial.aeval ((↑v⁻¹ : S) * g 1 1) (otherRestriction F) := by
  let t : S := (↑v⁻¹ : S) * g 1 1
  let a := g * (otherChart t)⁻¹
  have ha : a 1 0 = 0 := by
    change (g * (otherChart t)⁻¹) 1 0 = 0
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      otherChart, ← hv, t]
  have hd : a 1 1 = (v : S) := by
    change (g * (otherChart t)⁻¹) 1 1 = _
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      otherChart] using hv.symm
  have e := classify_leftCovariant m F hF a (otherChart t) ha
  rw [show a * otherChart t = g by dsimp [a]; simp, hd, classify_otherChart] at e
  exact e

end Restriction

end Langlands.GroupScheme.SpecialLinear.BinaryUpper

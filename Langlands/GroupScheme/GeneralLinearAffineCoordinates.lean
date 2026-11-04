import Langlands.GroupScheme.GeneralLinear
import Langlands.GroupScheme.Dynamic.GeneralLinearStabilizer
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The general linear group scheme inside the affine space of its coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial

namespace Langlands.GroupScheme.GeneralLinear

section Space

variable (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u})

/-- The affine space over `Spec R` whose coordinates are the matrix entries and the inverse
matrix entries. -/
abbrev coordinateSpace : Over (Spec R) :=
  (algSpec R).obj (op (CommAlgCat.of R (MvPolynomial (Coordinate n) R)))

/-- The embedding of the general linear group into the affine space of its matrix and inverse
matrix entries, the spectrum of the quotient map onto the coordinate ring. -/
def toSpace : (groupScheme n R).X ⟶ coordinateSpace n R :=
  (algSpec R).map (CommAlgCat.ofHom (quotient n R)).op

theorem toSpace_left :
    (toSpace n R).left =
      Spec.map (CommRingCat.ofHom (quotient n R).toRingHom) :=
  rfl

instance isClosedImmersion_toSpace : IsClosedImmersion (toSpace n R).left := by
  rw [toSpace_left]
  exact IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.mkₐ_surjective R (ideal n R))

variable {n R}

/-- The coordinate function `κ` pulled back along a point of the general linear group is the
corresponding entry of the matrix or of its inverse. -/
theorem toSpace_appTop {T : Over (Spec R)} (w : T ⟶ (groupScheme n R).X) (κ : Coordinate n) :
    (w ≫ toSpace n R).left.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Coordinate n) R))).inv (X κ)) =
      values (pointsEquiv n R T w) κ := by
  have h : (toSpace n R).left.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Coordinate n) R))).inv (X κ)) =
        (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing n R))).inv (quotient n R (X κ)) := by
    rw [toSpace_left]
    exact (congrArg (fun f => f.hom (X κ))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (quotient n R).toRingHom))).symm
  change w.left.appTop ((toSpace n R).left.appTop
    ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Coordinate n) R))).inv (X κ))) = _
  rw [h]
  cases κ with
  | entry i j => exact (pointsEquiv_apply_apply T w i j).symm
  | inverseEntry i j => exact (pointsEquiv_inv_apply T w i j).symm

end Space

section Values

variable {n : Type} [Fintype n] [DecidableEq n] {S S' : Type u} [CommRing S] [CommRing S']

/-- An invertible matrix is determined by its coordinate values. -/
theorem values_injective : Function.Injective (values (n := n) (S := S)) := by
  intro g g' h
  apply Units.ext
  ext i j
  exact congrFun h (.entry i j)

end Values

section Conjugation

variable {n : Type} [Fintype n] [DecidableEq n]
variable {S S' : Type*} [CommRing S] [CommRing S']

/-- Conjugation of a family of coordinate values by an invertible matrix `U`: both the matrix of
entry values and the matrix of inverse entry values are conjugated by `U`. -/
def conjCoords (U : GL n S) (v : Coordinate n → S) : Coordinate n → S
  | .entry i j =>
    ((U : Matrix n n S) * Matrix.of (fun a b => v (.entry a b)) * ((U⁻¹ : GL n S) : Matrix n n S)) i j
  | .inverseEntry i j =>
    ((U : Matrix n n S) * Matrix.of (fun a b => v (.inverseEntry a b)) *
      ((U⁻¹ : GL n S) : Matrix n n S)) i j

@[simp] theorem conjCoords_entry (U : GL n S) (v : Coordinate n → S) (i j : n) :
    conjCoords U v (.entry i j) =
      ((U : Matrix n n S) * Matrix.of (fun a b => v (.entry a b)) *
        ((U⁻¹ : GL n S) : Matrix n n S)) i j :=
  rfl

@[simp] theorem conjCoords_inverseEntry (U : GL n S) (v : Coordinate n → S) (i j : n) :
    conjCoords U v (.inverseEntry i j) =
      ((U : Matrix n n S) * Matrix.of (fun a b => v (.inverseEntry a b)) *
        ((U⁻¹ : GL n S) : Matrix n n S)) i j :=
  rfl

/-- Coordinate conjugation as an `S`-linear endomorphism of the coordinate values. -/
def conjCoordsLinear (U : GL n S) : (Coordinate n → S) →ₗ[S] (Coordinate n → S) where
  toFun := conjCoords U
  map_add' v w := by
    funext κ
    cases κ with
    | entry i j =>
      simp only [conjCoords_entry, Pi.add_apply]
      rw [show (Matrix.of fun a b => v (.entry a b) + w (.entry a b)) =
        Matrix.of (fun a b => v (.entry a b)) + Matrix.of (fun a b => w (.entry a b)) from rfl,
        Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    | inverseEntry i j =>
      simp only [conjCoords_inverseEntry, Pi.add_apply]
      rw [show (Matrix.of fun a b => v (.inverseEntry a b) + w (.inverseEntry a b)) =
        Matrix.of (fun a b => v (.inverseEntry a b)) +
          Matrix.of (fun a b => w (.inverseEntry a b)) from rfl,
        Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
  map_smul' s v := by
    funext κ
    cases κ with
    | entry i j =>
      simp only [conjCoords_entry, Pi.smul_apply, RingHom.id_apply]
      rw [show (Matrix.of fun a b => s • v (.entry a b)) =
        s • Matrix.of (fun a b => v (.entry a b)) from rfl,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply]
    | inverseEntry i j =>
      simp only [conjCoords_inverseEntry, Pi.smul_apply, RingHom.id_apply]
      rw [show (Matrix.of fun a b => s • v (.inverseEntry a b)) =
        s • Matrix.of (fun a b => v (.inverseEntry a b)) from rfl,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply]

@[simp] theorem conjCoordsLinear_apply (U : GL n S) (v : Coordinate n → S) :
    conjCoordsLinear U v = conjCoords U v :=
  rfl

theorem conjCoords_add (U : GL n S) (v w : Coordinate n → S) :
    conjCoords U (v + w) = conjCoords U v + conjCoords U w :=
  (conjCoordsLinear U).map_add v w

theorem conjCoords_smul (U : GL n S) (s : S) (v : Coordinate n → S) :
    conjCoords U (s • v) = s • conjCoords U v :=
  (conjCoordsLinear U).map_smul s v

theorem conjCoords_zero (U : GL n S) : conjCoords U (0 : Coordinate n → S) = 0 :=
  (conjCoordsLinear U).map_zero

theorem conjCoords_sum {ι : Type*} (U : GL n S) (s : Finset ι) (v : ι → Coordinate n → S) :
    conjCoords U (∑ l ∈ s, v l) = ∑ l ∈ s, conjCoords U (v l) :=
  map_sum (conjCoordsLinear U) v s

/-- Conjugation of coordinates of the form `κ ↦ ∑ₗ aₗ yₗ(κ)` acts on each `yₗ`. -/
theorem conjCoords_sum_mul {ι : Type*} (U : GL n S) (s : Finset ι) (a : ι → S)
    (y : ι → Coordinate n → S) :
    conjCoords U (fun κ => ∑ l ∈ s, a l * y l κ) =
      fun κ => ∑ l ∈ s, a l * conjCoords U (y l) κ := by
  have h : (fun κ => ∑ l ∈ s, a l * y l κ) = ∑ l ∈ s, a l • y l := by
    funext κ
    simp [Finset.sum_apply, smul_eq_mul]
  rw [h, conjCoords_sum]
  funext κ
  simp [Finset.sum_apply, conjCoords_smul, smul_eq_mul]

/-- The coordinate values of a conjugate matrix are the conjugated coordinate values. -/
theorem values_conj (U g : GL n S) :
    values (U * g * U⁻¹) = conjCoords U (values g) := by
  funext κ
  cases κ with
  | entry i j => rfl
  | inverseEntry i j =>
    change ((U * g * U⁻¹)⁻¹ : GL n S) i j = _
    rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc]
    rfl

/-- Coordinate conjugation is natural in ring homomorphisms. -/
theorem conjCoords_map (φ : S →+* S') (U : GL n S) (v : Coordinate n → S) :
    conjCoords (Matrix.GeneralLinearGroup.map φ U) (φ ∘ v) = φ ∘ conjCoords U v := by
  have hinv : (((Matrix.GeneralLinearGroup.map φ U)⁻¹ : GL n S') : Matrix n n S') =
      φ.mapMatrix ((U⁻¹ : GL n S) : Matrix n n S) := by
    rw [← Matrix.GeneralLinearGroup.map_inv]
    rfl
  have hU : ((Matrix.GeneralLinearGroup.map φ U : GL n S') : Matrix n n S') =
      φ.mapMatrix (U : Matrix n n S) := rfl
  funext κ
  cases κ with
  | entry i j =>
    simp only [conjCoords_entry, Function.comp_apply, hinv, hU]
    rw [show (Matrix.of fun a b => φ (v (.entry a b))) =
      φ.mapMatrix (Matrix.of fun a b => v (.entry a b)) from rfl,
      ← map_mul, ← map_mul]
    rfl
  | inverseEntry i j =>
    simp only [conjCoords_inverseEntry, Function.comp_apply, hinv, hU]
    rw [show (Matrix.of fun a b => φ (v (.inverseEntry a b))) =
      φ.mapMatrix (Matrix.of fun a b => v (.inverseEntry a b)) from rfl,
      ← map_mul, ← map_mul]
    rfl

@[simp] theorem conjCoords_one (v : Coordinate n → S) : conjCoords (1 : GL n S) v = v := by
  funext κ
  cases κ with
  | entry i j => simp
  | inverseEntry i j => simp

theorem conjCoords_mul (U U' : GL n S) (v : Coordinate n → S) :
    conjCoords (U * U') v = conjCoords U (conjCoords U' v) := by
  funext κ
  cases κ with
  | entry i j =>
    have h : (Matrix.of fun a b => conjCoords U' v (.entry a b)) =
        (U' : Matrix n n S) * Matrix.of (fun a b => v (.entry a b)) *
          ((U'⁻¹ : GL n S) : Matrix n n S) := rfl
    rw [conjCoords_entry, conjCoords_entry, h]
    simp only [mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  | inverseEntry i j =>
    have h : (Matrix.of fun a b => conjCoords U' v (.inverseEntry a b)) =
        (U' : Matrix n n S) * Matrix.of (fun a b => v (.inverseEntry a b)) *
          ((U'⁻¹ : GL n S) : Matrix n n S) := rfl
    rw [conjCoords_inverseEntry, conjCoords_inverseEntry, h]
    simp only [mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

end Conjugation

end Langlands.GroupScheme.GeneralLinear

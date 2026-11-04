import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.Torus.FrobeniusTensorPower
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finite matrix Frobenius -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable (k : Type u) [Field k] (p : ℕ) [ExpChar k p]

/-- The characteristic-power ring map on every test algebra, including the zero ring. -/
def algebraFrobenius (A : Type u) [CommRing A] [Algebra k A] : A →+* A where
  toFun x := x ^ p
  map_one' := one_pow p
  map_zero' := zero_pow (expChar_ne_zero k p)
  map_add' x y := by
    simpa only [pow_one] using
      CocharacterDescent.add_pow_expChar_pow_of_algebra k p 1 x y
  map_mul' x y := mul_pow x y p

@[simp] theorem algebraFrobenius_apply (A : Type u) [CommRing A] [Algebra k A] (x : A) :
    algebraFrobenius k p A x = x ^ p := rfl

variable (n : Type) [Fintype n] [DecidableEq n]

/-- Entrywise characteristic power is a homomorphism of invertible matrices. -/
def frobeniusPoints (A : Type u) [CommRing A] [Algebra k A] : GL n A →* GL n A :=
  Matrix.GeneralLinearGroup.map (algebraFrobenius k p A)

@[simp] theorem frobeniusPoints_entry (A : Type u) [CommRing A] [Algebra k A]
    (g : GL n A) (i j : n) : frobeniusPoints k p n A g i j = g i j ^ p := rfl

/-- Entrywise power commutes with every change of test algebra. -/
theorem frobeniusPoints_naturality {A B : Type u} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (f : A →ₐ[k] B) (g : GL n A) :
    frobeniusPoints k p n B (Matrix.GeneralLinearGroup.map f.toRingHom g) =
      Matrix.GeneralLinearGroup.map f.toRingHom (frobeniusPoints k p n A g) := by
  apply Units.ext
  ext i j
  exact (map_pow f (g i j) p).symm

/-- The natural homomorphism on the represented functor of invertible matrices. -/
def frobeniusNat : functor n (CommRingCat.of k) ⟶ functor n (CommRingCat.of k) where
  app A := GrpCat.ofHom (frobeniusPoints k p n A)
  naturality := by
    intro A B f
    apply ConcreteCategory.hom_ext
    intro g
    exact frobeniusPoints_naturality k p n f.hom g

/-- The actual matrix Frobenius homomorphism over the fixed ground field. -/
def frobeniusHom : groupScheme n (CommRingCat.of k) ⟶ groupScheme n (CommRingCat.of k) :=
  Corepresented.groupSchemeMap (corepresentableBy n (CommRingCat.of k))
    (corepresentableBy n (CommRingCat.of k)) (frobeniusNat k p n)

/-- Matrix Frobenius on every affine test scheme is entrywise characteristic power. -/
@[simp] theorem affinePointsEquiv_frobeniusHom (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ (groupScheme n (CommRingCat.of k)).X) :
    affinePointsEquiv n (CommRingCat.of k) A (x ≫ (frobeniusHom k p n).hom.hom) =
      frobeniusPoints k p n A (affinePointsEquiv n (CommRingCat.of k) A x) :=
  Corepresented.groupSchemeMap_affinePoints _ _ _ x

/-- The algebra map fixes ground-field coefficients and raises both sets of matrix
coordinates to their characteristic powers. -/
def frobeniusCoordinates : CoordinateRing n k →ₐ[k] CoordinateRing n k :=
  classify (frobeniusPoints k p n (CoordinateRing n k) (universal n k))

@[simp] theorem frobeniusCoordinates_entry (i j : n) :
    frobeniusCoordinates k p n (quotient n k (MvPolynomial.X (Coordinate.entry i j))) =
      quotient n k (MvPolynomial.X (Coordinate.entry i j)) ^ p :=
  classify_entry _ i j

@[simp] theorem frobeniusCoordinates_inverseEntry (i j : n) :
    frobeniusCoordinates k p n (quotient n k (MvPolynomial.X (Coordinate.inverseEntry i j))) =
      quotient n k (MvPolynomial.X (Coordinate.inverseEntry i j)) ^ p := by
  rw [frobeniusCoordinates, classify_inverseEntry, ← map_inv]
  rfl

/-- The underlying scheme map is the spectrum of the explicit coordinate map. -/
theorem frobeniusHom_hom : (frobeniusHom k p n).hom.hom.left =
    Spec.map (CommRingCat.ofHom (frobeniusCoordinates k p n).toRingHom) := rfl

/-- Every matrix coordinate is integral over the characteristic-power image. -/
theorem frobeniusCoordinates_isIntegral : (frobeniusCoordinates k p n).toRingHom.IsIntegral := by
  let f := (frobeniusCoordinates k p n).toRingHom
  have hv (v : Coordinate n) : f.IsIntegralElem (quotient n k (MvPolynomial.X v)) := by
    have he : f (quotient n k (MvPolynomial.X v)) =
        quotient n k (MvPolynomial.X v) ^ p := by
      cases v with
      | entry i j => exact frobeniusCoordinates_entry k p n i j
      | inverseEntry i j => exact frobeniusCoordinates_inverseEntry k p n i j
    refine ⟨Polynomial.X ^ p - Polynomial.C (quotient n k (MvPolynomial.X v)), ?_, ?_⟩
    · exact Polynomial.leadingCoeff_X_pow_sub_C (Nat.pos_of_ne_zero (expChar_ne_zero k p))
    · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, he, sub_self]
  intro x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  change f.IsIntegralElem (quotient n k q)
  induction q using MvPolynomial.induction_on with
  | C a =>
    have he : f (quotient n k (MvPolynomial.C a)) = quotient n k (MvPolynomial.C a) :=
      (frobeniusCoordinates k p n).commutes a
    rw [← he]
    exact f.isIntegralElem_map
  | add a b ha hb =>
    rw [map_add]
    exact ha.add f hb
  | mul_X a v ha =>
    rw [map_mul]
    exact ha.mul f (hv v)

/-- The coordinate map is finite over arbitrary fields, without a perfection premise. -/
theorem frobeniusCoordinates_finite : (frobeniusCoordinates k p n).toRingHom.Finite := by
  apply (frobeniusCoordinates_isIntegral k p n).to_finite
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap k (CoordinateRing n k))
  have hcomp : (frobeniusCoordinates k p n).toRingHom.comp
      (algebraMap k (CoordinateRing n k)) = algebraMap k (CoordinateRing n k) :=
    (frobeniusCoordinates k p n).comp_algebraMap
  rw [hcomp, RingHom.finiteType_algebraMap]
  let := coordinateRing_smooth n k
  infer_instance

/-- Matrix Frobenius is a finite morphism of actual schemes. -/
theorem isFinite_frobeniusHom : IsFinite (frobeniusHom k p n).hom.hom.left := by
  change IsFinite (Spec.map (CommRingCat.ofHom (frobeniusCoordinates k p n).toRingHom))
  rw [IsFinite.SpecMap_iff]
  exact frobeniusCoordinates_finite k p n

end Langlands.GroupScheme.GeneralLinear

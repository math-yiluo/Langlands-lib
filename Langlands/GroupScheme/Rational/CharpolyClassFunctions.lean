import Langlands.GroupScheme.Rational.TraceClassFunctions
import Langlands.GroupScheme.Rational.SteinbergRestriction
import Langlands.GroupScheme.Rational.PathMiddleLine
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! # Characteristic-polynomial class functions and the hypersurface `f = 0` -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n)

/-- The `i`-th coefficient of the characteristic polynomial of the universal matrix, as an actual
regular coordinate. -/
def charpolyCoeffCoordinate (i : ℕ) : ClassFunctions.Coord G :=
  ρ.universalCharacterMatrix.charpoly.coeff i

/-- The characteristic-polynomial coefficient evaluates to the corresponding coefficient of the
characteristic polynomial of the representation matrix. -/
theorem charpolyCoeffCoordinate_evaluate {A : Type u} [CommRing A] [Algebra k A]
    (g : Lie.AffinePoints G A) (i : ℕ) :
    Lie.pointCoordinates G g (charpolyCoeffCoordinate ρ i) =
      (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A) g : Matrix n n A).charpoly.coeff i := by
  unfold charpolyCoeffCoordinate
  have h := Matrix.charpoly_map ρ.universalCharacterMatrix (Lie.pointCoordinates G g).toRingHom
  have hm := AffineCoefficients.universalCharacterMatrix_map ρ
    (CommAlgCat.of (CommRingCat.of k) A) g
  calc Lie.pointCoordinates G g (ρ.universalCharacterMatrix.charpoly.coeff i)
      = (ρ.universalCharacterMatrix.charpoly.map (Lie.pointCoordinates G g).toRingHom).coeff i :=
        (Polynomial.coeff_map _ _).symm
    _ = (ρ.universalCharacterMatrix.map (Lie.pointCoordinates G g).toRingHom).charpoly.coeff i := by
        rw [h]
    _ = _ := congrArg (fun N : Matrix n n A => N.charpoly.coeff i) hm

/-- Characteristic-polynomial coefficients are invariant under conjugation. -/
theorem charpolyCoeffCoordinate_mem (i : ℕ) :
    charpolyCoeffCoordinate ρ i ∈ ClassFunctions.algebra G := by
  apply (ClassFunctions.mem_algebra_iff_invariant G).mpr
  intro A _ _ g z
  rw [charpolyCoeffCoordinate_evaluate, charpolyCoeffCoordinate_evaluate]
  simp only [map_mul, map_inv, Units.val_mul, Matrix.coe_units_inv]
  rw [Matrix.charpoly_units_conj]

/-- The `i`-th characteristic-polynomial coefficient as an element of the actual invariant
subalgebra. -/
def charpolyCoeffClassFunction (i : ℕ) : ClassFunctions.algebra G :=
  ⟨charpolyCoeffCoordinate ρ i, charpolyCoeffCoordinate_mem ρ i⟩

@[simp] theorem charpolyCoeffClassFunction_val (i : ℕ) :
    (charpolyCoeffClassFunction ρ i).val = charpolyCoeffCoordinate ρ i := rfl

/-- The determinant of `1` minus the universal matrix, as an actual regular coordinate. -/
def detOneSubCoordinate : ClassFunctions.Coord G :=
  (1 - ρ.universalCharacterMatrix).det

/-- The coordinate `det (1 - ρ)` evaluates to `det (1 - ρ(g))`. -/
theorem detOneSubCoordinate_evaluate {A : Type u} [CommRing A] [Algebra k A]
    (g : Lie.AffinePoints G A) :
    Lie.pointCoordinates G g (detOneSubCoordinate ρ) =
      (1 - (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A) g : Matrix n n A)).det := by
  unfold detOneSubCoordinate
  have hm := AffineCoefficients.universalCharacterMatrix_map ρ
    (CommAlgCat.of (CommRingCat.of k) A) g
  change (Lie.pointCoordinates G g).toRingHom (1 - ρ.universalCharacterMatrix).det = _
  rw [RingHom.map_det, map_sub, map_one, RingHom.mapMatrix_apply]
  exact congrArg (fun N : Matrix n n A => (1 - N).det) hm

/-- The coordinate `det (1 - ρ)` is invariant under conjugation. -/
theorem detOneSubCoordinate_mem :
    detOneSubCoordinate ρ ∈ ClassFunctions.algebra G := by
  apply (ClassFunctions.mem_algebra_iff_invariant G).mpr
  intro A _ _ g z
  rw [detOneSubCoordinate_evaluate, detOneSubCoordinate_evaluate]
  simp only [map_mul, map_inv, Units.val_mul]
  set u := ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A) g
  set N := (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A) z : Matrix n n A)
  have : (1 : Matrix n n A) - u.val * N * (u⁻¹).val = u.val * (1 - N) * (u⁻¹).val := by
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv]
  rw [this, Matrix.det_units_conj]

/-- The class function `f = det (1 - ρ)`. -/
def detOneSubClassFunction : ClassFunctions.algebra G :=
  ⟨detOneSubCoordinate ρ, detOneSubCoordinate_mem ρ⟩

@[simp] theorem detOneSubClassFunction_val :
    (detOneSubClassFunction ρ).val = detOneSubCoordinate ρ := rfl

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation
open Langlands.LinearAlgebra.RootDatumPathWeights

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G}
  {d : Type} [Fintype d] [DecidableEq d] {ρ : MatrixRepresentation G d}
  (D : p.SteinbergModifiedData) {q : ℕ} (e : Fin q ≃ D.Complement)
  (x : p.NormalizedSimpleRootParametrizations)
  {L : ℕ} {β : Fin L → p.base.support} {lam : characterLattice p.torus}

/-- **`f` vanishes on `N''`.** Under the hypotheses of
`det_one_sub_steinbergModifiedPolynomialMatrix_eq_zero_of_path`, the restriction of the actual
class function `det (1 - ρ)` along the modified product `N''` is zero. -/
theorem restriction_steinbergModifiedProduct_detOneSubClassFunction_eq_zero
    (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β) (hlam : IsPathFundamental β lam)
    {i : ℕ} (hi : i + 2 ≤ L) (ha : D.a = β ⟨i, by omega⟩) (hb : D.b = β ⟨i + 1, by omega⟩)
    (hnα : D.nAlpha.point ∈
      (RelativeRoot.subgroup p.inclusion (p.rootDatum.root D.alpha)).carrier
          (Over.mk (𝟙 _)) ⊔
        (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root D.alpha)).carrier
          (Over.mk (𝟙 _)))
    {v : d → k} (hv : v ∈ p.representationWeightSpace ρ (pathWeight β lam (i + 1)))
    (hv0 : v ≠ 0) :
    ClassFunctions.restriction G
        (steinbergModifiedProduct D e x (canonicalSimpleReflectionRepresentatives x))
        (detOneSubClassFunction ρ) = 0 := by
  change Lie.pointCoordinates G
    (steinbergModifiedProduct D e x (canonicalSimpleReflectionRepresentatives x))
    (detOneSubCoordinate ρ) = 0
  rw [detOneSubCoordinate_evaluate, ← steinbergModifiedPolynomialMatrix_eq_affineMatrix]
  exact det_one_sub_steinbergModifiedPolynomialMatrix_eq_zero_of_path D e x hρ hβ hlam hi ha hb
    hnα hv hv0

end Langlands.GroupScheme.SplitPinning

import Langlands.Geometry.FormalGroup.ScalarTorsionSchemes
import Langlands.GroupScheme.Cartier.Characters

/-! # The split evaluation pairing on scalar-power torsion -/

noncomputable section
universe u v
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme.Cartier

variable {S : Scheme.{v}} (G : CommGroupScheme S)

/-- Points of the product of a commutative group scheme and its Cartier character presheaf. -/
abbrev PointCharacterPair (T : Over S) :=
  (T ⟶ G.X) × Multiplicative (RelativeHom G (Gm S) T)

variable {T T' : Over S}

/-- The alternating evaluation pairing of the point and character product with itself. -/
def splitPairing (x y : PointCharacterPair G T) : T ⟶ (Gm S).X :=
  evaluation y.2.toAdd x.1 / evaluation x.2.toAdd y.1

@[simp]
theorem splitPairing_self (x : PointCharacterPair G T) : splitPairing G x x = 1 := by
  rw [splitPairing, div_self']

theorem splitPairing_swap (x y : PointCharacterPair G T) :
    splitPairing G y x = (splitPairing G x y)⁻¹ := by
  rw [splitPairing, splitPairing, inv_div]

theorem splitPairing_mul_left (x y z : PointCharacterPair G T) :
    splitPairing G (x * y) z = splitPairing G x z * splitPairing G y z := by
  change evaluation z.2.toAdd (x.1 * y.1) / evaluation (x.2.toAdd + y.2.toAdd) z.1 = _
  rw [evaluation_mul, evaluation_add, mul_div_mul_comm]
  rfl

theorem splitPairing_mul_right (x y z : PointCharacterPair G T) :
    splitPairing G x (y * z) = splitPairing G x y * splitPairing G x z := by
  change evaluation (y.2.toAdd + z.2.toAdd) x.1 / evaluation x.2.toAdd (y.1 * z.1) = _
  rw [evaluation_add, evaluation_mul, mul_div_mul_comm]
  rfl

/-- Restrict both entries of the split product along the test-scheme map. -/
def splitRestrict (a : T' ⟶ T) (x : PointCharacterPair G T) : PointCharacterPair G T' :=
  (a ≫ x.1, Multiplicative.ofAdd (restrict G (Gm S) a x.2.toAdd))

theorem splitPairing_restrict (a : T' ⟶ T) (x y : PointCharacterPair G T) :
    splitPairing G (splitRestrict G a x) (splitRestrict G a y) = a ≫ splitPairing G x y := by
  change evaluation (restrict G (Gm S) a y.2.toAdd) (a ≫ x.1) /
      evaluation (restrict G (Gm S) a x.2.toAdd) (a ≫ y.1) =
    a ≫ (evaluation y.2.toAdd x.1 / evaluation x.2.toAdd y.1)
  rw [evaluation_restrict, evaluation_restrict]
  exact (map_div ((yonedaGrpObj (Gm S).X).map a.op).hom _ _).symm

/-- Act on the first entry and precompose the character in the second entry. -/
def splitMap (f g : G ⟶ G) (x : PointCharacterPair G T) : PointCharacterPair G T :=
  (x.1 ≫ f.toMul.hom.hom, Multiplicative.ofAdd (precompose (Gm S) g T x.2.toAdd))

/-- Switching the two endomorphisms gives the adjoint for the split evaluation pairing. -/
theorem splitPairing_adjoint (f g : G ⟶ G) (x y : PointCharacterPair G T) :
    splitPairing G (splitMap G f g x) y = splitPairing G x (splitMap G g f y) := by
  change evaluation y.2.toAdd (x.1 ≫ f.toMul.hom.hom) /
      evaluation ((CommGroupScheme.baseChange T.hom).map g ≫ x.2.toAdd) y.1 =
    evaluation ((CommGroupScheme.baseChange T.hom).map f ≫ y.2.toAdd) x.1 /
      evaluation x.2.toAdd (y.1 ≫ g.toMul.hom.hom)
  rw [evaluation_precompose g, evaluation_precompose f]

end Langlands.GroupScheme.Cartier

namespace Langlands.FormalGroup.ModuleLaw.IsPiDivisible
open Langlands.GroupScheme

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]
variable {M : ModuleLaw O R σ} {π : O}

/-- The split evaluation pairing for an actual scalar-power torsion kernel. -/
def splitTorsionPairing (hM : M.IsPiDivisible π) (n : ℕ) {T : Over (Spec (CommRingCat.of R))}
    (x y : Cartier.PointCharacterPair (hM.torsionKernelModel n).commGroupScheme T) :
    T ⟶ (Gm (Spec (CommRingCat.of R))).X :=
  Cartier.splitPairing (hM.torsionKernelModel n).commGroupScheme x y

end Langlands.FormalGroup.ModuleLaw.IsPiDivisible

import Langlands.GroupScheme.GeneralLinearFrobenius
import Langlands.GroupScheme.MatrixRepresentation.PositiveTensorPower

/-! # Frobenius powers of actual finite matrix representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable (k : Type u) [Field k] (p : ℕ) [ExpChar k p]

/-- The iterated characteristic-power map, also in characteristic zero and the zero algebra. -/
def characteristicPowerMap (A : Type u) [CommRing A] [Algebra k A] (e : ℕ) : A →+* A where
  toFun x := x ^ p ^ e
  map_one' := one_pow _
  map_zero' := zero_pow (pow_ne_zero _ (expChar_ne_zero k p))
  map_add' x y := CocharacterDescent.add_pow_expChar_pow_of_algebra k p e x y
  map_mul' x y := mul_pow x y _

@[simp] theorem characteristicPowerMap_apply
    (A : Type u) [CommRing A] [Algebra k A] (e : ℕ) (x : A) :
    characteristicPowerMap k p A e x = x ^ p ^ e := rfl

variable {k} {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Iterated postcomposition with the actual matrix Frobenius homomorphism. -/
def frobeniusPower (ρ : MatrixRepresentation G n) : ℕ → MatrixRepresentation G n
  | 0 => ρ
  | e + 1 => frobeniusPower ρ e ≫ GeneralLinear.frobeniusHom k p n

/-- Restriction commutes with the iterated matrix Frobenius. -/
theorem frobeniusPower_restrict (ρ : MatrixRepresentation G n) (i : H ⟶ G) (e : ℕ) :
    (ρ.restrict i).frobeniusPower p e = (ρ.frobeniusPower p e).restrict i := by
  induction e with
  | zero => rfl
  | succ e ih =>
      change (ρ.restrict i).frobeniusPower p e ≫ GeneralLinear.frobeniusHom k p n = _
      rw [ih]
      exact Category.assoc i _ _

/-- On affine tests, every matrix entry is raised to the iterated characteristic power. -/
theorem frobeniusPower_affineMatrix (ρ : MatrixRepresentation G n)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A) (e : ℕ) :
    (ρ.frobeniusPower p e).affineMatrix A x =
      Matrix.GeneralLinearGroup.map (characteristicPowerMap k p A e) (ρ.affineMatrix A x) := by
  induction e with
  | zero =>
      apply Units.ext
      ext r s
      simp only [frobeniusPower, Matrix.GeneralLinearGroup.map_apply,
        characteristicPowerMap_apply, pow_zero, pow_one]
  | succ e ih =>
      change GeneralLinear.affinePointsEquiv n (CommRingCat.of k) A
        ((x ≫ (ρ.frobeniusPower p e).hom.hom) ≫
          (GeneralLinear.frobeniusHom k p n).hom.hom) = _
      rw [GeneralLinear.affinePointsEquiv_frobeniusHom]
      change Matrix.GeneralLinearGroup.map (GeneralLinear.algebraFrobenius k p A)
        ((ρ.frobeniusPower p e).affineMatrix A x) = _
      rw [ih]
      apply Units.ext
      ext r s
      simp only [Matrix.GeneralLinearGroup.map_apply, GeneralLinear.algebraFrobenius_apply,
        characteristicPowerMap_apply, ← pow_mul, pow_succ]

variable [IsAffineHom G.X.hom]

/-- Frobenius transforms a character vector into a vector of the characteristic-power
multiple character. -/
theorem frobeniusPower_characterSpace (ρ : MatrixRepresentation G n)
    {χ : rationalCharacters G} {v : n → k} (hv : v ∈ ρ.characterSpace χ) (e : ℕ) :
    (fun r => v r ^ p ^ e) ∈
      (ρ.frobeniusPower p e).characterSpace ((p ^ e) • χ) := by
  rw [mem_characterSpace_iff]
  unfold universalCharacterMatrix
  rw [frobeniusPower_affineMatrix]
  let A := CharacterUnits.Coord G
  let f := characteristicPowerMap k p A e
  have he := congrArg (fun w : n → A => fun r => f (w r)) hv
  change (fun r => f ((ρ.universalCharacterMatrix *ᵥ
    (fun s => algebraMap k A (v s))) r)) =
    (fun r => f ((CharacterUnits.unit χ : A) * algebraMap k A (v r))) at he
  have hvec : (fun r => algebraMap k A (v r ^ p ^ e)) =
      fun r => f (algebraMap k A (v r)) := by
    funext r
    exact map_pow _ _ _
  rw [hvec, characterUnit_nsmul]
  funext r
  exact ((f.map_mulVec _ _ r).symm.trans (congrFun he r)).trans (by
    simp only [map_mul, f, characteristicPowerMap_apply, Pi.smul_apply, smul_eq_mul,
      Units.val_pow_eq_pow_val])

end Langlands.GroupScheme.MatrixRepresentation

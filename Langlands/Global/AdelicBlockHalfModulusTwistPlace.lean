import Langlands.Global.FiniteParametrizedCuspidalNormalization
import Langlands.Global.AdelicBlockParabolicPlaceCompact
import Langlands.Global.ArchimedeanPlaceCompact

/-! # Inverse half-modulus block twists at one archimedean place -/

noncomputable section

open scoped BigOperators

namespace Langlands.GeneralLinear.BlockShape

universe uR

variable {n : ℕ} (B : BlockShape n) (R : Type uR) [CommRing R]

/-- Put an invertible matrix in one Levi block and the identity in the other blocks. -/
def singleBlockInParabolic (i : Fin B.length) :
    Langlands.GeneralLinear (B.size i) R →* B.parabolic R :=
  (B.leviInParabolic R).comp (MonoidHom.mulSingle (fun j => Langlands.GeneralLinear (B.size j) R) i)

@[simp]
theorem leviProjection_singleBlockInParabolic (i : Fin B.length)
    (a : Langlands.GeneralLinear (B.size i) R) :
    B.leviProjection R (B.singleBlockInParabolic R i a) = Pi.mulSingle i a :=
  B.leviProjection_section R _

end Langlands.GeneralLinear.BlockShape

namespace Langlands.Global.FiniteParametrizedBlockInduction

open Langlands.GeneralLinear Langlands.Automorphic
open AdelicBlockDeterminantCharacter AdelicBlockParabolic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

private theorem map_mulSingle {ι : Type*} [DecidableEq ι] {G H : ι → Type*}
    [∀ j, MulOneClass (G j)] [∀ j, MulOneClass (H j)]
    (f : ∀ j, G j →* H j) (i : ι) (x : G i) :
    (fun j => f j ((Pi.mulSingle i x : ∀ j, G j) j)) = Pi.mulSingle i (f i x) := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Pi.mulSingle_eq_of_ne h]

private theorem inverseHalfBlockHeckeCharacter_single (i : Fin B.length)
    (g : AdelicGL F (B.size i)) :
    (inverseHalfBlockHeckeCharacter F B i).adelicDeterminant (B.size i) g =
      (leviHalfCharacter F B (Pi.mulSingle i g))⁻¹ := by
  let m : FullLevi F B := Pi.mulSingle i g
  have h := prod_inverseHalfBlockHeckeCharacter F B m
  rw [Finset.prod_eq_single i] at h
  · simpa [m] using h
  · intro j _ hji
    simp [m, Pi.mulSingle_eq_of_ne hji]
  · simp

/-- The real place restriction of the inverse half-modulus twist on a
block is the reciprocal of the outer half-character on that block. -/
theorem inverseHalfBlockHeckeCharacter_realPlace (v : RP) (i : Fin B.length)
    (a : Langlands.GeneralLinear (B.size i) ℝ) :
    (inverseHalfBlockHeckeCharacter F B i).adelicDeterminant (B.size i)
        (AdelicGL.realPlaceInclusion F (B.size i) v a) =
      (parabolicHalfCharacter F B (realPlaceInclusion F B v (B.singleBlockInParabolic ℝ i a)))⁻¹ := by
  rw [inverseHalfBlockHeckeCharacter_single]
  change _ = (leviHalfCharacter F B (B.leviProjection (Adeles F)
    (realPlaceInclusion F B v (B.singleBlockInParabolic ℝ i a))))⁻¹
  rw [leviProjection_realPlaceInclusion, B.leviProjection_singleBlockInParabolic, map_mulSingle]

/-- The complex place restriction of the inverse half-modulus twist on a
block is the reciprocal of the outer half-character on that block. -/
theorem inverseHalfBlockHeckeCharacter_complexPlace (v : CP) (i : Fin B.length)
    (a : Langlands.GeneralLinear (B.size i) ℂ) :
    (inverseHalfBlockHeckeCharacter F B i).adelicDeterminant (B.size i)
        (AdelicGL.complexPlaceInclusion F (B.size i) v a) =
      (parabolicHalfCharacter F B (complexPlaceInclusion F B v (B.singleBlockInParabolic ℂ i a)))⁻¹ := by
  rw [inverseHalfBlockHeckeCharacter_single]
  change _ = (leviHalfCharacter F B (B.leviProjection (Adeles F)
    (complexPlaceInclusion F B v (B.singleBlockInParabolic ℂ i a))))⁻¹
  rw [leviProjection_complexPlaceInclusion, B.leviProjection_singleBlockInParabolic, map_mulSingle]

/-- The inverse half-modulus twist has value one on the real place
compact group of its block. -/
theorem inverseHalfBlockHeckeCharacter_realPlace_compact (v : RP) (i : Fin B.length)
    (k : Matrix.unitaryGroup (Fin (B.size i)) ℝ) :
    ((inverseHalfBlockHeckeCharacter F B i).adelicDeterminant (B.size i)
        (AdelicGL.realPlaceInclusion F (B.size i) v (Unitary.toUnits k)) : ℂ) = 1 := by
  rw [inverseHalfBlockHeckeCharacter_realPlace, Units.val_inv_eq_inv_val]
  have h := B.parabolicHalfCharacter_realPlace_compactLevi F v (Pi.mulSingle i k)
  rw [map_mulSingle (fun _ => Unitary.toUnits)] at h
  change (parabolicHalfCharacter F B (realPlaceInclusion F B v
    (B.leviInParabolic ℝ (Pi.mulSingle i (Unitary.toUnits k)))) : ℂ)⁻¹ = 1
  rw [h, inv_one]

/-- The inverse half-modulus twist has value one on the complex place
compact group of its block. -/
theorem inverseHalfBlockHeckeCharacter_complexPlace_compact (v : CP) (i : Fin B.length)
    (k : Matrix.unitaryGroup (Fin (B.size i)) ℂ) :
    ((inverseHalfBlockHeckeCharacter F B i).adelicDeterminant (B.size i)
        (AdelicGL.complexPlaceInclusion F (B.size i) v (Unitary.toUnits k)) : ℂ) = 1 := by
  rw [inverseHalfBlockHeckeCharacter_complexPlace, Units.val_inv_eq_inv_val]
  have h := B.parabolicHalfCharacter_complexPlace_compactLevi F v (Pi.mulSingle i k)
  rw [map_mulSingle (fun _ => Unitary.toUnits)] at h
  change (parabolicHalfCharacter F B (complexPlaceInclusion F B v
    (B.leviInParabolic ℂ (Pi.mulSingle i (Unitary.toUnits k)))) : ℂ)⁻¹ = 1
  rw [h, inv_one]

end Langlands.Global.FiniteParametrizedBlockInduction

import Langlands.Representation.RankinSelberg.RootTorusProductStatement
import Langlands.AllField.Group.GL.PadicSupplement
import Langlands.AllField.Representation.RankinSelberg.RootFiniteFunctionStatement
/-! Uniform finite-family reduction of a product of torus expansions. -/

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding RootTorusProductStatement
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open scoped BigOperators

universe uF

/-- Products of two finite torus expansions, the row test, and the inverse
modulus have a finite Schwartz expansion in root coordinates. The finite
function family is fixed before any test functions or matrix are chosen. -/
def RootTorusProductStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  letI := T.topology
  let A := Fin (n + 1) → Fˣ
  let toDiagonal : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let weight : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  let finiteFunction := fun f : A → ℂ => Continuous f ∧
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun b : A => fun a : A => f (b * a)))
  ∀ X Y : Finset (A → ℂ),
    (∀ χ ∈ X, finiteFunction χ) → (∀ χ ∈ Y, finiteFunction χ) →
    let I := {χ // χ ∈ X} × {χ // χ ∈ Y}
    let η : I → A → ℂ := fun z a =>
      z.1.val (toDiagonal a) * z.2.val (toDiagonal a) * weight a
    (∀ z, finiteFunction (η z)) ∧
    ∀ (φ : {χ // χ ∈ X} → SchwartzBruhat (Fin n → F))
      (φ' : {χ // χ ∈ Y} → SchwartzBruhat (Fin n → F))
      (Φ : SchwartzBruhat (Fin (n + 1) → F))
      (k : Langlands.GeneralLinear (n + 1) F),
    ∃ Ψ : I → SchwartzBruhat (Fin (n + 1) → F),
      ∀ a : A,
        (∑ χ, φ χ (fun i : Fin n =>
          ((toDiagonal a i.castSucc / toDiagonal a i.succ : Fˣ) : F)) *
            χ.val (toDiagonal a)) *
        (∑ χ, φ' χ (fun i : Fin n =>
          ((toDiagonal a i.castSucc / toDiagonal a i.succ : Fˣ) : F)) *
            χ.val (toDiagonal a)) *
        Φ (lastRow (GeneralLinear.Iwasawa.diagonalUnits (toDiagonal a) * k)) * weight a =
          ∑ z : I, Ψ z (fun i => (a i : F)) * η z a

end Langlands.AllField.RankinSelberg

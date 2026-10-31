import Langlands.AbelianScheme.Tate.AwayRationalScalars
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Freeness of actual full and away Tate modules at geometric points -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Tate

/-- At an algebraically closed point, the actual full and prime-to-modulus Tate
modules are free of rank `2 * g` over their integral and adelic scalar rings
when all selected torsion orders are invertible on the base. A proof target. -/
def GeometricAdelicRankStatement : Prop :=
  ∀ (S : Scheme.{u}) (A : AbelianScheme S) (g : ℕ),
    A.HasRelativeDimension g →
      ((∀ n : ℕ, 0 < n → IsUnit (n : Γ(S, ⊤))) →
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (s : Spec (CommRingCat.of Ω) ⟶ S),
          Nonempty ((Fin (2 * g) → Global.ProfiniteIntegerRing) ≃ₗ[
            Global.ProfiniteIntegerRing] FullAt A s) ∧
          ∀ h : Global.RationalProfiniteIntegerAdeleComparison,
            let := finiteAdeleModule A (Over.mk s) (fun _ => True) h
            Nonempty ((Fin (2 * g) → Global.FiniteAdeles ℚ) ≃ₗ[
              Global.FiniteAdeles ℚ] RationalFullAt A s)) ∧
      (∀ m : ℕ,
        (∀ n : ℕ, 0 < n → Nat.Coprime n m → IsUnit (n : Γ(S, ⊤))) →
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (s : Spec (CommRingCat.of Ω) ⟶ S),
            Nonempty ((Fin (2 * g) → Global.PrimeToProfiniteIntegerRing m) ≃ₗ[
              Global.PrimeToProfiniteIntegerRing m] AwayAt A s m) ∧
            ∀ (h : Global.RationalProfiniteIntegerAdeleComparison)
              (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m),
              let := primeToFiniteAdeleModule A (Over.mk s) hAway
              Nonempty ((Fin (2 * g) → Global.PrimeToFiniteAdeles m) ≃ₗ[
                Global.PrimeToFiniteAdeles m] RationalAwayAt A s m))

end Langlands.AbelianScheme.Tate

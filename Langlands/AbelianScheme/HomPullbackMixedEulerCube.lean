import Langlands.AbelianScheme.FieldCubePullbackProof
import Langlands.AbelianScheme.FieldAbelianSchemeGeometry
import Langlands.AbelianScheme.Rational
import Langlands.AlgebraicGeometry.Picard.MixedEulerCoefficientScaling
import Langlands.AlgebraicGeometry.Picard.MixedEulerCoefficientDenominator
import Langlands.Algebra.CubeQuadraticLocalLattice

/-! # The mixed Euler coefficient of pulled-back line bundles on Hom

For abelian schemes `A` and `B` over a field and line bundles `LA` on `A`,
`LB` on `B`, the function `f ↦ c_{LA}(f^* LB)` on `A ⟶ B` satisfies the cube
identity and has denominators bounded by `g!`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {k : Type u} [Field k] {A B : AbelianScheme (Spec (CommRingCat.of k))}

/-- The actual mixed Euler coefficient of the pullback of `LB` along a
homomorphism, computed with respect to `LA` and dimension truncation `g`. -/
def homMixedEuler (LA : LineBundle A.X.left) (LB : LineBundle B.X.left) (g : ℕ)
    (f : A ⟶ B) : ℚ :=
  mixedLineBundleEulerCoefficient A.X.hom LA ((LineBundle.pullback (hom f)).obj LB) g

/-- The values of `homMixedEuler` become integers after multiplication by `g!`. -/
theorem exists_int_factorial_mul_homMixedEuler (LA : LineBundle A.X.left)
    (LB : LineBundle B.X.left) (g : ℕ) (f : A ⟶ B) :
    ∃ z : ℤ, (g.factorial : ℚ) * homMixedEuler LA LB g f = z :=
  exists_int_factorial_mul_mixedLineBundleEulerCoefficient A.X.hom LA _ g

/-- In positive relative dimension, `homMixedEuler` satisfies the cube identity. -/
theorem homMixedEuler_cubeIdentity (LA : LineBundle A.X.left) (LB : LineBundle B.X.left)
    (d : ℕ) (hA : A.HasRelativeDimension (d + 1)) :
    Langlands.Algebra.CubeQuadratic.CubeIdentity (homMixedEuler LA LB (d + 1)) := by
  have : IsIntegral A.X.left := field_isIntegral A
  have : IsNoetherian A.X.left := field_isNoetherian A
  have : A.X.left.IsSeparated := field_isSeparated A
  have hX : topologicalKrullDim A.X.left ≤ (d : WithBot ℕ∞) + 1 := by
    rw [field_topologicalKrullDim hA]
    push_cast
    exact le_rfl
  have hadd : ∀ M N : LineBundle A.X.left,
      mixedLineBundleEulerCoefficient A.X.hom LA
        (LineBundle.tensor Langlands.Scheme.Modules.pullbackTensorComparisonIsIso M N) (d + 1) =
      mixedLineBundleEulerCoefficient A.X.hom LA M (d + 1) +
        mixedLineBundleEulerCoefficient A.X.hom LA N (d + 1) :=
    mixedEulerCoefficientTensorAdditive A.X.hom LA d hX
  intro f g h
  obtain ⟨e⟩ := GroupScheme.fieldCubePullback k B.toGrp inferInstance inferInstance
    inferInstance A.X (groupHom f).hom.hom (groupHom g).hom.hom (groupHom h).hom.hom LB
  let P : (A ⟶ B) → LineBundle A.X.left := fun x => (LineBundle.pullback (hom x)).obj LB
  let T := fun M N : LineBundle A.X.left =>
    LineBundle.tensor Langlands.Scheme.Modules.pullbackTensorComparisonIsIso M N
  have he := mixedLineBundleEulerPolynomial_iso A.X.hom LA
    (T (P (f + g + h)) (T (P f) (T (P g) (P h))))
    (T (P (f + g)) (T (P (f + h)) (P (g + h)))) (d + 1) e
  have hc : mixedLineBundleEulerCoefficient A.X.hom LA
      (T (P (f + g + h)) (T (P f) (T (P g) (P h)))) (d + 1) =
      mixedLineBundleEulerCoefficient A.X.hom LA
      (T (P (f + g)) (T (P (f + h)) (P (g + h)))) (d + 1) :=
    congrArg (fun p => Polynomial.coeff p (d + 1 - 1)) he
  simp only [T, P, hadd] at hc
  simp only [homMixedEuler]
  linarith

/-- The integral points of a finitely generated rational Hom subspace form a
finitely generated group, once `homMixedEuler` is positive at nonzero
homomorphisms. -/
theorem fg_comap_homToHom0_of_homMixedEuler_pos (LA : LineBundle A.X.left)
    (LB : LineBundle B.X.left) (d : ℕ) (hA : A.HasRelativeDimension (d + 1))
    (hpos : ∀ f : A ⟶ B, f ≠ 0 → 0 < homMixedEuler LA LB (d + 1) f)
    (V : Submodule ℚ (Hom0 A B)) (hV : V.FG) :
    ((V.restrictScalars ℤ).comap (homToHom0 (A := A) (B := B))).FG :=
  Langlands.Algebra.CubeQuadratic.fg_comap_of_cubeIdentity (homMixedEuler LA LB (d + 1))
    (homMixedEuler_cubeIdentity LA LB d hA) (d + 1).factorial (Nat.factorial_pos _)
    (exists_int_factorial_mul_homMixedEuler LA LB (d + 1)) hpos V hV

end Langlands.AbelianScheme

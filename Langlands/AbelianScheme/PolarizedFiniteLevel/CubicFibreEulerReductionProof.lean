import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreEulerReductionStatement
import Langlands.AlgebraicGeometry.Picard.SmoothProperLineBundleEulerPolynomialProof
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristicBasicProof
import Mathlib.Tactic

/-! # Finite cohomology and the dimension reduction for the actual cubic bundle -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Higher-cohomology vanishing turns an Euler-square equality into the dimension
of degree-zero cohomology. -/
theorem finrank_eq_of_higherCohomology_isZero_of_eulerSquare
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (h : HasFiniteCohomology f M) (r : ℕ)
    (hv : ∀ i : ℕ, 0 < i → IsZero ((relativeCohomology f i).obj M))
    (hs : (eulerCharacteristic f M h) ^ 2 = (r : ℤ) ^ 2) :
    Module.finrank K ((relativeCohomology f 0).obj M) = r := by
  have he := (eulerCharacteristicBasic K X f).2.2.2.2 M h hv
  rw [he] at hs
  have hdim : (0 : ℤ) ≤ Module.finrank K ((relativeCohomology f 0).obj M) :=
    Int.natCast_nonneg _
  have hr : (0 : ℤ) ≤ r := Int.natCast_nonneg _
  have heq : (Module.finrank K ((relativeCohomology f 0).obj M) : ℤ) = r := by
    nlinarith
  exact_mod_cast heq

end Langlands.AlgebraicGeometry.Modules.DerivedSections

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Modules.DerivedSections
  Langlands.AlgebraicGeometry.Picard

/-- The actual cubic bundle has finite-dimensional cohomology in every degree
and a finite cohomological vanishing bound over every field. -/
theorem Datum.cubicBundle_hasFiniteCohomology
    {P : Prerequisites.{u}} {K : Type u} [Field K] {g d n : ℕ}
    (a : Datum P (Spec (CommRingCat.of K)) g d n) :
    HasFiniteCohomology a.abelian.X.hom a.cubicBundle.obj := by
  obtain ⟨h, _⟩ := smoothProperLineBundleEulerPolynomial K a.abelian.X g
    a.dimension inferInstance inferInstance a.canonicalBundle
  exact h 3

/-- For the actual cubic bundle, positive-degree vanishing and the geometric
Euler square give the specified degree-zero dimension. -/
theorem Datum.cubicBundle_finrank_of_vanishing_of_eulerSquare
    {P : Prerequisites.{u}} {K : Type u} [Field K] {g d n : ℕ}
    (a : Datum P (Spec (CommRingCat.of K)) g d n)
    (h : HasFiniteCohomology a.abelian.X.hom a.cubicBundle.obj)
    (hv : ∀ i : ℕ, 0 < i →
      IsZero ((relativeCohomology a.abelian.X.hom i).obj a.cubicBundle.obj))
    (hs : (eulerCharacteristic a.abelian.X.hom a.cubicBundle.obj h) ^ 2 =
      (6 : ℤ) ^ (2 * g) * (d : ℤ) ^ 2) :
    Module.finrank K ((relativeCohomology a.abelian.X.hom 0).obj
      a.cubicBundle.obj) = 6 ^ g * d := by
  apply finrank_eq_of_higherCohomology_isZero_of_eulerSquare K _
    a.abelian.X.hom a.cubicBundle.obj h (6 ^ g * d) hv
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow, ← pow_mul,
    Nat.mul_comm g 2] using hs

/-- The unconditional finite-cohomology specialization and conditional
Euler-square dimension reduction hold for the actual cubic bundle. -/
theorem cubicFibreEulerReduction : CubicFibreEulerReductionStatement.{u} := by
  intro P K _ g d n a
  exact ⟨a.cubicBundle_hasFiniteCohomology,
    a.cubicBundle_finrank_of_vanishing_of_eulerSquare⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel

import Langlands.GroupScheme.Rational.TorusLinearization.AdditivePolynomials
import Langlands.GroupScheme.Rational.CharacterUnits
import Langlands.GroupScheme.Rational.RootFiniteness
import Mathlib.Algebra.Module.Torsion.Free

/-! # Characteristic powers in torus-equivariant additive polynomials -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Polynomial

namespace Langlands.GroupScheme

namespace TorusLinearization

variable {k : Type u} [Field k]

/-- Coefficient support at powers of a specified exponential characteristic. -/
theorem IsAddPoly₁.exists_pow_of_coeff_ne_zero
    {p : ℕ} [hp : ExpChar k p] {f : k[X]} (hf : IsAddPoly₁ f)
    {d : ℕ} (hd : f.coeff d ≠ 0) : ∃ r : ℕ, d = p ^ r := by
  cases hp with
  | zero =>
    have hd1 : d = 1 := by
      by_contra h
      have hd0 : d ≠ 0 := by
        intro h0
        subst d
        exact hd hf.coeff_zero
      have hc := hf.choose_mul_coeff (d := d) (i := 1) (by omega) (by omega)
      rw [Nat.choose_one_right] at hc
      exact (Nat.cast_ne_zero.mpr hd0) ((mul_eq_zero.mp hc).resolve_right hd)
    exact ⟨0, by simp [hd1]⟩
  | @prime p hp hchar =>
    let : Fact p.Prime := ⟨hp⟩
    by_contra h
    push Not at h
    exact hd (hf.coeff_eq_zero k p h)

/-- Every nonzero coefficient of an additive polynomial over a field has degree
an integral power of the field's characteristic exponent, including characteristic zero. -/
theorem IsAddPoly₁.exists_expChar_pow_of_coeff_ne_zero
    {f : k[X]} (hf : IsAddPoly₁ f) {d : ℕ} (hd : f.coeff d ≠ 0) :
    ∃ r : ℕ, d = ringExpChar k ^ r :=
  hf.exists_pow_of_coeff_ne_zero hd

end TorusLinearization

namespace IsogenyRootPolynomial

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffineHom T.toGrp.X.hom]

/-- Evaluate actual torus characters at the universal coordinate-algebra point,
with the units written additively. -/
def characterUnit : characterLattice T →+ Additive (CharacterUnits.Coord T.toGrp)ˣ :=
  CharacterUnits.unitHom.comp (rationalCharacters.equivCharacterLattice T).symm.toAddMonoidHom

 theorem characterUnit_injective : Function.Injective (characterUnit (T := T)) :=
  CharacterUnits.unitHom_injective.comp (rationalCharacters.equivCharacterLattice T).symm.injective

/-- The universal polynomial equivariance equation for source and target characters.
It is an equality over the actual torus coordinate algebra, not only over field points. -/
def IsEquivariant (α β : characterLattice T) (f : k[X]) : Prop :=
  Polynomial.aeval
      (Polynomial.C ((characterUnit α).toMul : CharacterUnits.Coord T.toGrp) * Polynomial.X) f =
    Polynomial.C ((characterUnit β).toMul : CharacterUnits.Coord T.toGrp) *
      f.map (algebraMap k (CharacterUnits.Coord T.toGrp))

private theorem coeff_scale (f : k[X]) (c : CharacterUnits.Coord T.toGrp) (d : ℕ) :
    (Polynomial.aeval (Polynomial.C c * Polynomial.X) f).coeff d =
      algebraMap k (CharacterUnits.Coord T.toGrp) (f.coeff d) * c ^ d := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, Polynomial.coeff_add, hf, hg, add_mul]
  | monomial n b =>
    simp only [Polynomial.aeval_monomial, Polynomial.algebraMap_apply, mul_pow,
      ← Polynomial.C_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_monomial]
    split_ifs <;> simp_all

/-- Every nonzero degree coefficient of an equivariant polynomial identifies
the target character with that multiple of the source character. -/
theorem IsEquivariant.character_eq_nsmul
    {α β : characterLattice T} {f : k[X]} (he : IsEquivariant α β f)
    {d : ℕ} (hd : f.coeff d ≠ 0) : β = d • α := by
  have hc := congrArg (fun p => Polynomial.coeff p d) he
  rw [coeff_scale, Polynomial.coeff_C_mul, Polynomial.coeff_map] at hc
  have hunit : IsUnit (algebraMap k (CharacterUnits.Coord T.toGrp) (f.coeff d)) :=
    (isUnit_iff_ne_zero.mpr hd).map (algebraMap k (CharacterUnits.Coord T.toGrp))
  have hval : ((characterUnit β).toMul : CharacterUnits.Coord T.toGrp) =
      ((characterUnit α).toMul : CharacterUnits.Coord T.toGrp) ^ d := by
    apply hunit.mul_left_cancel
    simpa only [mul_comm] using hc.symm
  apply characterUnit_injective
  apply Additive.toMul.injective
  rw [map_nsmul]
  exact Units.ext hval

/-- The resulting nonzero monomial, its characteristic power, and the actual
integral character equation. -/
structure PowerMonomial (α β : characterLattice T) (f : k[X]) where
  exponent : ℕ
  scalar : kˣ
  polynomial_eq : f = Polynomial.C (scalar : k) * Polynomial.X ^ (ringExpChar k ^ exponent)
  character_eq : β = (ringExpChar k ^ exponent) • α

/-- Nonzero equivariant additive polynomials of nonzero source weight are
single characteristic-power monomials, over arbitrary fields. -/
theorem nonempty_powerMonomial (hT : IsSplitTorus T.toGrp)
    {α β : characterLattice T} (hα : α ≠ 0) {f : k[X]} (hf0 : f ≠ 0)
    (hf : TorusLinearization.IsAddPoly₁ f) (he : IsEquivariant α β f) :
    Nonempty (PowerMonomial α β f) := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, f.coeff d ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (Polynomial.ext fun d => by simpa using h d)
  obtain ⟨r, hr⟩ := hf.exists_expChar_pow_of_coeff_ne_zero hd
  have hchar := he.character_eq_nsmul hd
  have hinj : Function.Injective (fun n : ℕ => n • α) := by
    intro m n h
    apply Nat.cast_injective (R := ℚ)
    have hαrat : Langlands.LinearAlgebra.RationalSpan.toRat α ≠ 0 := by
      intro hz
      apply hα
      apply hT.character_toRat_injective
      simpa using hz
    have hh := congrArg Langlands.LinearAlgebra.RationalSpan.toRat h
    simp only [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ] at hh
    exact smul_left_injective ℚ hαrat hh
  refine ⟨⟨r, Units.mk0 (f.coeff d) hd, ?_, ?_⟩⟩
  · rw [← hr, Polynomial.C_mul_X_pow_eq_monomial]
    apply Polynomial.ext
    intro n
    by_cases hn : n = d
    · subst n
      simp
    · have hzero : f.coeff n = 0 := by
        by_contra hn0
        exact hn (hinj ((he.character_eq_nsmul hn0).symm.trans hchar))
      simp [Polynomial.coeff_monomial, hzero, Ne.symm hn]
  · simpa [hr] using hchar

/-- Choose the monomial exponent and scalar with their two proved equations. -/
def powerMonomial (hT : IsSplitTorus T.toGrp)
    {α β : characterLattice T} (hα : α ≠ 0) {f : k[X]} (hf0 : f ≠ 0)
    (hf : TorusLinearization.IsAddPoly₁ f) (he : IsEquivariant α β f) :
    PowerMonomial α β f :=
  Classical.choice (nonempty_powerMonomial hT hα hf0 hf he)

end IsogenyRootPolynomial
end Langlands.GroupScheme

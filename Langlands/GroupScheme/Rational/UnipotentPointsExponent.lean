import Langlands.GroupScheme.Rational.UnipotentPointsNilpotent
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas

/-! # A uniform power exponent for unipotent groups in positive characteristic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

/-- One exponent kills every point on every relative scheme test. -/
def HasUniformPowerExponent {B : Scheme.{u}} (G : GroupScheme B) (q : ℕ) : Prop :=
  ∀ (T : Over B) (x : T ⟶ G.X), x ^ q = 1

/-- A monic subgroup inherits an all-test exponent, without a separate
unipotence assumption on that subgroup. -/
theorem HasUniformPowerExponent.of_mono {B : Scheme.{u}} {H G : GroupScheme B}
    {q : ℕ} (hG : HasUniformPowerExponent G q) (i : H ⟶ G) [Mono i.hom.hom] :
    HasUniformPowerExponent H q := by
  intro T x
  apply (cancel_mono i.hom.hom).1
  rw [MonObj.pow_comp, MonObj.one_comp]
  exact hG T (x ≫ i.hom.hom)

namespace UnitDifference

/-- A nilpotent difference bounds the p-power order of a unit. The coefficient
ring may be noncommutative or trivial. -/
theorem unit_pow_eq_one_of_sub_pow_eq_zero
    {k A : Type*} [Field k] [Ring A] (f : k →+* A)
    (p r m : ℕ) [Fact p.Prime] [CharP k p] (x : Aˣ)
    (hm : ((x : A) - 1) ^ m = 0) (hmp : m ≤ p ^ r) : x ^ (p ^ r) = 1 := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · apply Units.ext
    exact Subsingleton.elim _ _
  · let : CharP A p := charP_of_injective_ringHom f.injective p
    apply Units.ext
    change (x : A) ^ (p ^ r) = 1
    have hzero := pow_eq_zero_of_le hmp hm
    rw [sub_pow_char_pow_of_commute p r (Commute.one_right (x : A)), one_pow,
      sub_eq_zero] at hzero
    exact hzero

end UnitDifference

section PositiveCharacteristic

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (p : ℕ) [Fact p.Prime] [CharP k p]

namespace MatrixRepresentation

/-- The representation dimension bounds a uniform p-power exponent of the
represented points on all tests, including empty and nonreduced tests. -/
theorem pointMatrix_pow_eq_one_of_isUnipotent (hG : IsUnipotent G) {m : ℕ}
    (ρ : MatrixRepresentation G (Fin m)) {r : ℕ} (hr : m ≤ p ^ r)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    (ρ.pointMatrix T x) ^ (p ^ r) = 1 := by
  exact UnitDifference.unit_pow_eq_one_of_sub_pow_eq_zero
    ((Matrix.scalar (Fin m)).comp (scalarMap T)) p r m (ρ.pointMatrix T x)
    (pointMatrix_sub_one_pow_eq_zero_of_isUnipotent hG ρ T x) hr

/-- A faithful representation turns the matrix exponent into the same actual
all-test group exponent. -/
theorem hasUniformPowerExponent_of_mono (hG : IsUnipotent G) {m : ℕ}
    (ρ : MatrixRepresentation G (Fin m)) [Mono ρ.hom.hom]
    {r : ℕ} (hr : m ≤ p ^ r) : HasUniformPowerExponent G (p ^ r) := by
  intro T x
  apply pointMatrix_injective ρ T
  rw [map_pow, map_one]
  exact pointMatrix_pow_eq_one_of_isUnipotent p hG ρ hr T x

end MatrixRepresentation

/-- Every affine locally finite type unipotent group in characteristic p has
one p-power exponent valid on all scheme-valued points. -/
theorem exists_hasUniformPowerExponent_of_isUnipotent
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (hG : IsUnipotent G) :
    ∃ r : ℕ, HasUniformPowerExponent G (p ^ r) := by
  obtain ⟨m, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have : Mono ρ.hom.hom := Over.mono_of_mono_left _
  refine ⟨m, MatrixRepresentation.hasUniformPowerExponent_of_mono p hG ρ ?_⟩
  exact Nat.le_of_lt (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)

end PositiveCharacteristic

end Langlands.GroupScheme

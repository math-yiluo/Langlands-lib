import Langlands.Representation.RankinSelberg.TwistInvariance
import Langlands.Analysis.Local.QuotientTopology

/-!
# Recursive coordinates on the actual left-unipotent quotient

These are the algebraic and topological maps underlying JPSS Section 8.3,
printed p.449, equation (1). No measure or integration identity is asserted.
-/

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Langlands.QuotientIntegration

universe uF

variable {F : Type uF} [Field F]

/-- The actual representative `diag(g,1) a k` in rank `n + 2`. -/
def recursiveQuotientRepresentative (n : ℕ)
    (g : GeneralLinear (n + 1) F) (a : Fˣ) (k : GeneralLinear (n + 2) F) :
    GeneralLinear (n + 2) F :=
  rankInclusion 1 g * GeneralLinear.scalar a * k

/-- The representative also has the published iterated-identity application form. -/
theorem recursiveQuotientRepresentative_eq_appendIdentity (n : ℕ)
    (g : GeneralLinear (n + 1) F) (a : Fˣ) (k : GeneralLinear (n + 2) F) :
    recursiveQuotientRepresentative n g a k =
      appendIdentity n 1 g * GeneralLinear.scalar a * k := rfl

/-- A lower upper-unipotent translation becomes an actual upper-unipotent
translation in the larger rank. -/
theorem recursiveQuotientRepresentative_unipotent_mul (n : ℕ)
    (u : upperUnipotent (n + 1) F) (g : GeneralLinear (n + 1) F)
    (a : Fˣ) (k : GeneralLinear (n + 2) F) :
    recursiveQuotientRepresentative n (u.val * g) a k =
      (corankOneUnipotent u).val * recursiveQuotientRepresentative n g a k := by
  simp only [recursiveQuotientRepresentative, map_mul, corankOneUnipotent, mul_assoc]

/-- The class of the representative is independent of a lower unipotent
translation. This is the descent condition for the existing left quotient. -/
theorem recursiveQuotientRepresentative_class_invariant (n : ℕ)
    (a : Fˣ) (k : GeneralLinear (n + 2) F)
    (u : upperUnipotent (n + 1) F) (g : GeneralLinear (n + 1) F) :
    leftQuotientMap (upperUnipotent (n + 2) F)
        (recursiveQuotientRepresentative n (u.val * g) a k) =
      leftQuotientMap (upperUnipotent (n + 2) F)
        (recursiveQuotientRepresentative n g a k) := by
  rw [recursiveQuotientRepresentative_unipotent_mul]
  apply Eq.symm
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simpa only [mul_inv_cancel_right] using (corankOneUnipotent u).property

/-- Recursive coordinates from the actual rank `n + 1` left quotient, scalar
units, and an arbitrary rank `n + 2` group element to the larger left quotient. -/
def recursiveQuotientCoordinates (n : ℕ)
    (p : LeftUnipotentQuotient n F × Fˣ × GeneralLinear (n + 2) F) :
    LeftUnipotentQuotient (n + 1) F :=
  descend (upperUnipotent (n + 1) F)
    (fun g => leftQuotientMap (upperUnipotent (n + 2) F)
      (recursiveQuotientRepresentative n g p.2.1 p.2.2))
    (recursiveQuotientRepresentative_class_invariant n p.2.1 p.2.2) p.1

/-- Evaluation of the descended coordinates on an actual matrix class. -/
@[simp] theorem recursiveQuotientCoordinates_mk (n : ℕ)
    (g : GeneralLinear (n + 1) F) (a : Fˣ) (k : GeneralLinear (n + 2) F) :
    recursiveQuotientCoordinates n (Quotient.mk _ g, a, k) =
      Quotient.mk _ (rankInclusion 1 g * GeneralLinear.scalar a * k) := rfl

/-- Evaluation with the iterated-identity API, in the displayed product order. -/
theorem recursiveQuotientCoordinates_mk_appendIdentity (n : ℕ)
    (g : GeneralLinear (n + 1) F) (a : Fˣ) (k : GeneralLinear (n + 2) F) :
    recursiveQuotientCoordinates n (Quotient.mk _ g, a, k) =
      Quotient.mk _ (appendIdentity n 1 g * GeneralLinear.scalar a * k) := rfl

/-- Determinant absolute value for every representative, with arbitrary `k`. -/
theorem recursiveQuotientRepresentative_det_abs (n : ℕ)
    (abv : AbsoluteValue F ℝ) (g : GeneralLinear (n + 1) F)
    (a : Fˣ) (k : GeneralLinear (n + 2) F) :
    abv (Matrix.det (recursiveQuotientRepresentative n g a k).val) =
      abv (Matrix.det g.val) * abv (a : F) ^ (n + 2) *
        abv (Matrix.det k.val) := by
  have hs : Matrix.det (GeneralLinear.scalar a : GeneralLinear (n + 2) F).val =
      (a : F) ^ (n + 2) := by
    simp [GeneralLinear.scalar]
  simp only [recursiveQuotientRepresentative, Units.val_mul, Matrix.det_mul,
    det_rankInclusion, hs, map_mul, map_pow]

/-- Adjoining the last identity coordinate fixes the last row after multiplication. -/
theorem lastRow_rankInclusion_one_mul (n : ℕ) (g : GeneralLinear (n + 1) F)
    (h : GeneralLinear (n + 2) F) :
    lastRow (rankInclusion 1 g * h) = lastRow h := by
  funext j
  change ∑ i : Fin (n + 2),
    appendIdentity n 1 g (Fin.last (n + 1)) i * h i j = h (Fin.last (n + 1)) j
  rw [Finset.sum_eq_single (Fin.last (n + 1))]
  · simp [appendIdentity_entry]
  · intro i _ hi
    simp [appendIdentity_entry, Ne.symm hi]
  · simp

/-- Last-row scaling for an arbitrary matrix group element. -/
theorem lastRow_scalar_mul (n : ℕ) (a : Fˣ) (k : GeneralLinear (n + 2) F) :
    lastRow (GeneralLinear.scalar a * k) = fun j => (a : F) * lastRow k j := by
  funext j
  change (Matrix.scalar (Fin (n + 2)) (a : F) * k.val) (Fin.last (n + 1)) j = _
  simp [Matrix.scalar_apply, Matrix.diagonal_mul, lastRow]

/-- The representative's last row is the scalar multiple of the last row of `k`,
independently of the smaller matrix. -/
theorem recursiveQuotientRepresentative_lastRow (n : ℕ)
    (g : GeneralLinear (n + 1) F) (a : Fˣ) (k : GeneralLinear (n + 2) F) :
    lastRow (recursiveQuotientRepresentative n g a k) =
      fun j => (a : F) * lastRow k j := by
  rw [recursiveQuotientRepresentative, mul_assoc, lastRow_rankInclusion_one_mul,
    lastRow_scalar_mul]

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- Joint continuity of the actual representative map. -/
theorem continuous_recursiveQuotientRepresentative (n : ℕ) :
    Continuous (fun p : GeneralLinear (n + 1) F × Fˣ × GeneralLinear (n + 2) F =>
      recursiveQuotientRepresentative n p.1 p.2.1 p.2.2) :=
  (((rankInclusionContinuous 1).continuous.comp continuous_fst).mul
    (GeneralLinear.scalarContinuous.continuous.comp continuous_snd.fst)).mul
    continuous_snd.snd

/-- Joint continuity descends through the open quotient projection and its product
with the identity on the scalar and larger-group coordinates. -/
theorem continuous_recursiveQuotientCoordinates (n : ℕ) :
    Continuous (recursiveQuotientCoordinates (F := F) n) := by
  apply ((leftQuotient_isOpenQuotientMap (upperUnipotent (n + 1) F)).prodMap
    (IsOpenQuotientMap.id (X := Fˣ × GeneralLinear (n + 2) F))).isQuotientMap.continuous_iff.mpr
  exact (leftQuotient_isOpenQuotientMap (upperUnipotent (n + 2) F)).continuous.comp
    (continuous_recursiveQuotientRepresentative n)

end Topology

end Langlands.RankinSelberg

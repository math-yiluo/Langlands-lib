import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizerPairing
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # The conjugation submersion for an idempotent parabolic

On the locus where the adjoint action of the Levi coordinate is invertible on the
off-diagonal summand, conjugating an upper triangular Lie algebra element by a unit
has surjective strict derivative. This is the differential used in a pushforward
proof of local summability in Harish-Chandra's parabolic descent.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer

open ContinuousLinearMap
open scoped RightActions

universe u v

section Algebra

variable {F : Type u} [Field F] {A : Type v} [Ring A] [Algebra F A] {e : A}

private theorem mem_corner_iff (he : IsIdempotentElem e) {x : A} :
    x ∈ offDiagonalCorner F e ↔ e * x = x ∧ x * e = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨h₁, h₂, -, -, -, -, -, -⟩ := idempotent_mul_rules he
    simp only [cornerProjection_apply]
    exact ⟨by rw [← mul_assoc e (e * y), ← mul_assoc e e y, h₁],
      by rw [mul_assoc _ (1 - e), h₂, mul_zero]⟩
  · rintro ⟨hl, hr⟩
    exact ⟨x, by rw [cornerProjection_apply, hl, mul_sub, mul_one, hr, sub_zero]⟩

private theorem mem_opposite_corner_iff (he : IsIdempotentElem e) {x : A} :
    x ∈ offDiagonalCorner F (1 - e) ↔ e * x = 0 ∧ x * e = x := by
  rw [mem_corner_iff he.one_sub]
  simp only [sub_mul, mul_sub, one_mul, mul_one]
  constructor
  · rintro ⟨hl, hr⟩
    refine ⟨?_, (sub_eq_zero.mp hr).symm⟩
    calc
      e * x = x - (x - e * x) := (sub_sub_cancel _ _).symm
      _ = 0 := by rw [hl, sub_self]
  · rintro ⟨hl, hr⟩
    rw [hl, hr, sub_zero, sub_self]
    exact ⟨rfl, rfl⟩

private theorem cornerProjection_mul_left {y : A} (hy : e * y = y * e) (x : A) :
    cornerProjection F e (y * x) = y * cornerProjection F e x := by
  simp only [cornerProjection_apply, ← mul_assoc, hy]

private theorem cornerProjection_mul_right {y : A} (hy : e * y = y * e) (x : A) :
    cornerProjection F e (x * y) = cornerProjection F e x * y := by
  have hy' : y * (1 - e) = (1 - e) * y := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hy]
  simp only [cornerProjection_apply, mul_assoc, hy']

private theorem cornerProjection_of_mem (he : IsIdempotentElem e) {x : A}
    (hx : x ∈ offDiagonalCorner F e) : cornerProjection F e x = x := by
  obtain ⟨hl, hr⟩ := (mem_corner_iff he).mp hx
  rw [cornerProjection_apply, hl, mul_sub, mul_one, hr, sub_zero]

/-- Varying the conjugator in the opposite corner and varying the upper triangular
element span all the ambient directions when the Levi adjoint action is surjective
on the off-diagonal summand. -/
theorem exists_parabolic_commutator_add (he : IsIdempotentElem e)
    (y : Subalgebra.centralizer F ({e} : Set A)) (z : offDiagonalCorner F e)
    (hy : Function.Surjective (offDiagonalAdjoint F e y)) (w : A) :
    ∃ (t : offDiagonalCorner F (1 - e)) (v : Subalgebra.centralizer F ({e} : Set A))
      (s : offDiagonalCorner F e),
      (t : A) * ((y : A) + z) - ((y : A) + z) * t + ((v : A) + s) = w := by
  let lower (x : A) := cornerProjection F (1 - e) x
  have hlower (x : A) : lower x ∈ offDiagonalCorner F (1 - e) := cornerProjection_mem F _ _
  have hwOff : lower w ∈ offDiagonal F e := by
    obtain ⟨hl, hr⟩ := (mem_opposite_corner_iff he).mp (hlower w)
    rw [mem_offDiagonal_iff, diagonalProjection_apply, hl, zero_mul, zero_add,
      mul_sub, mul_one, mul_assoc, hr, sub_self]
  obtain ⟨x, hx⟩ := hy ⟨lower w, hwOff⟩
  have hx' : (y : A) * (x : A) - (x : A) * y = lower w :=
    congrArg Subtype.val hx
  let t : offDiagonalCorner F (1 - e) := ⟨-lower x, (offDiagonalCorner F (1 - e)).neg_mem
    (hlower x)⟩
  have hyComm := (mem_centralizer_singleton_iff F).mp y.property
  have hyComm' : (1 - e) * (y : A) = (y : A) * (1 - e) := by
    rw [sub_mul, mul_sub, one_mul, mul_one, hyComm]
  have htY : (t : A) * (y : A) - (y : A) * (t : A) = lower w := by
    have h := congrArg (cornerProjection F (1 - e)) hx'
    rw [map_sub, cornerProjection_mul_left hyComm', cornerProjection_mul_right hyComm',
      cornerProjection_of_mem he.one_sub (hlower w)] at h
    change (-lower x) * (y : A) - (y : A) * (-lower x) = lower w
    rw [neg_mul, mul_neg, neg_sub_neg]
    exact h
  have htZ : (t : A) * (z : A) - (z : A) * (t : A) ∈ Subalgebra.centralizer F ({e} : Set A) := by
    obtain ⟨htl, htr⟩ := (mem_opposite_corner_iff he).mp t.property
    obtain ⟨hzl, hzr⟩ := (mem_corner_iff he).mp z.property
    rw [mem_centralizer_singleton_iff, mul_sub, sub_mul, ← mul_assoc e (t : A),
      ← mul_assoc e (z : A), htl, hzl, zero_mul, mul_assoc (t : A) (z : A) e,
      mul_assoc (z : A) (t : A) e, htr, hzr, mul_zero]
  let v : Subalgebra.centralizer F ({e} : Set A) :=
    ⟨diagonalProjection F e w - ((t : A) * z - (z : A) * t),
      (Subalgebra.centralizer F ({e} : Set A)).sub_mem
        ((mem_centralizer_singleton_iff F).mpr (commute_diagonalProjection he w)) htZ⟩
  refine ⟨t, v,
    ⟨cornerProjection F e w, cornerProjection_mem F e w⟩, ?_⟩
  change (t : A) * ((y : A) + z) - ((y : A) + z) * t +
    (diagonalProjection F e w - ((t : A) * z - (z : A) * t) + cornerProjection F e w) = w
  rw [mul_add, add_mul, add_sub_add_comm, htY]
  conv_rhs => rw [← diagonal_add_corners F e w]
  change _ + _ + (_ - _ + _) = _ + _ + lower w
  abel

end Algebra

section Normed

variable (F : Type u) [NontriviallyNormedField F] [CompleteSpace F]
    {A : Type v} [NormedRing A] [NormedAlgebra F A] [FiniteDimensional F A] [CompleteSpace A]
    (e : A)

local notation "Levi" => Subalgebra.centralizer F (Set.singleton e)
local notation "Upper" => offDiagonalCorner F e

/-- Conjugation of an upper triangular element by the first coordinate, expressed on
additive coordinates using the ring inverse. -/
def parabolicConjugation (p : A × (Levi × Upper)) : A :=
  p.1 * ((p.2.1 : A) + p.2.2) * Ring.inverse p.1

/-- The parabolic conjugation map is a strict submersion at a unit and a Levi coordinate
whose adjoint action on the off-diagonal summand is surjective. -/
def IdempotentParabolicSubmersionStatement : Prop :=
  IsIdempotentElem e → ∀ (g : Aˣ) (y : Levi) (z : Upper),
    Function.Surjective (offDiagonalAdjoint F e y) →
      ∃ L : A × (Levi × Upper) →L[F] A,
        HasStrictFDerivAt (parabolicConjugation F e) L ((g : A), (y, z)) ∧
          Function.Surjective L

theorem idempotentParabolicSubmersion : IdempotentParabolicSubmersionStatement F e := by
  intro he g y z hy
  let p : A × (Levi × Upper) := ((g : A), (y, z))
  let a := fst F A (Levi × Upper)
  let b := ((Levi).val.toLinearMap.toContinuousLinearMap.comp (fst F Levi Upper) +
    (Upper).subtype.toContinuousLinearMap.comp (snd F Levi Upper)).comp (snd F A (Levi × Upper))
  have hInv := (hasStrictFDerivAt_ringInverse (𝕜 := F) g).comp p a.hasStrictFDerivAt
  have h := (a.hasStrictFDerivAt (x := p).mul' b.hasStrictFDerivAt).mul' hInv
  refine ⟨_, h, ?_⟩
  intro w
  obtain ⟨t, v, s, hw⟩ := exists_parabolic_commutator_add he y z hy
    (((g⁻¹ : Aˣ) : A) * w * (g : A))
  refine ⟨((g : A) * (t : A), (v, s)), ?_⟩
  simp only [a, b, p, Pi.mul_apply, coe_fst', coe_snd', add_apply, comp_apply,
    LinearMap.coe_toContinuousLinearMap', AlgHom.toLinearMap_apply, Subalgebra.val_apply,
    Submodule.subtype_apply, smul_apply, smul_eq_mul, op_smul_eq_mul,
    neg_apply, mulLeftRight_apply, Ring.inverse_unit]
  have hCancel : ((g⁻¹ : Aˣ) : A) * ((g : A) * (t : A)) = (t : A) := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [hCancel]
  calc
    _ = (g : A) * ((t : A) * ((y : A) + z) - ((y : A) + z) * t + ((v : A) + s)) *
        ((g⁻¹ : Aˣ) : A) := by noncomm_ring
    _ = w := by
      rw [hw, ← mul_assoc (g : A) _ (g : A), ← mul_assoc (g : A) _ w, Units.mul_inv,
        one_mul, mul_assoc w, Units.mul_inv, mul_one]

end Normed

end Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer

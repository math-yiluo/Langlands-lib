import Langlands.LinearAlgebra.CliffordSpinorNorm
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # Clifford lifts of determinant-one isometries -/

noncomputable section

universe u v w

namespace Langlands.QuadraticForm

open CliffordAlgebra

variable {R : Type u} {V : Type v} [CommRing R] [AddCommGroup V] [Module R V]
  (Q : QuadraticForm R V)

/-- Pairs of a grade-involution-fixed Clifford unit of reversion norm one
and a linear automorphism of determinant one. The intertwining equation
relates the unit and the automorphism on every vector. -/
def cliffordSpinLiftSubgroup : Subgroup ((CliffordAlgebra Q)ˣ × (V ≃ₗ[R] V)) where
  carrier := {g | involute (g.1 : CliffordAlgebra Q) = g.1 ∧
    reverse (g.1 : CliffordAlgebra Q) * (g.1 : CliffordAlgebra Q) = 1 ∧
    LinearEquiv.det g.2 = 1 ∧
    ∀ v : V, (g.1 : CliffordAlgebra Q) * ι Q v = ι Q (g.2 v) * (g.1 : CliffordAlgebra Q)}
  one_mem' := by
    change involute (1 : CliffordAlgebra Q) = 1 ∧ reverse (1 : CliffordAlgebra Q) * 1 = 1 ∧
      LinearEquiv.det (1 : V ≃ₗ[R] V) = 1 ∧ ∀ v : V, (1 : CliffordAlgebra Q) * ι Q v = ι Q v * 1
    simp
  mul_mem' := by
    rintro ⟨a, g⟩ ⟨b, h⟩ ⟨ha, hna, hg, hga⟩ ⟨hb, hnb, hh, hhb⟩
    let a' : CliffordAlgebra Q := a
    let b' : CliffordAlgebra Q := b
    refine ⟨?_, ?_, ?_, fun v => ?_⟩
    · change involute (a' * b') = a' * b'
      rw [map_mul, show involute a' = a' from ha, show involute b' = b' from hb]
    · change reverse (a' * b') * (a' * b') = 1
      rw [reverse.map_mul]
      calc
        _ = (reverse b' * (reverse a' * a')) * b' := by
          simp only [mul_assoc]
        _ = 1 := by
          rw [show reverse a' * a' = 1 from hna, mul_one]
          exact hnb
    · change LinearEquiv.det (g * h) = 1
      rw [map_mul, hg, hh, mul_one]
    · change ((a : CliffordAlgebra Q) * ↑b) * ι Q v = ι Q (g (h v)) * (↑a * ↑b)
      rw [mul_assoc, hhb v, ← mul_assoc, hga (h v), mul_assoc]
  inv_mem' := by
    rintro ⟨a, g⟩ ⟨ha, hna, hg, hga⟩
    refine ⟨?_, ?_, ?_, fun v => ?_⟩
    · let f : (CliffordAlgebra Q)ˣ →* (CliffordAlgebra Q)ˣ :=
        Units.map (involute (Q := Q)).toMonoidHom
      have h : f a = a := Units.ext ha
      change (f a⁻¹ : CliffordAlgebra Q) = (a⁻¹ : (CliffordAlgebra Q)ˣ)
      rw [map_inv, h]
    · have hrev : reverse (a : CliffordAlgebra Q) = (a⁻¹ : (CliffordAlgebra Q)ˣ) :=
        (Units.mul_left_inj a).mp (hna.trans (Units.inv_mul a).symm)
      have he := congrArg reverse hrev
      rw [reverse_reverse] at he
      change reverse (↑a⁻¹ : CliffordAlgebra Q) * ↑a⁻¹ = 1
      rw [← he, Units.mul_inv]
    · change LinearEquiv.det (g⁻¹) = 1
      rw [map_inv, hg, inv_one]
    · change (↑a⁻¹ : CliffordAlgebra Q) * ι Q v = ι Q (g.symm v) * ↑a⁻¹
      have h := hga (g.symm v)
      rw [LinearEquiv.apply_symm_apply] at h
      have h' := congrArg (fun x : CliffordAlgebra Q => ↑a⁻¹ * x * ↑a⁻¹) h
      simpa only [mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one] using h'.symm

/-- The coefficient group of scalar spin lifts. -/
abbrev CliffordSpinLift := cliffordSpinLiftSubgroup Q

namespace CliffordSpinLift

/-- The underlying Clifford unit. -/
def unit : CliffordSpinLift Q →* (CliffordAlgebra Q)ˣ :=
  (MonoidHom.fst _ _).comp (cliffordSpinLiftSubgroup Q).subtype

/-- The actual action of a lift on the vector space. -/
def vectorAction : CliffordSpinLift Q →* (V ≃ₗ[R] V) :=
  (MonoidHom.snd _ _).comp (cliffordSpinLiftSubgroup Q).subtype

theorem involute_unit (s : CliffordSpinLift Q) : involute (unit Q s : CliffordAlgebra Q) = unit Q s :=
  s.property.1

theorem reverse_mul_unit (s : CliffordSpinLift Q) :
    reverse (unit Q s : CliffordAlgebra Q) * (unit Q s : CliffordAlgebra Q) = 1 :=
  s.property.2.1

theorem det_vectorAction (s : CliffordSpinLift Q) : LinearEquiv.det (vectorAction Q s) = 1 :=
  s.property.2.2.1

theorem unit_mul_vector (s : CliffordSpinLift Q) (v : V) :
    (unit Q s : CliffordAlgebra Q) * ι Q v = ι Q (vectorAction Q s v) * ↑(unit Q s) :=
  s.property.2.2.2 v

theorem unit_conj_vector (s : CliffordSpinLift Q) (v : V) :
    (unit Q s : CliffordAlgebra Q) * ι Q v * ↑(unit Q s)⁻¹ = ι Q (vectorAction Q s v) := by
  rw [unit_mul_vector, mul_assoc, Units.mul_inv, mul_one]

/-- A square root of unity acts as a scalar Clifford unit and acts trivially on vectors. -/
def scalar : rootsOfUnity 2 R →* CliffordSpinLift Q where
  toFun t := ⟨⟨Units.map (algebraMap R (CliffordAlgebra Q)) (t : Rˣ), 1⟩, by
    have ht : (t : Rˣ) ^ 2 = 1 := (mem_rootsOfUnity 2 _).mp t.property
    have ht' : ((t : Rˣ) : R) * ((t : Rˣ) : R) = 1 := by
      simpa only [pow_two, Units.val_mul, Units.val_one] using congrArg Units.val ht
    change involute (algebraMap R (CliffordAlgebra Q) (t : Rˣ)) = _ ∧
      reverse (algebraMap R (CliffordAlgebra Q) (t : Rˣ)) *
        algebraMap R (CliffordAlgebra Q) (t : Rˣ) = 1 ∧
      LinearEquiv.det (1 : V ≃ₗ[R] V) = 1 ∧ ∀ v : V,
        algebraMap R (CliffordAlgebra Q) (t : Rˣ) * ι Q v =
          ι Q v * algebraMap R (CliffordAlgebra Q) (t : Rˣ)
    exact ⟨involute.commutes _, by rw [reverse.commutes, ← map_mul, ht', map_one],
      map_one _, fun v => Algebra.commutes _ _⟩⟩
  map_one' := Subtype.ext (Prod.ext (map_one _) rfl)
  map_mul' t r := Subtype.ext (Prod.ext (map_mul _ _ _) (by simp))

@[simp] theorem unit_scalar (t : rootsOfUnity 2 R) :
    (unit Q (scalar Q t) : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) (t : Rˣ) := rfl

@[simp] theorem vectorAction_scalar (t : rootsOfUnity 2 R) : vectorAction Q (scalar Q t) = 1 := rfl

variable [Invertible (2 : R)]

private theorem algebraMap_injective : Function.Injective (algebraMap R (CliffordAlgebra Q)) := by
  intro a b h
  have h' := congrArg (equivExterior Q) h
  change changeForm changeForm.associated_neg_proof (algebraMap R (CliffordAlgebra Q) a) =
    changeForm changeForm.associated_neg_proof (algebraMap R (CliffordAlgebra Q) b) at h'
  rw [changeForm_algebraMap, changeForm_algebraMap] at h'
  exact (ExteriorAlgebra.algebraMap_leftInverse V).injective h'

/-- The action of a Clifford lift preserves its quadratic form over the coefficient ring. -/
theorem vectorAction_preserves (s : CliffordSpinLift Q) (v : V) : Q (vectorAction Q s v) = Q v := by
  let a := unit Q s
  apply algebraMap_injective Q
  rw [← ι_sq_scalar, ← ι_sq_scalar]
  simp only [← unit_conj_vector]
  have h₁ : ((a : CliffordAlgebra Q) * ι Q v * ↑a⁻¹) * ((a : CliffordAlgebra Q) * ι Q v * ↑a⁻¹) =
      ((a : CliffordAlgebra Q) * (ι Q v * ι Q v)) * ↑a⁻¹ := by
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  rw [h₁, ι_sq_scalar, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

/-- For an orthogonal basis of unit values, the kernel of the vector action consists exactly
of scalar square roots of unity. -/
theorem exists_scalar_of_vectorAction_eq_one {I : Type w} [LinearOrder I]
    (b : Module.Basis I R V) (hb : ∀ i, IsUnit (Q (b i)))
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0)
    (s : CliffordSpinLift Q) (hs : vectorAction Q s = 1) : ∃ t : rootsOfUnity 2 R, scalar Q t = s := by
  obtain ⟨r, hr⟩ := exists_scalar_of_involute_eq_of_commutes_vectors Q b horth hb
    (involute_unit Q s) (fun v => by
      have h := unit_mul_vector Q s v
      rw [hs] at h
      exact h.symm)
  have h := reverse_mul_unit Q s
  rw [← hr, reverse.commutes, ← map_mul, ← map_one (algebraMap R (CliffordAlgebra Q))] at h
  have hsq : r * r = 1 := algebraMap_injective Q h
  let z : Rˣ := Units.mkOfMulEqOne r r hsq
  have hz : z ^ 2 = 1 := by
    apply Units.ext
    rw [pow_two, Units.val_mul]
    exact hsq
  let t : rootsOfUnity 2 R := ⟨z, (mem_rootsOfUnity 2 _).mpr hz⟩
  refine ⟨t, Subtype.ext (Prod.ext (Units.ext ?_) hs.symm)⟩
  exact hr

end CliffordSpinLift

section Field

variable {F : Type u} {W : Type v} [Field F] [AddCommGroup W] [Module F W]
  [FiniteDimensional F W] [Invertible (2 : F)] (Q : QuadraticForm F W)

/-- Over a field, lifting a determinant-one isometry is equivalent to a square spinor norm. -/
theorem exists_cliffordSpinLift_iff
    (hQ : Q.polarBilin.Nondegenerate) (l : List {v : W // Q v ≠ 0}) (hl : Even l.length) :
    (∃ s : CliffordSpinLift Q, CliffordSpinLift.vectorAction Q s = (reflectionWord Q l).toLinearEquiv) ↔
    ∃ t : F, reflectionWordValue Q l = t ^ 2 := by
  rw [← exists_clifford_lift_iff_reflectionWordValue_isSquare Q hQ l hl]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨CliffordSpinLift.unit Q s, CliffordSpinLift.involute_unit Q s,
      CliffordSpinLift.reverse_mul_unit Q s, fun v => ?_⟩
    rw [CliffordSpinLift.unit_conj_vector, hs]
    rfl
  · rintro ⟨a, ha, hn, hv⟩
    refine ⟨⟨⟨a, (reflectionWord Q l).toLinearEquiv⟩, ⟨ha, hn, ?_, fun v => ?_⟩⟩, rfl⟩
    · apply Units.ext
      rw [LinearEquiv.coe_det, det_reflectionWord Q l, hl.neg_one_pow]
      rfl
    · apply (Units.mul_left_inj a⁻¹).mp
      change (a : CliffordAlgebra Q) * ι Q v * ↑a⁻¹ =
        (ι Q (reflectionWord Q l v) * (a : CliffordAlgebra Q)) * ↑a⁻¹
      rw [mul_assoc (ι Q (reflectionWord Q l v)), Units.mul_inv, mul_one]
      exact hv v

/-- Every determinant-one isometry of a regular form lifts over an algebraically closed field. -/
theorem exists_cliffordSpinLift_of_isAlgClosed [IsAlgClosed F]
    (hQ : Q.polarBilin.Nondegenerate) (g : Q.IsometryEquiv Q) (hg : LinearEquiv.det g.toLinearEquiv = 1) :
    ∃ s : CliffordSpinLift Q, CliffordSpinLift.vectorAction Q s = g.toLinearEquiv := by
  have hd : g.toLinearEquiv.toLinearMap.det = 1 := by
    simpa only [LinearEquiv.coe_det, Units.val_one] using congrArg Units.val hg
  obtain ⟨l, hl, rfl⟩ := exists_even_reflectionWord Q hQ g hd
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (reflectionWordValue Q l) zero_lt_two
  exact (exists_cliffordSpinLift_iff Q hQ l hl).mpr ⟨t, ht.symm⟩

end Field

end Langlands.QuadraticForm

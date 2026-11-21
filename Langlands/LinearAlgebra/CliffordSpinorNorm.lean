import Langlands.LinearAlgebra.CliffordEvenCentralizer
import Langlands.LinearAlgebra.CliffordReflectionWord
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! # The spinor norm from even Clifford reflection products -/

noncomputable section

universe u v

namespace Langlands.QuadraticForm

open QuadraticMap CliffordAlgebra

variable {F : Type u} {V : Type v} [Field F] [AddCommGroup V] [Module F V]
  (Q : QuadraticForm F V)

/-- The product of the quadratic values in a reflection expression. -/
def reflectionWordValue (l : List {v : V // Q v ≠ 0}) : F :=
  (l.map (fun x : {x : V // Q x ≠ 0} => Q x)).prod

theorem reflectionWordValue_ne_zero (l : List {v : V // Q v ≠ 0}) :
    reflectionWordValue Q l ≠ 0 := by
  induction l with
  | nil => exact one_ne_zero
  | cons x l ih => exact mul_ne_zero x.property ih

private theorem cliffordReflectionWord_norm (l : List {v : V // Q v ≠ 0}) :
    reverse (cliffordReflectionWord Q l : CliffordAlgebra Q) *
        (cliffordReflectionWord Q l : CliffordAlgebra Q) =
      algebraMap F (CliffordAlgebra Q) (reflectionWordValue Q l) :=
  reverse_mul_cliffordReflectionWord Q l

/-- The Clifford product of an even reflection expression is fixed by the grade involution. -/
theorem involute_cliffordReflectionWord_of_even (l : List {v : V // Q v ≠ 0})
    (hl : Even l.length) :
    involute (cliffordReflectionWord Q l : CliffordAlgebra Q) = cliffordReflectionWord Q l := by
  have h (l : List {v : V // Q v ≠ 0}) :
      involute (cliffordReflectionWord Q l : CliffordAlgebra Q) =
        ((-1 : F) ^ l.length) • (cliffordReflectionWord Q l : CliffordAlgebra Q) := by
    induction l with
    | nil => simp [cliffordReflectionWord]
    | cons x l ih =>
      let c : CliffordAlgebra Q := cliffordReflectionWord Q l
      let a : CliffordAlgebra Q := cliffordVectorUnit Q x
      change involute (c * a) = ((-1 : F) ^ (x :: l).length) • (c * a)
      rw [map_mul, show involute c = _ from ih, show a = ι Q (x : V) from
        cliffordVectorUnit_val Q x, involute_ι, mul_neg, smul_mul_assoc,
        List.length_cons, pow_succ, mul_neg_one, neg_smul]
  simpa only [hl.neg_one_pow, one_smul] using h l

variable [Invertible (2 : F)] [FiniteDimensional F V]

/-- Even Clifford units with the same conjugation on every vector differ by a scalar. -/
theorem exists_smul_of_even_clifford_conj_eq (hQ : Q.polarBilin.Nondegenerate)
    (a b : (CliffordAlgebra Q)ˣ)
    (ha : involute (a : CliffordAlgebra Q) = a)
    (hb : involute (b : CliffordAlgebra Q) = b)
    (h : ∀ v : V, (a : CliffordAlgebra Q) * ι Q v * ↑a⁻¹ =
      (b : CliffordAlgebra Q) * ι Q v * ↑b⁻¹) :
    ∃ t : F, t ≠ 0 ∧ (a : CliffordAlgebra Q) = t • (b : CliffordAlgebra Q) := by
  have hs : Q.polarBilin.IsSymm := ⟨fun x y => polar_comm Q x y⟩
  obtain ⟨c, hc⟩ := LinearMap.BilinForm.exists_orthogonal_basis hs
  have hcu (i : Fin (Module.finrank F V)) : IsUnit (Q (c i)) := by
    have hn := LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate
      (B := Q.polarBilin) (v := c) hc hQ i
    change polar Q (c i) (c i) ≠ 0 at hn
    rw [polar_self] at hn
    exact isUnit_iff_ne_zero.mpr fun hz => hn (by rw [hz, smul_zero])
  let d := b⁻¹ * a
  let f : (CliffordAlgebra Q)ˣ →* (CliffordAlgebra Q)ˣ :=
    Units.map (involute (Q := Q)).toMonoidHom
  have ha' : f a = a := Units.ext ha
  have hb' : f b = b := Units.ext hb
  have hd : involute (d : CliffordAlgebra Q) = d := by
    have he : f d = d := by
      change f (b⁻¹ * a) = b⁻¹ * a
      rw [map_mul, map_inv, ha', hb']
    exact congrArg (fun u : (CliffordAlgebra Q)ˣ => (u : CliffordAlgebra Q)) he
  have hdv (v : V) : Commute (ι Q v) (d : CliffordAlgebra Q) := by
    have hh : ConjAct.toConjAct a • ι Q v = ConjAct.toConjAct b • ι Q v := h v
    have he := congrArg (fun x : CliffordAlgebra Q => ConjAct.toConjAct b⁻¹ • x) hh
    simp only [← mul_smul, ← ConjAct.toConjAct_mul, inv_mul_cancel, ConjAct.toConjAct_one,
      one_smul] at he
    change (d : CliffordAlgebra Q) * ι Q v * ↑d⁻¹ = ι Q v at he
    have he' := congrArg (fun z : CliffordAlgebra Q => z * ↑d) he
    rw [mul_assoc (↑d * ι Q v), Units.inv_mul, mul_one] at he'
    exact he'.symm
  obtain ⟨t, ht⟩ := exists_scalar_of_involute_eq_of_commutes_vectors Q c
    (fun i j hij => hc hij) hcu hd hdv
  refine ⟨t, fun hz => d.ne_zero (by rw [← ht, hz, map_zero]), ?_⟩
  rw [Algebra.smul_def, Algebra.commutes, ht]
  change (a : CliffordAlgebra Q) = (b : CliffordAlgebra Q) * (↑b⁻¹ * (a : CliffordAlgebra Q))
  rw [← mul_assoc, Units.mul_inv, one_mul]

/-- The square class of the product of values is independent of an even reflection expression. -/
theorem reflectionWordValue_eq_sq_mul_of_eq (hQ : Q.polarBilin.Nondegenerate)
    (l m : List {v : V // Q v ≠ 0}) (hl : Even l.length) (hm : Even m.length)
    (h : reflectionWord Q l = reflectionWord Q m) :
    ∃ t : F, t ≠ 0 ∧ reflectionWordValue Q l = t ^ 2 * reflectionWordValue Q m := by
  obtain ⟨t, ht₀, ht⟩ := exists_smul_of_even_clifford_conj_eq Q hQ
    (cliffordReflectionWord Q l) (cliffordReflectionWord Q m)
    (involute_cliffordReflectionWord_of_even Q l hl)
    (involute_cliffordReflectionWord_of_even Q m hm) (fun v => by
      rw [cliffordReflectionWord_conj_of_even Q l hl,
        cliffordReflectionWord_conj_of_even Q m hm, h])
  refine ⟨t, ht₀, (algebraMap F (CliffordAlgebra Q)).injective ?_⟩
  rw [map_mul, ← Algebra.smul_def]
  change algebraMap F (CliffordAlgebra Q) _ = t ^ 2 • algebraMap F (CliffordAlgebra Q) _
  rw [← cliffordReflectionWord_norm Q l, ← cliffordReflectionWord_norm Q m, ht,
    map_smul, smul_mul_smul_comm, pow_two]

/-- A determinant-one isometry has a Clifford lift fixed by grading and of reversion norm one
exactly when the value product of any even reflection expression is a square. -/
theorem exists_clifford_lift_iff_reflectionWordValue_isSquare (hQ : Q.polarBilin.Nondegenerate)
    (l : List {v : V // Q v ≠ 0}) (hl : Even l.length) :
    (∃ b : (CliffordAlgebra Q)ˣ, involute (b : CliffordAlgebra Q) = b ∧
      reverse (b : CliffordAlgebra Q) * (b : CliffordAlgebra Q) = 1 ∧
        ∀ v : V, (b : CliffordAlgebra Q) * ι Q v * ↑b⁻¹ = ι Q (reflectionWord Q l v)) ↔
    ∃ t : F, reflectionWordValue Q l = t ^ 2 := by
  constructor
  · rintro ⟨b, hb, hn, hv⟩
    obtain ⟨t, _, ht⟩ := exists_smul_of_even_clifford_conj_eq Q hQ (cliffordReflectionWord Q l) b
      (involute_cliffordReflectionWord_of_even Q l hl) hb (fun v => by
        rw [cliffordReflectionWord_conj_of_even Q l hl, hv])
    refine ⟨t, (algebraMap F (CliffordAlgebra Q)).injective ?_⟩
    change algebraMap F (CliffordAlgebra Q) (reflectionWordValue Q l) = _
    rw [← cliffordReflectionWord_norm Q l, ht, map_smul, smul_mul_smul_comm, hn,
      ← pow_two, Algebra.algebraMap_eq_smul_one]
  · rintro ⟨t, ht⟩
    have ht₀ : t ≠ 0 := fun hz => reflectionWordValue_ne_zero Q l (by rw [ht, hz, zero_pow (by decide)])
    let C := CliffordAlgebra Q
    let c := cliffordReflectionWord Q l
    let r := Units.map (algebraMap F C).toMonoidHom (Units.mk0 t⁻¹ (inv_ne_zero ht₀))
    let b := r * c
    have hrc : (r : C) = algebraMap F C t⁻¹ := rfl
    have hb : (b : C) = t⁻¹ • (c : C) := by
      rw [Algebra.smul_def]
      exact congrArg (fun x : C => x * (c : C)) hrc
    refine ⟨b, ?_, ?_, fun v => ?_⟩
    · rw [hb, map_smul, involute_cliffordReflectionWord_of_even Q l hl]
    · rw [hb, map_smul, smul_mul_smul_comm, ← pow_two]
      change (t⁻¹ ^ 2) • (reverse (cliffordReflectionWord Q l : C) *
        (cliffordReflectionWord Q l : C)) = 1
      rw [cliffordReflectionWord_norm Q l, ht, Algebra.smul_def, ← map_mul, ← mul_pow,
        inv_mul_cancel₀ ht₀, one_pow, map_one]
    · have hr (y : C) : ConjAct.toConjAct r • y = y := by
        change ((r : C) * y) * ↑r⁻¹ = y
        rw [hrc, Algebra.commutes, ← hrc, mul_assoc, Units.mul_inv, mul_one]
      change ConjAct.toConjAct b • ι Q v = _
      rw [show b = r * c from rfl, ConjAct.toConjAct_mul, mul_smul, hr]
      exact cliffordReflectionWord_conj_of_even Q l hl v

end Langlands.QuadraticForm

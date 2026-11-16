/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 740, 16 November 2026: extract only the proof of M104.004
`exists_idempotent_lift_of_surjective_henselianRing_ker` from
Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean
(lines 90–136) at commit fbd320cd8b1b06487c58227e92eb135794267709 into
Langlands.NYLL; import only the published Henselian.Statements module, state
the theorem as its
`exists_idempotent_lift_of_surjective_henselianRing_kerStatement` applied to
the source binders and open it with `unfold`. The source proof's three calls
of the not yet published M104.001–.003 theorems are replaced by their source
tactic proofs (lines 30–32, 39–43 and 53–83), inlined as local `have`s for
the ideal `RingHom.ker f`; the rest of the source tactic proof is unchanged.
The noncomputable section and the unused universes u v are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.Statements

/-!
# Idempotents lift along a surjection with Henselian kernel (NYLL M104.004)

Let `f : R →+* S` be surjective with `R` Henselian along `ker f`. Every
idempotent `e` of `S` is the image of an idempotent of `R`: lift `e` to any
`a0`, which is then a root of `X ^ 2 - X` modulo `ker f` at which the
derivative `2X - 1` is a unit, and apply Hensel's lemma.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField

/-- Idempotents lift along a surjective ring map whose kernel is a Henselian
ideal.

This is the `X^2 - X` simple-root form of Hensel's lemma.  At an idempotent,
the derivative `2X - 1` is a unit because its square is `1`. -/
theorem exists_idempotent_lift_of_surjective_henselianRing_ker
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f)
    [HenselianRing R (RingHom.ker f)]
    (e : S) (he : IsIdempotentElem e) :
    exists_idempotent_lift_of_surjective_henselianRing_kerStatement f hf e he := by
  unfold exists_idempotent_lift_of_surjective_henselianRing_kerStatement
  cases subsingleton_or_nontrivial R with
  | inl hR =>
      have hS : Subsingleton S := by
        constructor
        intro x y
        rcases hf x with ⟨a, rfl⟩
        rcases hf y with ⟨b, rfl⟩
        exact congrArg f (Subsingleton.elim a b)
      exact ⟨0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  | inr hR =>
      let : Nontrivial R := hR
      rcases hf e with ⟨a0, ha0⟩
      let p : Polynomial R := Polynomial.X ^ 2 - Polynomial.X
      -- Source proof of M104.001 (lines 30–32), inlined.
      have hpmonic : p.Monic := by
        dsimp [p]
        exact Polynomial.monic_X_pow_sub (by
          rw [Polynomial.degree_X]
          norm_num)
      have ha0_quotient :
          IsIdempotentElem
            (Ideal.Quotient.mk (RingHom.ker f) a0) := by
        rw [IsIdempotentElem]
        rw [← map_mul, Ideal.Quotient.eq]
        rw [RingHom.mem_ker]
        simp [ha0, he.eq]
      -- Source proof of M104.002 (lines 39–43) for `I := RingHom.ker f`, inlined.
      have hroot : p.eval a0 ∈ RingHom.ker f := by
        dsimp [p]
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        change
          Ideal.Quotient.mk (RingHom.ker f)
            ((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).eval a0) = 0
        simpa [pow_two] using sub_eq_zero.mpr ha0_quotient.eq
      -- Source proof of M104.003 (lines 53–83) for `I := RingHom.ker f`, inlined.
      have hsimple :
          IsUnit
            (Ideal.Quotient.mk (RingHom.ker f) (p.derivative.eval a0)) := by
        dsimp [p]
        rw [isUnit_iff_exists]
        refine
          ⟨Ideal.Quotient.mk (RingHom.ker f)
            ((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).derivative.eval a0),
            ?_, ?_⟩
        · simp only [pow_two, Polynomial.derivative_mul,
            Polynomial.derivative_X, one_mul, mul_one, Polynomial.eval_sub,
            Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, map_sub, map_add,
            map_one]
          calc
            (Ideal.Quotient.mk (RingHom.ker f) a0 + Ideal.Quotient.mk (RingHom.ker f) a0 - 1) *
                (Ideal.Quotient.mk (RingHom.ker f) a0 +
                  Ideal.Quotient.mk (RingHom.ker f) a0 - 1) =
              1 + (4 * (Ideal.Quotient.mk (RingHom.ker f) a0 *
                  Ideal.Quotient.mk (RingHom.ker f) a0) -
                4 * Ideal.Quotient.mk (RingHom.ker f) a0) := by
                ring
            _ = 1 := by
                rw [ha0_quotient.eq]
                ring
        · simp only [pow_two, Polynomial.derivative_mul,
            Polynomial.derivative_X, one_mul, mul_one, Polynomial.eval_sub,
            Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, map_sub, map_add,
            map_one]
          calc
            (Ideal.Quotient.mk (RingHom.ker f) a0 + Ideal.Quotient.mk (RingHom.ker f) a0 - 1) *
                (Ideal.Quotient.mk (RingHom.ker f) a0 +
                  Ideal.Quotient.mk (RingHom.ker f) a0 - 1) =
              1 + (4 * (Ideal.Quotient.mk (RingHom.ker f) a0 *
                  Ideal.Quotient.mk (RingHom.ker f) a0) -
                4 * Ideal.Quotient.mk (RingHom.ker f) a0) := by
                ring
            _ = 1 := by
                rw [ha0_quotient.eq]
                ring
      rcases HenselianRing.is_henselian p hpmonic a0 hroot hsimple with
        ⟨a, haroot, hacongr⟩
      refine ⟨a, ?_, ?_⟩
      · change a * a = a
        exact sub_eq_zero.mp (by simpa [p, pow_two] using haroot)
      · have hsub : f (a - a0) = 0 := RingHom.mem_ker.mp hacongr
        rw [map_sub, ha0, sub_eq_zero] at hsub
        exact hsub

end Langlands.NYLL.ValuationTheory.DiscreteValuationField

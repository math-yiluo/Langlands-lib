/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 94, 2026-11-11: adapt M242.001 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 to prove the published closed
normal_of_profiniteStatement, with independent universes u, v, w. Import the
published statement; prefix the namespace with Langlands.NYLL; introduce the
complete original telescope inside the proof. The source proof body is unchanged.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.ProfiniteInvariant.NormalStatement

/-!
# Normality of maximal residue extensions of profinite invariant rings

The proof of NYLL M242.001, for the exact published closed statement.
-/

universe u v w

namespace Langlands.NYLL.RamificationTheory.Ideal.Quotient

noncomputable section

open scoped Pointwise

attribute [local instance] Ideal.Quotient.field

/-- NYLL M242.001: the maximal residue extension of a profinite invariant ring
is normal, with the complete original action and topology hypotheses. -/
theorem normal_of_profinite : normal_of_profiniteStatement.{u, v, w} := by
  intro A B _ _ _ G _ _ _ _ _ _ _ _ _ _ _ P Q _ _ _
  cases subsingleton_or_nontrivial B
  · cases ‹Q.IsMaximal›.ne_top (Subsingleton.elim _ _)
  have hIntegral : Algebra.IsIntegral A B :=
    Algebra.IsInvariant.isIntegral_of_profinite (G := G)
  constructor
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨N, hN⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (stabilizer_isOpen G x) (MulAction.mem_stabilizer_iff.mpr (one_smul G x))
  let B' := FixedPoints.subalgebra A B N.1.1
  let x' : B' := ⟨x, fun g ↦ hN g.2⟩
  let j : B' →ₐ[A] B := B'.val
  have hjx : j x' = x := rfl
  let : Algebra.IsInvariant A B' (G ⧸ N.1.1) := inferInstance
  cases nonempty_fintype (G ⧸ N.1.1)
  obtain ⟨p, hp, _hdegree, hpmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic
      (Algebra.IsInvariant.charpoly_mem_lifts A B' (G ⧸ N.1.1) x')
      (MulSemiringAction.monic_charpoly (G ⧸ N.1.1) x')
  let qB : B →+* B ⧸ Q := Ideal.Quotient.mk Q
  let qB' : B' →+* B ⧸ Q := qB.comp j.toRingHom
  have hroot : Polynomial.aeval (Ideal.Quotient.mk Q x)
      (p.map (algebraMap A (A ⧸ P))) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    have hmap :
        (p.map (algebraMap A B')).map qB' =
          p.map ((algebraMap (A ⧸ P) (B ⧸ Q)).comp
            (Ideal.Quotient.mk P)) := by
      rw [Polynomial.map_map]
      apply congrArg (fun f : A →+* B ⧸ Q ↦ p.map f)
      ext a
      rfl
    calc
      Polynomial.eval (Ideal.Quotient.mk Q x)
          ((p.map (algebraMap A (A ⧸ P))).map
            (algebraMap (A ⧸ P) (B ⧸ Q))) =
          Polynomial.eval (Ideal.Quotient.mk Q x)
            ((p.map (algebraMap A B')).map qB') := by
        rw [hmap, Polynomial.map_map, Ideal.Quotient.algebraMap_eq]
      _ = 0 := by
        rw [hp, show Ideal.Quotient.mk Q x = qB' x' from rfl,
          Polynomial.eval_map_apply, MulSemiringAction.eval_charpoly, map_zero]
  have hdiv := minpoly.dvd (A ⧸ P) (Ideal.Quotient.mk Q x)
    (p := p.map (algebraMap A (A ⧸ P))) hroot
  refine Polynomial.Splits.of_dvd ?_ ?_ ((Polynomial.map_dvd_map' _).mpr hdiv)
  · rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq A B', ← Polynomial.map_map, hp,
      MulSemiringAction.charpoly_eq, Polynomial.map_prod]
    exact Polynomial.Splits.prod
      (fun _ _ ↦ (Polynomial.Splits.X_sub_C _).map _)
  · exact ((hpmonic.map _).map _).ne_zero

end

end Langlands.NYLL.RamificationTheory.Ideal.Quotient

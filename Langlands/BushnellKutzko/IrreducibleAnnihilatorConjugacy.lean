import Langlands.MathlibBase

/-! # Conjugacy of endomorphisms killed by one irreducible polynomial

Over a finite field `k`, two endomorphisms of a finite-dimensional vector space which are
annihilated by the same irreducible polynomial `p` are conjugate. Each endomorphism makes the
space a vector space over the field `k[X]/(p)`; both have the same cardinality, hence the same
dimension over `k[X]/(p)`, and an isomorphism of these vector spaces intertwines them.
-/

open Polynomial

namespace Langlands.BushnellKutzko

/-- Two endomorphisms of a finite-dimensional vector space over a finite field which are killed by
the same irreducible polynomial are conjugate by a linear automorphism. -/
theorem exists_linearEquiv_conj_of_aeval_irreducible {k W : Type*} [Field k] [Finite k]
    [AddCommGroup W] [Module k W] [Module.Finite k W] {p : k[X]} (hp : Irreducible p)
    {A B : Module.End k W} (hA : aeval A p = 0) (hB : aeval B p = 0) :
    ∃ φ : W ≃ₗ[k] W, ∀ w, φ (A w) = B (φ w) := by
  classical
  have htors : ∀ C : Module.End k W, aeval C p = 0 →
      Module.IsTorsionBySet k[X] (Module.AEval' C) (Ideal.span {p} : Set k[X]) := by
    intro C hC
    rw [← RingHom.mem_ker, ← Module.AEval.annihilator_eq_ker_aeval (M := W), Module.mem_annihilator,
      ← Module.IsTorsionBy, ← Module.isTorsionBySet_singleton_iff,
      Module.isTorsionBySet_iff_is_torsion_by_span] at hC
    exact hC
  let I : Ideal k[X] := Ideal.span {p}
  have : I.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp
  let : Field (k[X] ⧸ I) := Ideal.Quotient.field I
  have : FiniteDimensional k (k[X] ⧸ I) := (AdjoinRoot.powerBasis hp.ne_zero).finite
  have : Finite (k[X] ⧸ I) := Module.finite_of_finite k
  have : Finite W := Module.finite_of_finite k
  let : Module (k[X] ⧸ I) (Module.AEval' A) := (htors A hA).module
  let : Module (k[X] ⧸ I) (Module.AEval' B) := (htors B hB).module
  have : Finite (Module.AEval' A) := inferInstanceAs (Finite W)
  have : Finite (Module.AEval' B) := inferInstanceAs (Finite W)
  have hcardA := Module.natCard_eq_pow_finrank (K := k[X] ⧸ I) (V := Module.AEval' A)
  have hcardB := Module.natCard_eq_pow_finrank (K := k[X] ⧸ I) (V := Module.AEval' B)
  have hAB : Nat.card (Module.AEval' A) = Nat.card (Module.AEval' B) := rfl
  have hK : 1 < Nat.card (k[X] ⧸ I) := Finite.one_lt_card
  have hrank : Module.finrank (k[X] ⧸ I) (Module.AEval' A) =
      Module.finrank (k[X] ⧸ I) (Module.AEval' B) :=
    Nat.pow_right_injective hK (hcardA.symm.trans (hAB.trans hcardB))
  let e := LinearEquiv.ofFinrankEq (Module.AEval' A) (Module.AEval' B) hrank
  have hCA (c : k) (m : Module.AEval' A) : c • m = (Ideal.Quotient.mk I (C c)) • m := by
    change c • m = (C c) • m
    rw [← algebraMap_eq, algebraMap_smul]
  have hCB (c : k) (m : Module.AEval' B) : c • m = (Ideal.Quotient.mk I (C c)) • m := by
    change c • m = (C c) • m
    rw [← algebraMap_eq, algebraMap_smul]
  have hXA (w : W) : Module.AEval'.of A (A w) = (Ideal.Quotient.mk I X) • Module.AEval'.of A w :=
    (Module.AEval'.X_smul_of A w).symm
  have hXB (m : Module.AEval' B) :
      (Module.AEval'.of B).symm ((Ideal.Quotient.mk I X) • m) = B ((Module.AEval'.of B).symm m) :=
    Module.AEval'.of_symm_X_smul B m
  refine ⟨{ toFun := fun w => (Module.AEval'.of B).symm (e (Module.AEval'.of A w))
            invFun := fun w => (Module.AEval'.of A).symm (e.symm (Module.AEval'.of B w))
            map_add' := by intro v w; simp
            map_smul' := by
              intro c w
              simp only [RingHom.id_apply]
              rw [map_smul, hCA, map_smul, ← hCB, map_smul]
            left_inv := by intro w; simp
            right_inv := by intro w; simp }, ?_⟩
  intro w
  change (Module.AEval'.of B).symm (e (Module.AEval'.of A (A w))) =
    B ((Module.AEval'.of B).symm (e (Module.AEval'.of A w)))
  rw [hXA, map_smul, hXB]

end Langlands.BushnellKutzko

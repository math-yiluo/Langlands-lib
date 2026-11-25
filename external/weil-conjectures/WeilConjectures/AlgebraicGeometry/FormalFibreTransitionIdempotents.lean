/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalFibreCohomology
import WeilConjectures.AlgebraicGeometry.NilpotentBaseChangeIdempotents

/-! # One-step lifting of infinitesimal-fibre idempotents -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Restriction across one infinitesimal-fibre transition uniquely lifts idempotents.
Source: Stacks Project, Tags 0G7X, 09ZU, 04EX and 00EE.
(blueprint: lem-weil-pbc-formal-fibre-transition-idempotents)

Proof: Write A = O_(S,s) and m = its maximal ideal. The quotient map
A/m^(n+2) → A/m^(n+1) has kernel J, the image of m^(n+1). Its square is zero:
2(n+1) ≥ n+2, so m^(2(n+1)) maps to zero in A/m^(n+2).
The quotient by J is canonically A/m^(n+1), with the quotient map identified with
factorPow. Pullback pasting identifies the base change of X_(n+1) along this
quotient with X_n, and its projection with formalFibreTransition f s n.
Apply nilpotent_baseChange_idempotents with N = 2 and transport along this
identification. This gives existence and uniqueness among idempotent sections,
including 0 and 1 and the unique section of an empty fibre; it makes no claim
that all global sections lift. -/
theorem formalFibreTransition_idempotents {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (n : ℕ) (e : Γ(formalFibre f s n, ⊤)) (he : IsIdempotentElem e) :
    ∃! e' : {a : Γ(formalFibre f s (n + 1), ⊤) // IsIdempotentElem a},
      (formalFibreTransition f s n).appTop.hom e'.val = e := by
  classical
  let m := IsLocalRing.maximalIdeal (S.presheaf.stalk s)
  let B := (S.presheaf.stalk s) ⧸ m ^ (n + 1 + 1)
  let r := Ideal.Quotient.factorPow m (Nat.le_succ (n + 1))
  let J : Ideal B := RingHom.ker r
  have hJ : J ^ 2 = ⊥ := by
    rw [show J = (m ^ (n + 1)).map (Ideal.Quotient.mk (m ^ (n + 1 + 1))) from
      Ideal.Quotient.factor_ker _, ← Ideal.map_pow, ← pow_mul]
    apply (Ideal.map_eq_bot_iff_le_ker _).mpr
    rw [Ideal.mk_ker]
    exact Ideal.pow_le_pow_right (by omega)
  have hr : Function.Surjective r := Ideal.Quotient.factor_surjective _
  let ε := r.quotientKerEquivOfSurjective hr
  let α := Scheme.Spec.mapIso ε.toCommRingCatIso.op
  let q := Spec.map (CommRingCat.ofHom r)
  let qJ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let g := pullback.fst (formalFibreBaseMap S s (n + 1)) f
  have hq : q = α.hom ≫ qJ := by
    change Spec.map (CommRingCat.ofHom r) =
      Spec.map (CommRingCat.ofHom ε.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
    rw [← Spec.map_comp]
    congr 1
  have hp : IsPullback (formalFibreTransition f s n)
      (pullback.fst (formalFibreBaseMap S s n) f) g q := by
    apply IsPullback.of_right (h₁₂ := pullback.snd (formalFibreBaseMap S s (n + 1)) f)
      (h₂₂ := formalFibreBaseMap S s (n + 1))
    · simpa [formalFibreTransition, q, r, m, ← formalFibreBaseMap_transition] using
        (IsPullback.of_hasPullback (formalFibreBaseMap S s n) f).flip
    · simp [formalFibreTransition, g, q, r, m]
    · exact (IsPullback.of_hasPullback (formalFibreBaseMap S s (n + 1)) f).flip
  have hp' : IsPullback (formalFibreTransition f s n)
      (pullback.fst (formalFibreBaseMap S s n) f ≫ α.hom) g qJ := by
    apply hp.of_iso (Iso.refl _) (Iso.refl _) α (Iso.refl _)
    · simp
    · simp
    · simp
    · simpa using hq
  obtain ⟨β, hβ⟩ : ∃ β : formalFibre f s n ≅ pullback g qJ,
      β.hom ≫ pullback.fst g qJ = formalFibreTransition f s n :=
    ⟨hp'.isoPullback, hp'.isoPullback_hom_fst⟩
  have hi := (nilpotent_baseChange_idempotents B J 2 (by omega) hJ
    (formalFibre f s (n + 1)) g).2.2.2.2
  have hpred (a : {a : Γ(formalFibre f s (n + 1), ⊤) // IsIdempotentElem a}) :
      (formalFibreTransition f s n).appTop.hom a.val = e ↔
      (pullback.fst g qJ).appTop.hom a.val = β.inv.appTop.hom e := by
    have inverse {Y Z : Scheme.{u}} (γ : Y ≅ Z) (x : Γ(Z, ⊤)) :
        γ.inv.appTop.hom (γ.hom.appTop.hom x) = x := by
      change ((γ.hom.appTop ≫ γ.inv.appTop).hom) x = x
      rw [← Scheme.Hom.comp_appTop, γ.inv_hom_id, Scheme.Hom.id_appTop]
      rfl
    rw [← hβ, Scheme.Hom.comp_appTop]
    change β.hom.appTop.hom ((pullback.fst g qJ).appTop.hom a.val) = e ↔ _
    constructor
    · intro h
      exact (inverse β _).symm.trans (congrArg (fun x ↦ β.inv.appTop.hom x) h)
    · intro h
      exact (congrArg (fun x ↦ β.hom.appTop.hom x) h).trans (inverse β.symm e)
  have H := hi (β.inv.appTop.hom e) (he.map β.inv.appTop.hom)
  exact (existsUnique_congr hpred).mpr H

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Ring.Idempotent
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal
import WeilConjectures.AlgebraicGeometry.SchemeClopenIdempotent

/-!
# Idempotents under nilpotent base change

Source: Stacks Project, More on Morphisms, Tags 09ZU and 04EX; Derived Categories of Schemes,
proof of Tag 0G7X, using Algebra, Tag 00EE
(blueprint: lem-weil-pbc-base-change-nilpotent-thickening-idempotents).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Base change by a nilpotent quotient is a finite order thickening, and restriction
of global sections uniquely lifts idempotents.
Source: Stacks Project, Tags 09ZU, 04EX, and the equal-topological-spaces step of the proof
of Tag 0G7X, with Tag 00EE.
(blueprint: lem-weil-pbc-base-change-nilpotent-thickening-idempotents).

Proof plan:
1. Apply `lem-weil-pbc-quotient-base-change-closed-immersion-ideal` to `g` and `J`.
The first projection is a closed immersion with defining ideal sheaf `J O_Y`; on each
affine open with ring `B` its ideal is `JB`.
2. The same lemma identifies the `N`th power with `J^N O_Y`, which vanishes by the
hypothesis. Thus the ideal sheaf has `N`th power zero, giving a finite order thickening.
3. Mathlib's `Scheme.IdealSheafData.support_pow` identifies the support of the
positive power with the support of the kernel. The zero ideal sheaf has full support.
By `Scheme.Hom.support_ker`, the closure of the image is therefore all of `Y`.
The image is closed, so the closed immersion is surjective, hence a homeomorphism.
4. By `lem-weil-pbc-scheme-clopen-idempotent`, idempotent global sections correspond
bijectively to clopen subsets, compatibly with pullback. Inverse image along the
homeomorphism is a bijection on clopen subsets. Hence each idempotent on the base change
has exactly one idempotent lift. This does not require surjectivity on all global sections. -/
theorem nilpotent_baseChange_idempotents
    (A : Type u) [CommRing A] (J : Ideal A) (N : ℕ) (hN : 1 ≤ N) (hJ : J ^ N = ⊥)
    (Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of A)) :
    let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
    let Y₀ := pullback g q
    let i : Y₀ ⟶ Y := pullback.fst g q
    IsClosedImmersion i ∧ i.ker ^ N = ⊥ ∧ IsFiniteOrderThickening i ∧
      IsHomeomorph i ∧
      (∀ e₀ : Γ(Y₀, ⊤), IsIdempotentElem e₀ →
        ∃! e : {e : Γ(Y, ⊤) // IsIdempotentElem e},
          (Scheme.Γ.map i.op).hom e.val = e₀) := by
  classical
  dsimp only
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let i := pullback.fst g q
  obtain ⟨hi, hker, _⟩ := quotientBaseChange_closedImmersion_ideal g J
  have : IsClosedImmersion i := hi
  have hpow : i.ker ^ N = ⊥ := by
    rw [hker, (quotientBaseChange_extendedIdeal_mul_pow g).2 J N hN, hJ]
    have hb : Scheme.IdealSheafData.ofIdealTop (⊥ : Ideal Γ(Spec
        (CommRingCat.of A), ⊤)) = ⊥ := by
      ext U : 2
      simp [Scheme.IdealSheafData.ofIdealTop_ideal]
    simp [hb]
  have hsupport : i.ker.support = ⊤ := by
    rw [← Scheme.IdealSheafData.support_pow i.ker N (by omega), hpow]
    rfl
  have hsurj : Function.Surjective i := by
    rw [← Set.range_eq_univ, ← i.isClosedEmbedding.isClosed_range.closure_eq,
      ← Scheme.Hom.support_ker, hsupport]
    rfl
  have hhomeo : IsHomeomorph i :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨i.isClosedEmbedding.isEmbedding, hsurj⟩
  have hfinite : IsFiniteOrderThickening i := by
    refine ⟨N - 1, hi, ?_⟩
    simpa only [Nat.sub_add_cancel hN] using hpow
  refine ⟨hi, hpow, hfinite, hhomeo, ?_⟩
  intro e₀ he₀
  have h₀ := (scheme_clopen_idempotent (pullback g q)).1 e₀ he₀
  let U := i '' idempotentOpen e₀
  have hU : IsOpen U ∧ IsClosed U :=
    ⟨hhomeo.isOpenMap _ h₀.2.1, i.isClosedEmbedding.isClosedMap _ h₀.2.2.1⟩
  obtain ⟨e, he, heU⟩ := (scheme_clopen_idempotent Y).2.1.2 U hU
  have hlocus : idempotentOpen (i.appTop e) = idempotentOpen e₀ := by
    rw [(scheme_clopen_idempotent Y).2.2.2 i e he |>.2, heU]
    exact Set.preimage_image_eq _ i.isClosedEmbedding.injective
  have heq : i.appTop e = e₀ := by
    have h : (⟨i.appTop e, he.map i.appTop.hom⟩ :
        {e : Γ(pullback g q, ⊤) // IsIdempotentElem e}) = ⟨e₀, he₀⟩ :=
      (scheme_clopen_idempotent (pullback g q)).2.1.1 hlocus
    exact congrArg Subtype.val h
  refine ⟨⟨e, he⟩, heq, ?_⟩
  intro e' he'
  apply (scheme_clopen_idempotent Y).2.1.1
  apply Set.preimage_injective.mpr hsurj
  rw [← (scheme_clopen_idempotent Y).2.2.2 i e'.val e'.property |>.2,
    ← (scheme_clopen_idempotent Y).2.2.2 i e he |>.2]
  change i.appTop e'.val = e₀ at he'
  rw [he', heq]

end AlgebraicGeometry

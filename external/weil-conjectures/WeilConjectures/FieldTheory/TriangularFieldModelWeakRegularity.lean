/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.TriangularFieldModelEquations
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Regular.RegularSequence

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Weak regularity of triangular model equations

Source: Stacks Project, proof of Tag 07BV, the successive monic equations, with the
localization presentation of Tag 08JZ
(blueprint: lem-weil-pbc-triangular-field-model-weak-regularity).
-/

@[expose] public section

universe u

namespace FieldTheory

private theorem monic_mul_mem_extended_ideal
    {A : Type*} [CommRing A] (I : Ideal A) (p q : Polynomial A) (hp : p.Monic)
    (hq : p * q ∈ I.map Polynomial.C) : q ∈ I.map Polynomial.C := by
  have hker : RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk I)) =
      I.map Polynomial.C := by
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
  have heq : Polynomial.map (Ideal.Quotient.mk I) (p * q) = 0 := by
    simpa only [← hker, RingHom.mem_ker, Polynomial.coe_mapRingHom] using hq
  rw [Polynomial.map_mul] at heq
  have hz := (hp.map (Ideal.Quotient.mk I)).mul_right_eq_zero_iff.mp heq
  simpa only [← hker, RingHom.mem_ker, Polynomial.coe_mapRingHom] using hz

private theorem fresh_monic_mul_mem_extended_ideal
    {R σ τ : Type*} [CommRing R] (f : σ → τ) (t : τ)
    (ht : ∀ s, f s ≠ t) (I : Ideal (MvPolynomial σ R))
    (p : Polynomial (MvPolynomial σ R)) (hp : p.Monic)
    (q : MvPolynomial τ R)
    (hq : Polynomial.eval₂ (MvPolynomial.rename f).toRingHom (MvPolynomial.X t) p * q ∈
      I.map (MvPolynomial.rename f).toRingHom) :
    q ∈ I.map (MvPolynomial.rename f).toRingHom := by
  classical
  let σ' := {s : τ // s ≠ t}
  let g : σ → σ' := fun s ↦ ⟨f s, ht s⟩
  let e : MvPolynomial τ R ≃ₐ[R] Polynomial (MvPolynomial σ' R) :=
    (MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe t).symm).trans
      (MvPolynomial.optionEquivLeft R σ')
  let a : MvPolynomial σ R →+* MvPolynomial σ' R :=
    (MvPolynomial.rename g).toRingHom
  have he : e.toRingHom.comp (MvPolynomial.rename f).toRingHom = Polynomial.C.comp a := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply]
      change e (MvPolynomial.rename f (MvPolynomial.C r)) =
        Polynomial.C (MvPolynomial.rename g (MvPolynomial.C r))
      simp only [MvPolynomial.rename_C]
      change (MvPolynomial.optionEquivLeft R σ')
        (MvPolynomial.rename (Equiv.optionSubtypeNe t).symm (MvPolynomial.C r)) = _
      rw [MvPolynomial.rename_C]
      exact MvPolynomial.optionEquivLeft_C R σ' r
    · intro s
      change e (MvPolynomial.rename f (MvPolynomial.X s)) =
        Polynomial.C (MvPolynomial.rename g (MvPolynomial.X s))
      simp only [MvPolynomial.rename_X]
      change (MvPolynomial.optionEquivLeft R σ')
        (MvPolynomial.rename (Equiv.optionSubtypeNe t).symm (MvPolynomial.X (f s))) = _
      rw [MvPolynomial.rename_X, Equiv.optionSubtypeNe_symm_of_ne (ht s)]
      exact MvPolynomial.optionEquivLeft_X_some R σ' (g s)
  have het : e (MvPolynomial.X t) = Polynomial.X := by
    change (MvPolynomial.optionEquivLeft R σ')
      (MvPolynomial.rename (Equiv.optionSubtypeNe t).symm (MvPolynomial.X t)) = _
    rw [MvPolynomial.rename_X, Equiv.optionSubtypeNe_symm_self]
    exact MvPolynomial.optionEquivLeft_X_none R σ'
  have hep : e (Polynomial.eval₂ (MvPolynomial.rename f).toRingHom (MvPolynomial.X t) p) =
      p.map a := by
    change (e.toRingHom.comp (Polynomial.eval₂RingHom _ _)) p = _
    have hhom : e.toRingHom.comp (Polynomial.eval₂RingHom
        (MvPolynomial.rename f).toRingHom (MvPolynomial.X t)) = Polynomial.mapRingHom a := by
      apply Polynomial.ringHom_ext
      · intro b
        simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
          Polynomial.coe_mapRingHom, Polynomial.map_C] using congrArg (fun F ↦ F b) he
      · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
          Polynomial.coe_mapRingHom, Polynomial.map_X]
        change e (MvPolynomial.X t) = Polynomial.X
        exact het
    exact congrArg (fun F ↦ F p) hhom
  have hI : (I.map (MvPolynomial.rename f).toRingHom).map e.toRingHom =
      (I.map a).map Polynomial.C := by
    rw [Ideal.map_map, he, ← Ideal.map_map]
  have hmem : p.map a * e q ∈ (I.map a).map Polynomial.C := by
    rw [← hI, ← hep, ← map_mul]
    exact Ideal.mem_map_of_mem e.toRingHom hq
  have hq' := monic_mul_mem_extended_ideal (I.map a) (p.map a) (e q) (hp.map a) hmem
  rw [← hI] at hq'
  exact (Ideal.apply_mem_of_equiv_iff (f := e.toRingEquiv)).mp hq'

/-- Triangular monic equations after a localization equation form a weakly regular
sequence. This is a statement about arbitrary monic equations, with no extension field.
Source: Stacks Project, Algebra, proof of Tags 07BV and 08JZ
(blueprint: lem-weil-pbc-triangular-field-model-weak-regularity).

Proof:
1. In the polynomial domain over `k`, `h T - 1` is nonzero (its constant coefficient
   as a polynomial in `T` is `-1`), hence multiplication by it is injective.
2. Quotienting by that equation identifies the coefficient ring with `k[X,1/h]`.
   After additionally quotienting by the first `i` monic equations, the whole ring
   is a polynomial ring in the remaining variables over the successive quotient
   `B i = k[X,1/h,Y₀,...,Yᵢ₋₁]/(P₀,...,Pᵢ₋₁)`. This follows by the localization
   presentation and successive quotient isomorphisms, since no earlier equation
   involves a later variable.
3. The next equation is the image of `p i` in `B i[Yᵢ]`, with the still later
   variables adjoined to its coefficient ring. Its leading coefficient is one:
   ring maps preserve monicity. Multiplication by a monic polynomial over any
   commutative ring is injective, by comparing the highest nonzero coefficient
   of a product. Thus it is a nonzerodivisor in the successive quotient.
4. Transport this injectivity through the quotient isomorphisms of step 2. These
   are exactly all the conditions `regular_mod_prev` for a weakly regular sequence.
For `r = 0` only step 1 is needed. A monic constant equation may be `1`, so this
statement deliberately asserts weak regularity only: later quotients may be zero.
No nontriviality of the final quotient is assumed or asserted. -/
theorem triangularFieldModelEquations_isWeaklyRegular
    (k : Type u) [Field k] (d r : ℕ) (h : MvPolynomial (Fin d) k)
    (p : (i : Fin r) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k))
    (hh : h ≠ 0) (hp : ∀ i, (p i).Monic) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin (d + 1 + r)) k)
      (triangularFieldModelEquations k d r h p) := by
  classical
  have _hh := hh
  let A := MvPolynomial (Fin (d + 1 + r)) k
  let fs := triangularFieldModelEquations k d r h p
  have hsmul (I : Ideal A) : I • (⊤ : Submodule A A) = I := by
    exact (Ideal.smul_eq_mul I ⊤).trans (Ideal.mul_top I)
  constructor
  intro j hj
  rw [hsmul]
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
  intro q hq
  change fs[j] * q ∈ Ideal.ofList (fs.take j) at hq
  change q ∈ Ideal.ofList (fs.take j)
  cases j with
  | zero =>
    have hne : fs[0] ≠ 0 := by
      intro hz
      have he := congrArg (MvPolynomial.eval (fun _ ↦ (0 : k))) hz
      simp [fs, triangularFieldModelEquations] at he
    have hz : fs[0] * q = 0 := by simpa using hq
    have hq0 := (mul_eq_zero.mp hz).resolve_left hne
    simp [hq0]
  | succ i =>
    have hir : i < r := by simpa [fs] using hj
    let f : Fin (d + 1 + i) → Fin (d + 1 + r) := fun a ↦ ⟨a.val, by omega⟩
    let t : Fin (d + 1 + r) := ⟨d + 1 + i, by omega⟩
    let F := (MvPolynomial.rename f (R := k)).toRingHom
    let I := Ideal.ofList (fs.take (i + 1))
    have hI : (I.comap F).map F = I := by
      apply le_antisymm Ideal.map_comap_le
      apply Ideal.span_le.mpr
      intro a ha
      obtain ⟨b, hb, hab⟩ := List.mem_take_iff_getElem.mp ha
      have hbi : b < i + 1 := (Nat.lt_min.mp hb).1
      have hpre : ∃ a' : MvPolynomial (Fin (d + 1 + i)) k, F a' = fs[b] := by
        cases b with
        | zero =>
          refine ⟨MvPolynomial.rename (fun a : Fin d ↦
            (⟨a.val, by omega⟩ : Fin (d + 1 + i))) h *
            MvPolynomial.X ⟨d, by omega⟩ - 1, ?_⟩
          simp [F, f, fs, triangularFieldModelEquations, MvPolynomial.rename_rename,
            Function.comp_def]
        | succ b =>
          have hbr : b < r := by omega
          let g : Fin (d + 1 + b) → Fin (d + 1 + i) :=
            fun a ↦ ⟨a.val, by omega⟩
          refine ⟨Polynomial.eval₂ (MvPolynomial.rename g).toRingHom
            (MvPolynomial.X ⟨d + 1 + b, by omega⟩) (p ⟨b, hbr⟩), ?_⟩
          rw [Polynomial.hom_eval₂]
          have hcomp : F.comp (MvPolynomial.rename g).toRingHom =
              (MvPolynomial.rename (fun a : Fin (d + 1 + b) ↦
                (⟨a.val, by omega⟩ : Fin (d + 1 + r)))).toRingHom := by
            ext a <;> simp [F, f, g, MvPolynomial.rename_rename, Function.comp_def]
          rw [hcomp]
          simp [F, f, fs, triangularFieldModelEquations, List.getElem_ofFn]
      obtain ⟨a', ha'⟩ := hpre
      rw [← hab, ← ha']
      apply Ideal.mem_map_of_mem
      change F a' ∈ I
      rw [ha']
      apply Ideal.subset_span
      change fs[b] ∈ fs.take (i + 1)
      rw [List.mem_take_iff_getElem]
      exact ⟨_, hb, rfl⟩
    have ht : ∀ a, f a ≠ t := by
      intro a he
      have hv := congrArg Fin.val he
      dsimp [f, t] at hv
      omega
    have heq : fs[i + 1] =
        Polynomial.eval₂ F (MvPolynomial.X t) (p ⟨i, hir⟩) := by
      simp [fs, triangularFieldModelEquations, F, f, t, List.getElem_ofFn]
    change fs[i + 1] * q ∈ I at hq
    change q ∈ I
    rw [heq, ← hI] at hq
    rw [← hI]
    exact fresh_monic_mul_mem_extended_ideal f t ht (I.comap F)
      (p ⟨i, hir⟩) (hp ⟨i, hir⟩) q hq

end FieldTheory

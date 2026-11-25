/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.RingTheory.AdicCompletion.Algebra
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import all WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage

/-! # Affine coordinates for a coherent completion system

Source: Stacks Project, Tags 087W, 01I7 and 01IB.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Canonical affine completion projections, including their inverse-limit property.

Source: Stacks Project, Tag 087W, first paragraph; Tags 01I7 and 01IB,
affine module/sections comparison.
(blueprint: lem-weil-pbc-completion-affine-sections-coordinates).

Proof:
1. Coherence on the Noetherian scheme implies quasi-coherence and finite type. On U,
   the ideal-product comparison and exactness of affine sections identify the cokernel
   at level n with P(U)/(I(U)^(n+1) P(U)). The identification is the unique linear
   equivalence carrying the sheaf quotient projection to the module quotient projection.
2. The quotient identifications commute with all transitions: precompose each claimed
   equality with the surjective ordinary section quotient and use the defining equations
   of the cokernel transitions. Compose their inverses with AdicCompletion.eval to define p.
3. The evaluation maps are surjective. Their joint injectivity at positive levels follows
   from AdicCompletion.ext; the omitted zeroth quotient is zero. The formula on of follows
   from eval_of. Completed scalar multiplication acts at level n through eval of the ring;
   replacing that scalar by any ordinary representative gives the scalar formula.
4. Given compatible sections, apply the quotient identifications at every positive level
   and use zero at level zero. Transition compatibility makes an element of AdicCompletion.
   Its projections are exactly the given sections. This proves the inverse-limit property.
No choice of generators or of arbitrary module data is required. -/
theorem completion_affine_sections_coordinates {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (P : CoherentModules X) (U : X.affineOpens) :
    let A := Γ(X, U.val)
    let J := I.ideal U
    let C := AdicCompletion J Γ(P.obj, U.val)
    ∃ p : ∀ n : ℕᵒᵖ,
      C →ₗ[A] Γ(formalModuleQuotient I (n.unop + 1) P.obj, U.val),
      (∀ n, Function.Surjective (p n)) ∧
      (∀ x y : C, (∀ n, p n x = p n y) → x = y) ∧
      (∀ (a b : ℕᵒᵖ) (f : a ⟶ b) (x : C),
        ((formalCompletionSystem I P.obj).map f).val.app (op U.val) (p a x) = p b x) ∧
      (∀ n x, p n (AdicCompletion.of J _ x) =
        (formalModuleQuotientπ I (n.unop + 1) P.obj).val.app (op U.val) x) ∧
      (∀ n (r : AdicCompletion J A) (a : A) (x : C),
        AdicCompletion.evalₐ J (n.unop + 1) r = Ideal.Quotient.mk _ a →
          p n (r • x) = a • p n x) ∧
      (∀ s : ∀ n : ℕᵒᵖ, Γ(formalModuleQuotient I (n.unop + 1) P.obj, U.val),
        (∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
          ((formalCompletionSystem I P.obj).map f).val.app (op U.val) (s a) = s b) →
        ∃ x : C, ∀ n, p n x = s n) := by
  classical
  let A := Γ(X, U.val)
  let J := I.ideal U
  let M := Γ(P.obj, U.val)
  have hP := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X P.obj).mp P.property
  have : P.obj.IsQuasicoherent := hP.1
  let i (n : ℕ) := (Scheme.idealSheafPower I.toModulesι (n + 1)).2
  have hp := Scheme.Modules.ideal_times_quasiCoherent_affine_sections I P.obj
  have hr (n : ℕ) : LinearMap.range
      ((Scheme.idealModuleProductι (i n) P.obj).val.app (op U.val)).hom =
      J ^ (n + 1) • (⊤ : Submodule A M) := by
    have := hp.2.2.1 (n + 1) (by omega)
    have hI : (LinearMap.range ((i n).val.app (op U.val)).hom : Ideal A) =
        J ^ (n + 1) := by
      exact SetLike.coe_injective ((hp.2.2.2.1 U).2.2.2 (n + 1) (by omega))
    apply SetLike.coe_injective
    exact hI ▸ Scheme.Modules.multiplication_range (i n) P.obj U
  have hq (n : ℕ) : ∃ q : (M ⧸ (J ^ (n + 1) • ⊤ : Submodule A M)) ≃ₗ[A]
      Γ(formalModuleQuotient I (n + 1) P.obj, U.val),
      ∀ x : M, q (Submodule.Quotient.mk x) =
        (formalModuleQuotientπ I (n + 1) P.obj).val.app (op U.val) x := by
    have := hp.2.2.1 (n + 1) (by omega)
    have := Scheme.Modules.product_qc (i n) P.obj
    obtain ⟨q, hq⟩ := (Scheme.Modules.quasiCoherent_cokernel_image
      (Scheme.idealModuleProductι (i n) P.obj)).2.2.2.2.2.2.2.2 U |>.2.2.2
    refine ⟨(Submodule.quotEquivOfEq _ _ (hr n).symm).trans q, ?_⟩
    intro x
    exact hq x
  choose q hq using hq
  have htrans (a b : ℕ) (h : b ≤ a)
      (x : M ⧸ (J ^ (a + 1) • ⊤ : Submodule A M)) :
      ((formalCompletionSystem I P.obj).map (homOfLE h).op).val.app (op U.val) (q a x) =
        q b (AdicCompletion.transitionMap J M (Nat.succ_le_succ h) x) := by
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      rw [hq]
      change ((formalModuleQuotientπ I (a + 1) P.obj ≫
        formalModuleQuotientMap I (𝟙 P.obj) (Nat.succ_le_succ h)).val.app (op U.val)) x = _
      have hc : formalModuleQuotientπ I (a + 1) P.obj ≫
          formalModuleQuotientMap I (𝟙 P.obj) (Nat.succ_le_succ h) =
          formalModuleQuotientπ I (b + 1) P.obj := by
        simp [formalModuleQuotientπ, formalModuleQuotientMap]
      rw [hc]
      exact (hq b x).symm
  let p (n : ℕᵒᵖ) := (q n.unop).toLinearMap.comp (AdicCompletion.eval J M (n.unop + 1))
  refine ⟨p, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (q n.unop).surjective.comp (AdicCompletion.eval_surjective J M _)
  · intro x y h
    apply AdicCompletion.ext
    intro n
    cases n with
    | zero =>
      have : Subsingleton (M ⧸ (J ^ 0 • ⊤ : Submodule A M)) := by
        simpa only [pow_zero, Ideal.one_eq_top, Submodule.top_smul] using
          (inferInstance : Subsingleton (M ⧸ (⊤ : Submodule A M)))
      exact Subsingleton.elim _ _
    | succ n => exact (q n).injective (h (op n))
  · intro a b f x
    have ht := htrans a.unop b.unop (leOfHom f.unop) (x.val (a.unop + 1))
    change ((formalCompletionSystem I P.obj).map f).val.app (op U.val)
      (q a.unop (x.val (a.unop + 1))) = q b.unop (x.val (b.unop + 1))
    have hf : (homOfLE (leOfHom f.unop)).op = f := Subsingleton.elim _ _
    simpa only [op_unop, hf, AdicCompletion.transitionMap_comp_eval_apply] using ht
  · intro n x
    change q n.unop (AdicCompletion.eval J M (n.unop + 1) (AdicCompletion.of J M x)) = _
    rw [AdicCompletion.eval_of]
    exact hq n.unop x
  · intro n r a x ha
    change q n.unop ((r • x).val (n.unop + 1)) = a • q n.unop (x.val (n.unop + 1))
    rw [AdicCompletion.smul_eval, AdicCompletion.val_smul_eq_evalₐ_smul, ha]
    change q n.unop (a • x.val (n.unop + 1)) = _
    exact (q n.unop).map_smul a _
  · intro s hs
    let z : ∀ n : ℕ, M ⧸ (J ^ n • ⊤ : Submodule A M)
      | 0 => 0
      | n + 1 => (q n).symm (s (op n))
    have hz {m n : ℕ} (h : m ≤ n) :
        AdicCompletion.transitionMap J M h (z n) = z m := by
      cases m with
      | zero =>
        have : Subsingleton (M ⧸ (J ^ 0 • ⊤ : Submodule A M)) := by
          simpa only [pow_zero, Ideal.one_eq_top, Submodule.top_smul] using
            (inferInstance : Subsingleton (M ⧸ (⊤ : Submodule A M)))
        exact Subsingleton.elim _ _
      | succ m =>
        cases n with
        | zero => omega
        | succ n =>
          apply (q m).injective
          change q m (AdicCompletion.transitionMap J M h ((q n).symm (s (op n)))) =
            q m ((q m).symm (s (op m)))
          rw [← htrans n m (Nat.le_of_succ_le_succ h), LinearEquiv.apply_symm_apply,
            LinearEquiv.apply_symm_apply]
          exact hs (op n) (op m) (homOfLE (Nat.le_of_succ_le_succ h)).op
    refine ⟨⟨z, hz⟩, ?_⟩
    intro n
    change q n.unop ((q n.unop).symm (s (op n.unop))) = s n
    simpa only [op_unop] using (q n.unop).apply_symm_apply (s n)

end AlgebraicGeometry

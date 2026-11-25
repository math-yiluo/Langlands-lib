/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Completion and inverse systems with stable ranges

Source: Stacks Project, Theorem 02OC, the inverse-limit argument in its proof.
(blueprint: lem-weil-pbc-adic-completion-stable-ranges).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

/-- An inverse system whose stable images come from H and whose reduction kernels
are cofinal with the I-adic filtration has the same limit as the completion of H.
Source: Stacks Project, Theorem 02OC, proof after applying Lemma 02OB.
(blueprint: lem-weil-pbc-adic-completion-stable-ranges).

Proof: Write K_n = ker rho_n and N_n = range rho_n. Compatibility makes N an
inverse subsystem of M. A compatible family x in M has x_n in N_n because
x_n is the transition of x_(n+c), and the range of that transition is N_n.
Thus inclusion induces an isomorphism lim N -> lim M. The first isomorphism
theorem identifies N_n with H/K_n compatibly with all transitions. Factoring
rho_n through theta_n gives I^(n+1) H <= K_n. The kernel hypothesis gives
K_(n+c) <= I^(n+1) H. The quotient maps H/I^(n+1) H -> H/K_n and
H/K_(n+c) -> H/I^(n+1) H therefore induce inverse maps on limits: both
composites evaluate to the transition by c levels, hence to the original
compatible family. Level zero of the adic completion is a zero module, so
omitting it changes nothing. Compose these isomorphisms to obtain the asserted
isomorphism; its projections are theta_n followed by evaluation by construction.
This argument also covers c=0 and the zero and unit ideals, without finiteness
or surjectivity of rho_n. -/
theorem adicCompletion_iso_of_stable_ranges {A : Type u} [CommRing A]
    (I : Ideal A) (H : ModuleCat.{u} A) (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (ρ : ∀ n : ℕ, H →ₗ[A] M.obj (op n))
    (θ : ∀ n : ℕ, (H ⧸ (I ^ (n + 1) • ⊤ : Submodule A H)) →ₗ[A]
      M.obj (op n))
    (hθ : ∀ n, (θ n).comp (Submodule.mkQ (I ^ (n + 1) • ⊤)) = ρ n)
    (htrans : ∀ (n m : ℕ) (h : n ≤ m),
      (M.map (homOfLE h).op).hom.comp (θ m) =
        (θ n).comp (AdicCompletion.transitionMap I H (Nat.succ_le_succ h)))
    (c : ℕ)
    (hker : ∀ n : ℕ, LinearMap.ker (ρ (n + c)) ≤
      I ^ (n + 1) • (⊤ : Submodule A H))
    (hrange : ∀ n : ℕ, Set.range (M.map (homOfLE (Nat.le_add_right n c)).op).hom =
      Set.range (ρ n)) :
    ∃ e : ModuleCat.of A (AdicCompletion I H) ≅ limit M,
      ∀ n : ℕ, e.hom ≫ limit.π M (op n) =
        ModuleCat.ofHom ((θ n).comp (AdicCompletion.eval I H (n + 1)))  := by
  classical
  have hρ (n m : ℕ) (h : n ≤ m) :
      (M.map (homOfLE h).op).hom.comp (ρ m) = ρ n := by
    rw [← hθ m, ← LinearMap.comp_assoc, htrans, LinearMap.comp_assoc]
    have hq : (AdicCompletion.transitionMap I H (Nat.succ_le_succ h)).comp
        (Submodule.mkQ (I ^ (m + 1) • ⊤)) =
        Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A H)) := by
      ext x
      rfl
    rw [hq, hθ]
  let cone : Cone M :=
    { pt := ModuleCat.of A (AdicCompletion I H)
      π :=
        { app j := ModuleCat.ofHom ((θ j.unop).comp
            (AdicCompletion.eval I H (j.unop + 1)))
          naturality := by
            intro i j f
            have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
            simp only [Functor.const_obj_map]
            symm
            apply ModuleCat.hom_ext
            change (M.map f).hom.comp ((θ i.unop).comp
              (AdicCompletion.eval I H (i.unop + 1))) = _
            have ht := htrans j.unop i.unop (leOfHom f.unop)
            rw [← hf] at ht
            rw [← LinearMap.comp_assoc, ht, LinearMap.comp_assoc,
              AdicCompletion.transitionMap_comp_eval]
            rfl } }
  let φ := limit.lift M cone
  have hφ (n : ℕ) : φ ≫ limit.π M (op n) =
      ModuleCat.ofHom ((θ n).comp (AdicCompletion.eval I H (n + 1))) :=
    limit.lift_π cone (op n)
  have hφval (n : ℕ) (x : AdicCompletion I H) :
      (limit.π M (op n)) (φ x) = θ n (x.val (n + 1)) :=
    ConcreteCategory.congr_hom (hφ n) x
  have hinj : Function.Injective φ := by
    apply (φ.hom).ker_eq_bot.1
    apply le_antisymm _ bot_le
    intro x hx
    change φ x = 0 at hx
    change x = 0
    apply Subtype.ext
    funext n
    have hzero (k : ℕ) : θ k (x.val (k + 1)) = 0 := by
      rw [← hφval, hx]
      exact map_zero _
    obtain ⟨y, hy⟩ :=
      (I ^ (n + c + 1) • (⊤ : Submodule A H)).mkQ_surjective (x.val (n + c + 1))
    have hky : y ∈ (ρ (n + c)).ker := by
      rw [LinearMap.mem_ker, ← hθ (n + c)]
      change θ (n + c) ((I ^ (n + c + 1) • (⊤ : Submodule A H)).mkQ y) = 0
      rw [hy, hzero]
    have hmem : y ∈ (I ^ n • (⊤ : Submodule A H)) :=
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n))) (hker n hky)
    have heval := x.property (show n ≤ n + c + 1 by omega)
    rw [← hy] at heval
    change (I ^ n • (⊤ : Submodule A H)).mkQ y = x.val n at heval
    rw [← heval]
    exact (Submodule.Quotient.mk_eq_zero _).2 hmem
  have hsurj : Function.Surjective φ := by
    intro z
    have hπ (n m : ℕ) (h : n ≤ m) :
        (M.map (homOfLE h).op) ((limit.π M (op m)) z) = (limit.π M (op n)) z :=
      ConcreteCategory.congr_hom (limit.w M (homOfLE h).op) z
    have hex (n : ℕ) : ∃ y : H, ρ (n + c) y = (limit.π M (op (n + c))) z := by
      apply (hrange (n + c)).le
      exact ⟨(limit.π M (op (n + c + c))) z, hπ _ _ (Nat.le_add_right _ c)⟩
    choose y hy using hex
    have hrep (n m : ℕ) (h : n ≤ m) :
        ρ (n + c) (y m) = (limit.π M (op (n + c))) z := by
      rw [← LinearMap.congr_fun (hρ (n + c) (m + c) (Nat.add_le_add_right h c))]
      simp only [LinearMap.comp_apply, hy, hπ]
    let x : AdicCompletion I H :=
      ⟨fun n ↦ (I ^ n • (⊤ : Submodule A H)).mkQ (y n), by
        intro m n h
        change (I ^ m • (⊤ : Submodule A H)).mkQ (y n) =
          (I ^ m • (⊤ : Submodule A H)).mkQ (y m)
        apply (Submodule.Quotient.eq _).2
        apply Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ m))
        apply hker m
        rw [LinearMap.mem_ker, map_sub, hrep m n h, hy, sub_self]⟩
    refine ⟨x, ?_⟩
    apply Concrete.limit_ext M
    intro j
    let n := j.unop
    change (limit.π M (op n)) (φ x) = (limit.π M (op n)) z
    rw [hφval]
    change θ n ((I ^ (n + 1) • (⊤ : Submodule A H)).mkQ (y (n + 1))) = _
    rw [← LinearMap.comp_apply, hθ]
    rw [← LinearMap.congr_fun (hρ n (n + 1 + c) (by omega)) (y (n + 1))]
    simpa only [LinearMap.comp_apply, hy] using hπ n (n + 1 + c) (by omega)
  exact ⟨(LinearEquiv.ofBijective φ.hom ⟨hinj, hsurj⟩).toModuleIso, hφ⟩

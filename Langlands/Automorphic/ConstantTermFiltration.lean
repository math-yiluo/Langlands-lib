import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Cyclic quotients and a finite filtration by kernels

The module-theoretic part of Langlands (1979), pp. 204–205, selecting a
constant term that keeps a given simple quotient and kills the later terms.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Automorphic

universe uR uV uY uW

variable {R : Type uR} [Ring R] {V : Type uV} [AddCommGroup V] [Module R V]
variable {k : ℕ} {Y : Fin k → Type uY} [∀ i, AddCommGroup (Y i)] [∀ i, Module R (Y i)]

/-- The common kernel of the maps at or after the cutoff `n`. -/
def laterTermKernel (c : ∀ i, V →ₗ[R] Y i) (n : ℕ) : Submodule R V :=
  ⨅ (i : Fin k) (_ : n ≤ i.val), LinearMap.ker (c i)

theorem mem_laterTermKernel (c : ∀ i, V →ₗ[R] Y i) (n : ℕ) (x : V) :
    x ∈ laterTermKernel c n ↔ ∀ i : Fin k, n ≤ i.val → c i x = 0 := by
  simp only [laterTermKernel, Submodule.mem_iInf, LinearMap.mem_ker]

/-- A finite ordered family that separates vectors has a term whose cyclic
image still surjects onto the given simple quotient. All later terms vanish
on the source cyclic module. -/
theorem exists_cyclic_term_quotient (c : ∀ i, V →ₗ[R] Y i)
    (hsep : ∀ x : V, (∀ i, c i x = 0) → x = 0)
    {W : Type uW} [AddCommGroup W] [Module R W] [IsSimpleModule R W]
    (q : V →ₗ[R] W) (hq : Function.Surjective q) :
    ∃ (i : Fin k) (x : V) (p : (R ∙ c i x) →ₗ[R] W),
      (∀ j : Fin k, i < j → (R ∙ x) ≤ LinearMap.ker (c j)) ∧
      Function.Surjective p ∧
      p ⟨c i x, Submodule.mem_span_singleton_self _⟩ = q x ∧ q x ≠ 0 := by
  classical
  have := IsSimpleModule.nontrivial R W
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hq w
  let good (n : ℕ) : Prop := ∃ x : V, q x ≠ 0 ∧ x ∈ laterTermKernel c n
  have hgk : good k :=
    ⟨v, hw, (mem_laterTermKernel c k v).mpr fun i hi => (i.isLt.not_ge hi).elim⟩
  have hg : ∃ n, good n := ⟨k, hgk⟩
  have hg0 : ¬ good 0 := by
    rintro ⟨x, hn, hx⟩
    have hz := hsep x fun i => (mem_laterTermKernel c 0 x).mp hx i (Nat.zero_le _)
    exact hn (hz ▸ q.map_zero)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (fun h => hg0 (h ▸ Nat.find_spec hg))
  have hnk := Nat.find_min' hg hgk
  let i : Fin k := ⟨n, by omega⟩
  obtain ⟨x, hqx, hx⟩ : good (n + 1) := by
    simpa only [hn] using Nat.find_spec hg
  have hspan : (R ∙ x) ≤ laterTermKernel c (n + 1) :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hx
  let qₓ := q.domRestrict (R ∙ x)
  let f := (c i).domRestrict (R ∙ x)
  have hker : LinearMap.ker f ≤ LinearMap.ker qₓ := by
    intro y hy
    change q y.val = 0
    by_contra hyq
    apply Nat.find_min hg (show n < Nat.find hg by omega)
    refine ⟨y.val, hyq, (mem_laterTermKernel c n y.val).mpr fun j hj => ?_⟩
    by_cases he : j.val = n
    · have hji : j = i := Fin.ext he
      subst j
      exact hy
    · exact (mem_laterTermKernel c (n + 1) y.val).mp (hspan y.property) j (by omega)
  have hrange : LinearMap.range f = R ∙ c i x := by
    dsimp [f]
    rw [LinearMap.range_domRestrict, Submodule.map_span, Set.image_singleton]
  let p : (R ∙ c i x) →ₗ[R] W := (LinearMap.ker f).liftQ qₓ hker ∘ₗ
    f.quotKerEquivRange.symm.toLinearMap ∘ₗ (LinearEquiv.ofEq _ _ hrange.symm).toLinearMap
  have hp : p ⟨c i x, Submodule.mem_span_singleton_self _⟩ = q x := by
    have he : (LinearEquiv.ofEq _ _ hrange.symm)
        ⟨c i x, Submodule.mem_span_singleton_self _⟩ =
        ⟨f ⟨x, Submodule.mem_span_singleton_self _⟩, LinearMap.mem_range_self _ _⟩ :=
      Subtype.ext rfl
    unfold p
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  refine ⟨i, x, p, ?_, p.surjective_or_eq_zero.resolve_right ?_, hp, hqx⟩
  · intro j hj y hy
    exact (mem_laterTermKernel c (n + 1) y).mp (hspan hy) j (Nat.succ_le_of_lt hj)
  · intro h
    exact hqx (by simpa [h] using hp.symm)

end Langlands.Automorphic

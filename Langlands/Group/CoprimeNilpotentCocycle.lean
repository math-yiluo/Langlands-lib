import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.GCD

/-! # Coprime one-cocycles with values in nilpotent groups are coboundaries -/

namespace Langlands.Group.CoprimeNilpotentCocycle

open Subgroup

/-- In a group of exponent dividing `n`, raising to a power prime to `n` is undone by the
Bézout coefficient. -/
theorem zpow_gcdA_pow {A : Type*} [Group A] {m n : ℕ} (hn : ∀ x : A, x ^ n = 1)
    (hcop : Nat.Coprime m n) (x : A) : (x ^ m) ^ (Nat.gcdA m n) = x := by
  have hgcd : ((Nat.gcd m n : ℕ) : ℤ) = m * Nat.gcdA m n + n * Nat.gcdB m n :=
    Nat.gcd_eq_gcd_ab m n
  rw [hcop.gcd_eq_one, Nat.cast_one] at hgcd
  calc (x ^ m) ^ (Nat.gcdA m n)
      = x ^ ((m : ℤ) * Nat.gcdA m n) := by rw [zpow_mul, zpow_natCast]
    _ = x ^ ((m : ℤ) * Nat.gcdA m n + n * Nat.gcdB m n) := by
        rw [zpow_add, zpow_mul x (n : ℤ), zpow_natCast x n, hn, one_zpow, mul_one]
    _ = x := by rw [← hgcd, zpow_one]

/-- The abelian case: a finite group whose order is prime to the exponent of a
commutative group. The maps `φ f` need only be group endomorphisms. -/
theorem abelian {F A : Type*} [Group F] [Finite F] [CommGroup A] (φ : F → A →* A)
    {n : ℕ} (hn : ∀ x : A, x ^ n = 1) (hcop : Nat.Coprime (Nat.card F) n)
    (c : F → A) (hc : ∀ f g, c (f * g) = c f * φ f (c g)) :
    ∃ a : A, ∀ f, c f = a * (φ f a)⁻¹ := by
  classical
  have := Fintype.ofFinite F
  let P : A := ∏ g, c g
  have key : ∀ f, P * (φ f P)⁻¹ = c f ^ Nat.card F := by
    intro f
    have h1 : ∀ g, φ f (c g) = (c f)⁻¹ * c (f * g) := by
      intro g
      rw [hc, inv_mul_cancel_left]
    have h2 : (∏ g, c (f * g)) = P :=
      Fintype.prod_equiv (Equiv.mulLeft f) _ _ (fun _ => rfl)
    have h3 : φ f P = ((c f)⁻¹) ^ Nat.card F * P := by
      change φ f (∏ g, c g) = _
      rw [map_prod]
      simp_rw [h1]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Nat.card_eq_fintype_card, h2]
    rw [h3, inv_pow, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  refine ⟨P ^ (Nat.gcdA (Nat.card F) n), fun f => ?_⟩
  rw [map_zpow, ← inv_zpow, ← mul_zpow, key, zpow_gcdA_pow hn hcop]

universe u v

/-- Coprime one-cocycles with values in a nilpotent group of finite exponent are
coboundaries. Here `F` is finite, acts on `G` through `φ`, and `Nat.card F` is prime to an
exponent `n` of `G`. -/
def VanishingStatement : Prop :=
  ∀ {F : Type u} [Group F] [Finite F] (G : Type v) [Group G]
    [Group.IsNilpotent G] (φ : F →* MulAut G) {n : ℕ},
    (∀ x : G, x ^ n = 1) → Nat.Coprime (Nat.card F) n →
    ∀ (c : F → G), (∀ f g, c (f * g) = c f * φ f (c g)) →
      ∃ a : G, ∀ f, c f = a * (φ f a)⁻¹

/-- Proof of coprime one-cocycle vanishing, by induction through the center quotient. -/
theorem exists_coboundary : VanishingStatement.{u, v} := by
  intro F _ _ G _ _ φ n hn hcop c hc
  revert φ c
  refine Group.nilpotent_center_quotient_ind
    (P := fun G _ _ => (∀ x : G, x ^ n = 1) → ∀ (φ : F →* MulAut G) (c : F → G),
      (∀ f g, c (f * g) = c f * φ f (c g)) → ∃ a : G, ∀ f, c f = a * (φ f a)⁻¹)
    G ?_ ?_ hn
  · intro G _ _ _ φ c _
    exact ⟨1, fun f => Subsingleton.elim _ _⟩
  · intro G _ _ ih hn φ c hc
    -- the action on the quotient by the center
    let ψ : MulAut G →* MulAut (G ⧸ center G) :=
      { toFun := fun e => QuotientGroup.congr (center G) (center G) e (map_center_eq e)
        map_one' := by
          ext x
          induction x using QuotientGroup.induction_on
          rfl
        map_mul' := by
          intro e e'
          ext x
          induction x using QuotientGroup.induction_on
          rfl }
    have hnq : ∀ x : G ⧸ center G, x ^ n = 1 := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H x => rw [← QuotientGroup.mk_pow, hn, QuotientGroup.mk_one]
    obtain ⟨b, hb⟩ := ih hnq (ψ.comp φ) (fun f => (c f : G ⧸ center G)) (by
      intro f g
      rw [hc, QuotientGroup.mk_mul]
      rfl)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective b
    -- the twisted cocycle lands in the center
    have hmem : ∀ f, a⁻¹ * c f * φ f a ∈ center G := by
      intro f
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul, hb f]
      change ((a⁻¹ : G) : G ⧸ center G) * ((a : G ⧸ center G) * ((φ f a : G) : G ⧸ center G)⁻¹) *
        ((φ f a : G) : G ⧸ center G) = 1
      rw [QuotientGroup.mk_inv]
      group
    let _ : CommGroup (center G) :=
      { (center G).toGroup with mul_comm := fun x y => Subtype.ext (x.2.comm y) }
    have hcen : ∀ (f : F) (x : G), x ∈ center G → φ f x ∈ center G := fun f x hx => by
      rw [← SetLike.mem_coe, coe_center] at hx ⊢
      exact MulEquivClass.apply_mem_center (φ f) hx
    let φZ : F → center G →* center G := fun f =>
      { toFun := fun z => ⟨φ f (z : G), hcen f z z.2⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun x y => Subtype.ext (map_mul (φ f) (x : G) (y : G)) }
    let cZ : F → center G := fun f => ⟨a⁻¹ * c f * φ f a, hmem f⟩
    obtain ⟨z, hz⟩ := abelian φZ (n := n) (fun x => Subtype.ext (by
        rw [SubgroupClass.coe_pow, hn]; rfl)) hcop cZ (by
      intro f g
      apply Subtype.ext
      change a⁻¹ * c (f * g) * φ (f * g) a =
        a⁻¹ * c f * φ f a * φ f (a⁻¹ * c g * φ g a)
      rw [hc, map_mul, MulAut.mul_apply, map_mul, map_mul, map_inv]
      group)
    refine ⟨a * z, fun f => ?_⟩
    have h := congrArg Subtype.val (hz f)
    change a⁻¹ * c f * φ f a = (z : G) * (φ f (z : G))⁻¹ at h
    rw [map_mul, mul_inv_rev, ← mul_assoc, mul_assoc a, ← h]
    group

end Langlands.Group.CoprimeNilpotentCocycle

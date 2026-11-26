import Langlands.Correspondence.Laumon.Completion

/-!
# The tame quotient of inertia

Laumon (1987), (2.1.1), p. 151: the action of inertia on the roots of order prime to `p` of a
uniformizer factors through a canonical quotient `I → Ẑ'(1)(k̄) = lim μ_N(k̄)`, `p ∤ N`, whose
kernel is the wild inertia `P`. This module constructs the topological group `lim μ_N(F)` and
states, for `LaurentSeries k` with `k` finite, that the Library's inertia modulo wild inertia,
on the Galois and on the Weil side, is isomorphic to it as a topological group by the action on
the roots of the uniformizer of the end trait, compatibly with the Galois action on the roots
of unity.
-/

noncomputable section

universe u v

open CategoryTheory

namespace Langlands.Henniart.Laumon

attribute [local instance] Langlands.LocalField.Laurent.valuativeRel

section TameRoots

/-- The integers `n ≥ 1` with `p ∤ n` (for a prime `p`: the integers prime to `p`). -/
def TameIndex (p : ℕ) : Type := {n : ℕ // 0 < n ∧ ¬ p ∣ n}

variable (F : Type v) [Field F] (p : ℕ)

/-- The compatible families `(ζ_n)` of `n`-th roots of unity, `p ∤ n`, with
`ζ_m ^ (m / n) = ζ_n` for `n ∣ m`: the inverse limit of the `μ_n(F)` as a subgroup of the
product. -/
def tameRootsSubgroup : Subgroup (TameIndex p → Fˣ) where
  carrier := {ζ | (∀ n : TameIndex p, ζ n ^ n.1 = 1) ∧
    ∀ n m : TameIndex p, n.1 ∣ m.1 → ζ m ^ (m.1 / n.1) = ζ n}
  one_mem' := ⟨fun _ => one_pow _, fun _ _ _ => one_pow _⟩
  mul_mem' {a b} ha hb := ⟨fun n => by simp [Pi.mul_apply, mul_pow, ha.1 n, hb.1 n],
    fun n m h => by simp [Pi.mul_apply, mul_pow, ha.2 n m h, hb.2 n m h]⟩
  inv_mem' {a} ha := ⟨fun n => by simp [inv_pow, ha.1 n],
    fun n m h => by simp [inv_pow, ha.2 n m h]⟩

/-- The inverse limit `lim μ_n(F)` over the `n ≥ 1` with `p ∤ n`. -/
def TameRoots : Type v := tameRootsSubgroup F p

/-- The group structure of the inverse limit. -/
instance : CommGroup (TameRoots F p) := inferInstanceAs (CommGroup (tameRootsSubgroup F p))

/-- The inverse limit topology: the subspace topology of the product of the discrete groups
`Fˣ`. -/
instance : TopologicalSpace (TameRoots F p) :=
  TopologicalSpace.induced (fun ζ : tameRootsSubgroup F p => (ζ : TameIndex p → Fˣ))
    (@Pi.topologicalSpace (TameIndex p) (fun _ => Fˣ) (fun _ => ⊥))

/-- The `n`-th component `ζ_n ∈ F` of a compatible family. -/
def TameRoots.component {F : Type v} [Field F] {p : ℕ} (ζ : TameRoots F p) (n : TameIndex p) : F :=
  (Subtype.val (p := fun x => x ∈ tameRootsSubgroup F p) ζ n : Fˣ)

end TameRoots

open Langlands.LocalGalois.SepClosed Langlands.Weil.Local.SepClosed
  Langlands.Ramification.Local in
/-- **Tame inertia.** For a finite field `k`, the Library's inertia of `LaurentSeries k` modulo
wild inertia is isomorphic as a topological group to `lim μ_n(k̄)`, `n` prime to `p`, with `k̄`
the constants `endConstants k` of the strict end trait, by the isomorphism under which a class
of `σ` acts on every `n`-th root `ϖ` of the uniformizer `t` by multiplication by its `n`-th
component; the isomorphism carries conjugation by `g` to the action of `g` on the roots of
unity. The same holds for the inertia subgroup of the local Weil group modulo the preimage of
wild inertia. -/
def LocalTameInertiaQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k],
    (∃ θ : (absoluteInertia (LaurentSeries k) (SeparableClosure (LaurentSeries k)) ⧸
        (localWildInertia (LaurentSeries k) (SeparableClosure (LaurentSeries k))).subgroupOf
          (absoluteInertia (LaurentSeries k) (SeparableClosure (LaurentSeries k)))) ≃ₜ*
        TameRoots (endConstants k) (ringChar k),
      (∀ (σ : absoluteInertia (LaurentSeries k) (SeparableClosure (LaurentSeries k)))
          (n : TameIndex (ringChar k)) (ϖ : endGenericClosure k),
        ϖ ^ n.1 = algebraMap (endField k) (endGenericClosure k)
            ((endUniformizer k .zero : endRing k) : endField k) →
          completionRestriction k σ ϖ =
            ((θ (QuotientGroup.mk σ)).component n : endGenericClosure k) * ϖ) ∧
      ∀ (g : Gal(SeparableClosure (LaurentSeries k)/LaurentSeries k))
          (σ τ : absoluteInertia (LaurentSeries k) (SeparableClosure (LaurentSeries k))),
        (τ : Gal(SeparableClosure (LaurentSeries k)/LaurentSeries k)) = g * σ * g⁻¹ →
          ∀ n : TameIndex (ringChar k),
            ((θ (QuotientGroup.mk τ)).component n : endGenericClosure k) =
              completionRestriction k g ((θ (QuotientGroup.mk σ)).component n)) ∧
    ∃ θ : (localInertia (LaurentSeries k) (SeparableClosure (LaurentSeries k)) ⧸
        ((localWildInertia (LaurentSeries k) (SeparableClosure (LaurentSeries k))).comap
          (localProjection (LaurentSeries k) (SeparableClosure (LaurentSeries k))).toMonoidHom).subgroupOf
          (localInertia (LaurentSeries k) (SeparableClosure (LaurentSeries k)))) ≃ₜ*
        TameRoots (endConstants k) (ringChar k),
      (∀ (w : localInertia (LaurentSeries k) (SeparableClosure (LaurentSeries k)))
          (n : TameIndex (ringChar k)) (ϖ : endGenericClosure k),
        ϖ ^ n.1 = algebraMap (endField k) (endGenericClosure k)
            ((endUniformizer k .zero : endRing k) : endField k) →
          completionRestriction k
              (localProjection (LaurentSeries k) (SeparableClosure (LaurentSeries k)) w) ϖ =
            ((θ (QuotientGroup.mk w)).component n : endGenericClosure k) * ϖ) ∧
      ∀ (g : localWeilGroup (LaurentSeries k) (SeparableClosure (LaurentSeries k)))
          (w w' : localInertia (LaurentSeries k) (SeparableClosure (LaurentSeries k))),
        (w' : localWeilGroup (LaurentSeries k) (SeparableClosure (LaurentSeries k))) =
            g * w * g⁻¹ →
          ∀ n : TameIndex (ringChar k),
            ((θ (QuotientGroup.mk w')).component n : endGenericClosure k) =
              completionRestriction k
                (localProjection (LaurentSeries k) (SeparableClosure (LaurentSeries k)) g)
                ((θ (QuotientGroup.mk w)).component n)

end Langlands.Henniart.Laumon

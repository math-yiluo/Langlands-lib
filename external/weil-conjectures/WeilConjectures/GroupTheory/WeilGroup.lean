/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The Weil group of a homomorphism and an element

Let `π : G →* Γ` be a group homomorphism and `Φ : Γ`. The *Weil group* `W(π, Φ)` is the fibre
product `G ×_Γ ℤ` of `π` with `n ↦ Φ ^ n`, realised as the subgroup of `G × ℤ` of pairs `(g, n)`
with `π g = Φ ^ n`, and its *degree map* is the second projection `deg : W(π, Φ) → ℤ`.

In the application `G = π₁(X₀, x̄)` is the arithmetic fundamental group of a geometrically
connected scheme `X₀` over a finite field `k₀`, `Γ = Gal(k / k₀)`, and `Φ` is the geometric
Frobenius; then `W(π, Φ)` is the Weil group `W(X₀, x̄)` of `X₀`, and the kernel `ker π` is the
geometric fundamental group `π₁(X, x̄)`. Since `Φ` has infinite order, `ℤ` is identified with the
cyclic subgroup `⟨Φ⟩` and `W(π, Φ)` with the inverse image of `⟨Φ⟩` in `G`.

## Main declarations

* `MonoidHom.weilGroup`: the Weil group `W(π, Φ)`.
* `MonoidHom.weilGroupDeg`: its degree map.
* `MonoidHom.kerToWeilGroup`: the inclusion `ker π → W(π, Φ)`, `g ↦ (g, 0)`.
* `MonoidHom.exact_weilGroupDeg`: the sequence `1 → ker π → W(π, Φ) → ℤ → 0` is exact, and the
  lifts of `Φ` have degree one.

## Blueprint

`MonoidHom.exact_weilGroupDeg` implements `situation-weil`. The Weil group of a
scheme (`situation-weil`) is `AlgebraicGeometry.Scheme.FiniteEtale.weilGroup`, the Weil group
`W(π, Φ)` of the action of `π₁(X₀, s)` on the geometric fibres of the constant covers and the
geometric Frobenius.
-/

@[expose] public section

namespace MonoidHom

variable {G Γ : Type*} [Group G] [Group Γ] (π : G →* Γ) (Φ : Γ)

/-- The Weil group `W(π, Φ)` of a homomorphism `π : G →* Γ` and an element `Φ : Γ`: the fibre
product of `π` with `zpowersHom Γ Φ : ℤ →* Γ`, as the subgroup of `G × ℤ` of pairs `(g, n)` with
`π g = Φ ^ n`. -/
def weilGroup : Subgroup (G × Multiplicative ℤ) :=
  (π.comp (fst G (Multiplicative ℤ))).eqLocus ((zpowersHom Γ Φ).comp (snd G (Multiplicative ℤ)))

variable {π Φ} in
theorem mem_weilGroup {x : G × Multiplicative ℤ} :
    x ∈ weilGroup π Φ ↔ π x.1 = Φ ^ x.2.toAdd :=
  Iff.rfl

/-- The degree map `deg : W(π, Φ) → ℤ`, which records the exponent of `Φ`. -/
def weilGroupDeg : weilGroup π Φ →* Multiplicative ℤ :=
  (snd G (Multiplicative ℤ)).comp (weilGroup π Φ).subtype

@[simp]
theorem weilGroupDeg_apply (w : weilGroup π Φ) : weilGroupDeg π Φ w = (w : G × _).2 :=
  rfl

/-- The inclusion `ker π → W(π, Φ)`, `g ↦ (g, 0)`, of the geometric part. -/
def kerToWeilGroup : π.ker →* weilGroup π Φ :=
  ((π.ker.subtype).prod 1).codRestrict _ fun g ↦ by
    rw [mem_weilGroup]
    exact (mem_ker.1 g.2).trans (zpow_zero Φ).symm

@[simp]
theorem coe_kerToWeilGroup_apply (g : π.ker) :
    (kerToWeilGroup π Φ g : G × Multiplicative ℤ) = ((g : G), 1) :=
  rfl

/-- **The Weil group sequence is exact.** For an element `Φ` of infinite order lifting to `G`,
the degree map `deg : W(π, Φ) → ℤ` is surjective, the inclusion `ker π → W(π, Φ)` is injective
with image `ker deg`, and every lift of `Φ` to `W(π, Φ)` has degree one; that is,
`1 → ker π → W(π, Φ) → ℤ → 0` is exact.
(blueprint: `situation-weil`) -/
theorem exact_weilGroupDeg (hπ : Φ ∈ π.range) (hΦ : ¬IsOfFinOrder Φ) :
    Function.Surjective (weilGroupDeg π Φ) ∧ Function.Injective (kerToWeilGroup π Φ) ∧
      (kerToWeilGroup π Φ).range = (weilGroupDeg π Φ).ker ∧
      ∀ w : weilGroup π Φ, π (w : G × Multiplicative ℤ).1 = Φ →
        weilGroupDeg π Φ w = Multiplicative.ofAdd 1 := by
  obtain ⟨s, hs⟩ := hπ
  refine ⟨fun n ↦ ?_, fun g h hgh ↦ ?_, ?_, fun w hw ↦ ?_⟩
  · refine ⟨⟨(s ^ n.toAdd, n), ?_⟩, rfl⟩
    rw [mem_weilGroup, map_zpow, hs]
  · exact Subtype.ext congr(($hgh : G × Multiplicative ℤ).1)
  · ext w
    constructor
    · rintro ⟨g, rfl⟩
      rfl
    · intro hw
      rw [mem_ker, weilGroupDeg_apply] at hw
      have hg : (w : G × Multiplicative ℤ).1 ∈ π.ker := by
        rw [mem_ker, mem_weilGroup.1 w.2, hw, toAdd_one, zpow_zero]
      exact ⟨⟨_, hg⟩, Subtype.ext (Prod.ext rfl hw.symm)⟩
  · have h := mem_weilGroup.1 w.2
    rw [hw] at h
    apply Multiplicative.toAdd.injective
    have := (injective_zpow_iff_not_isOfFinOrder.2 hΦ) (h.symm.trans (zpow_one Φ).symm)
    simpa using this

end MonoidHom

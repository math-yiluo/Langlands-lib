import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Group

/-! # Finite chamber charts with prescribed diagonal generators -/

noncomputable section

universe uΔ uX uG

namespace Langlands

open scoped BigOperators

variable {Δ : Type uΔ} {X : Type uX} [AddCommGroup X]

/-- Natural Euclidean quotients for a prescribed family of chamber generators. -/
def chamberCoordinates (pair : Δ → X →+ ℤ) (gen : Δ → X) (B : ℤ)
    (x : X) : Δ → ℕ :=
  fun α => ((pair α x + B) / pair α (gen α)).toNat

/-- Subtract the prescribed chamber directions using their Euclidean quotients. -/
def chamberRemainder [Fintype Δ] (pair : Δ → X →+ ℤ) (gen : Δ → X)
    (B : ℤ) (x : X) : X :=
  x - ∑ α, chamberCoordinates pair gen B x α • gen α

variable [Fintype Δ]

theorem pair_chamberRemainder (pair : Δ → X →+ ℤ) (gen : Δ → X)
    (hpos : ∀ α, 0 < pair α (gen α))
    (hzero : ∀ α β, β ≠ α → pair β (gen α) = 0)
    (B : ℤ) (x : X) (hx : ∀ α, -B ≤ pair α x) (α : Δ) :
    pair α (chamberRemainder pair gen B x) =
      (pair α x + B) % pair α (gen α) - B := by
  classical
  have hn : (chamberCoordinates pair gen B x α : ℤ) =
      (pair α x + B) / pair α (gen α) :=
    Int.natCast_toNat_eq_self.mpr
      (Int.ediv_nonneg (by linarith [hx α]) (hpos α).le)
  have hs : pair α (∑ β, chamberCoordinates pair gen B x β • gen β) =
      (chamberCoordinates pair gen B x α : ℤ) * pair α (gen α) := by
    simp only [map_sum, map_nsmul, nsmul_eq_mul]
    apply Finset.sum_eq_single α
    · intro β _ hβα
      rw [hzero β α (Ne.symm hβα), mul_zero]
    · simp
  rw [chamberRemainder, map_sub, hs, hn]
  linarith [Int.emod_add_ediv_mul (pair α x + B) (pair α (gen α))]

/-- A finite set of representatives works for any supplied diagonal-positive
family, without changing that family. -/
theorem exists_finite_prescribed_chamber_representatives
    (pair : Δ → X →+ ℤ) (gen : Δ → X)
    (hpos : ∀ α, 0 < pair α (gen α))
    (hzero : ∀ α β, β ≠ α → pair β (gen α) = 0) (B : ℤ) :
    ∃ R : Set X, R.Finite ∧
      ∀ x : X, (∀ α, -B ≤ pair α x) →
        ∃ r ∈ R, ∃ z : X, (∀ α, pair α z = 0) ∧
          x = r + (∑ α, chamberCoordinates pair gen B x α • gen α) + z := by
  classical
  let φ : X → (Δ → ℤ) := fun x α => pair α x
  let S : Set X :=
    {x | ∀ α, -B ≤ pair α x ∧ pair α x ≤ pair α (gen α) - B}
  have hbox : (φ '' S).Finite := by
    refine (Set.Finite.pi (t := fun α : Δ => Set.Icc (-B) (pair α (gen α) - B))
      fun α => Set.finite_Icc _ _).subset ?_
    rintro _ ⟨x, hx, rfl⟩ α _
    exact hx α
  refine ⟨Function.invFunOn φ S '' (φ '' S), hbox.image _, fun x hx => ?_⟩
  let y : X := chamberRemainder pair gen B x
  have hy : y ∈ S := by
    intro α
    rw [show pair α y = (pair α x + B) % pair α (gen α) - B from
      pair_chamberRemainder pair gen hpos hzero B x hx α]
    constructor
    · linarith [Int.emod_nonneg (pair α x + B) (ne_of_gt (hpos α))]
    · linarith [Int.emod_lt_of_pos (pair α x + B) (hpos α)]
  let r : X := Function.invFunOn φ S (φ y)
  have hr : r ∈ Function.invFunOn φ S '' (φ '' S) :=
    ⟨φ y, ⟨y, hy, rfl⟩, rfl⟩
  have hpair (α : Δ) : pair α r = pair α y :=
    congrFun (Function.invFunOn_eq (f := φ) (s := S) ⟨y, hy, rfl⟩) α
  refine ⟨r, hr, y - r, fun α => ?_, ?_⟩
  · rw [map_sub, hpair, sub_self]
  · dsimp [y, chamberRemainder]
    abel

variable {G : Type uG} [Group G]

/-- A lower-bounded lattice cover yields finite central charts using precisely
the supplied generators. No topology is needed for this conversion. -/
theorem exists_finite_prescribed_chamber_cartan_cover
    (K : Set G) (e : Multiplicative X →* G) (pair : Δ → X →+ ℤ)
    (gen : Δ → X) (hpos : ∀ α, 0 < pair α (gen α))
    (hzero : ∀ α β, β ≠ α → pair β (gen α) = 0)
    (F₀ : Set G) (hF₀ : F₀.Finite)
    (hcentral : ∀ z : X, (∀ α, pair α z = 0) →
      e (.ofAdd z) ∈ Subgroup.center G)
    (B : ℤ)
    (hcover : ∀ g : G, ∃ k₁ ∈ K, ∃ x : X, ∃ f ∈ F₀, ∃ k₂ ∈ K,
      (∀ α, -B ≤ pair α x) ∧ g = k₁ * e (.ofAdd x) * f * k₂) :
    ∃ T : Set G, T.Finite ∧
      ∀ g : G, ∃ n : Δ → ℕ, ∃ k₁ ∈ K, ∃ t ∈ T, ∃ k₂ ∈ K,
        ∃ z ∈ Subgroup.center G,
          g = k₁ * e (.ofAdd (∑ α, n α • gen α)) * t * k₂ * z := by
  classical
  obtain ⟨R, hR, hrep⟩ :=
    exists_finite_prescribed_chamber_representatives pair gen hpos hzero B
  let T : Set G := (fun p : X × G => e (.ofAdd p.1) * p.2) '' (R ×ˢ F₀)
  refine ⟨T, (hR.prod hF₀).image _, fun g => ?_⟩
  obtain ⟨k₁, hk₁, x, f, hf, k₂, hk₂, hx, hg⟩ := hcover g
  obtain ⟨r, hr, z, hz, hxeq⟩ := hrep x hx
  let n := chamberCoordinates pair gen B x
  have hzc := hcentral z hz
  have he : e (.ofAdd x) =
      e (.ofAdd r) * e (.ofAdd (∑ α, n α • gen α)) * e (.ofAdd z) := by
    rw [hxeq, ofAdd_add, ofAdd_add, map_mul, map_mul]
  have hrs : e (.ofAdd r) * e (.ofAdd (∑ α, n α • gen α)) =
      e (.ofAdd (∑ α, n α • gen α)) * e (.ofAdd r) := by
    rw [← e.map_mul, ← e.map_mul, mul_comm]
  refine ⟨n, k₁, hk₁, e (.ofAdd r) * f,
    ⟨(r, f), ⟨hr, hf⟩, rfl⟩, k₂, hk₂, e (.ofAdd z), hzc, ?_⟩
  calc
    g = k₁ * (e (.ofAdd r) * e (.ofAdd (∑ α, n α • gen α)) *
        e (.ofAdd z)) * f * k₂ := by rw [hg, he]
    _ = k₁ * (e (.ofAdd r) * e (.ofAdd (∑ α, n α • gen α))) *
        (e (.ofAdd z) * (f * k₂)) := by group
    _ = k₁ * (e (.ofAdd (∑ α, n α • gen α)) * e (.ofAdd r)) *
        ((f * k₂) * e (.ofAdd z)) := by
      rw [hrs, ← Subgroup.mem_center_iff.mp hzc (f * k₂)]
    _ = _ := by group

end Langlands

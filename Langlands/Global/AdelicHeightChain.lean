import Langlands.Global.AdelicOrbitHeightMinimum
import Langlands.Global.AdelicGroupNormOne

/-! # Simultaneous minima along a rational subgroup chain -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- A rational point acting by a nonzero rational scalar on the fixed vector preserves
its represented adelic height. The product formula is essential here. -/
theorem orbitHeight_mul_rational_eq_of_scalar {n : ℕ}
    (ρ : MatrixRepresentation G (Fin n)) (v : Fin n → F) (hv : v ≠ 0)
    (q : RationalGroupPoints F G) (a : Fˣ)
    (ha : (rationalMatrix F G ρ q).val *ᵥ v = (a : F) • v)
    (g : AdelicGroupPoints F G) :
    orbitHeight F G ρ v (g * rational F G q) = orbitHeight F G ρ v g := by
  rw [orbitHeight_mul_rational, ha]
  exact PrimitiveAdelicHeight.rationalHeight_smul F n (adelicMatrix F G ρ g) a v hv

/-- The finite-chain height-minimal set. Each height may use a different actual
representation and dimension; the rational subgroup in its inequality is specified. -/
def chainHeightMinimalSet (r : ℕ) (d : ℕ → ℕ)
    (ρ : (i : ℕ) → MatrixRepresentation G (Fin (d i)))
    (v : (i : ℕ) → Fin (d i) → F)
    (Q : ℕ → Subgroup (RationalGroupPoints F G)) (c : ℝ) :
    Set (normOneSubgroup F G) :=
  {g | ∀ i, i < r → ∀ q : Q i,
    orbitHeight F G (ρ i) (v i) g ≤
      c * orbitHeight F G (ρ i) (v i) ((g : AdelicGroupPoints F G) * rational F G q)}

/-- Successive minima coexist when the rational subgroups descend and later subgroups
act by nonzero rational scalars on earlier selected lines. -/
theorem exists_simultaneous_min_orbitHeight (r : ℕ) (d : ℕ → ℕ)
    (ρ : (i : ℕ) → MatrixRepresentation G (Fin (d i)))
    (v : (i : ℕ) → Fin (d i) → F)
    (hv : ∀ i, i < r → v i ≠ 0)
    (Q : ℕ → Subgroup (RationalGroupPoints F G)) (hQ : Antitone Q)
    (hline : ∀ i j, i < j → j < r → ∀ q : Q j,
      ∃ a : Fˣ, (rationalMatrix F G (ρ i) q).val *ᵥ v i = (a : F) • v i)
    (g : AdelicGroupPoints F G) :
    ∃ q : Q 0, ∀ i, i < r → ∀ s : Q i,
      orbitHeight F G (ρ i) (v i) (g * rational F G q) ≤
        orbitHeight F G (ρ i) (v i)
          ((g * rational F G q) * rational F G s) := by
  induction r with
  | zero => exact ⟨1, fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ r ih =>
    obtain ⟨q, hq⟩ := ih (fun i hi => hv i (Nat.lt_succ_of_lt hi))
      (fun i j hij hj => hline i j hij (Nat.lt_succ_of_lt hj))
    let h := g * rational F G q
    let p : Q r := minimumOrbitTranslate F G (ρ r) (Q r) (v r)
      (hv r (Nat.lt_succ_self r)) h
    let p₀ : Q 0 := ⟨p, hQ (Nat.zero_le r) p.2⟩
    refine ⟨q * p₀, ?_⟩
    have hprod : g * rational F G ((q * p₀ : Q 0) : RationalGroupPoints F G) =
        h * rational F G p := by
      change g * rational F G ((q : RationalGroupPoints F G) * p) =
        (g * rational F G q) * rational F G p
      rw [map_mul, mul_assoc]
    intro i hi s
    rw [hprod]
    obtain hi | hi := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)
    · obtain ⟨a, ha⟩ := hline i r hi (Nat.lt_succ_self r) p
      rw [orbitHeight_mul_rational_eq_of_scalar F G (ρ i) (v i)
        (hv i (Nat.lt_succ_of_lt hi)) p a ha h]
      let pᵢ : Q i := ⟨p, hQ (Nat.le_of_lt hi) p.2⟩
      have hm := hq i hi (pᵢ * s)
      change orbitHeight F G (ρ i) (v i) h ≤
        orbitHeight F G (ρ i) (v i)
          (h * rational F G ((p : RationalGroupPoints F G) * s)) at hm
      rw [map_mul, ← mul_assoc] at hm
      exact hm
    · subst i
      exact minimumOrbitTranslate_min F G (ρ r) (Q r) (v r)
        (hv r (Nat.lt_succ_self r)) h s

/-- The actual norm-one adelic group is covered by rational translates of the chain
minimum set with constant one. The rational translate stays in the first subgroup. -/
theorem exists_mul_rational_mem_chainHeightMinimalSet (r : ℕ) (d : ℕ → ℕ)
    (ρ : (i : ℕ) → MatrixRepresentation G (Fin (d i)))
    (v : (i : ℕ) → Fin (d i) → F)
    (hv : ∀ i, i < r → v i ≠ 0)
    (Q : ℕ → Subgroup (RationalGroupPoints F G)) (hQ : Antitone Q)
    (hline : ∀ i j, i < j → j < r → ∀ q : Q j,
      ∃ a : Fˣ, (rationalMatrix F G (ρ i) q).val *ᵥ v i = (a : F) • v i)
    (g : normOneSubgroup F G) :
    ∃ q : Q 0, g * rationalNormOne F G q ∈
      chainHeightMinimalSet F G r d ρ v Q 1 := by
  obtain ⟨q, hq⟩ := exists_simultaneous_min_orbitHeight F G r d ρ v hv Q hQ hline g
  refine ⟨q, ?_⟩
  intro i hi s
  simpa only [one_mul, Subgroup.coe_mul, rationalNormOne_val] using hq i hi s

end Langlands.Global.RepresentationGrowth

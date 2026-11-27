import Langlands.BushnellKutzko.SimpleCharacterCommutatorStep

/-! # Conjugation with trace error on the mixed neighborhood and double coset -/

noncomputable section

open ValuativeRel
open scoped Pointwise commutatorElement

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- An intertwining unit gives the conjugation formula when its trace-error
character vanishes on the domain. -/
theorem characterConjugationRatio_of_intertwining (ψF : AddChar F ℂ) (b : A)
    {H : Subgroup G} (θ : H →* ℂˣ) {x : G} (hx : x ∈ characterSelfIntertwining θ)
    (htr : ∀ u : H, elementCharacter (traceCharacter ψF) ((↑x⁻¹ : A) * b * (x : A) - b) (u : G) = 1) :
    characterConjugationRatio ψF b θ x := by
  intro u hu
  rw [htr u, mul_one, hx u hu]

/-- On the double coset of the centralizer by domain-normalizing factors,
the trace-error identities for the factors combine to give the identity on
the full overlap. -/
theorem characterConjugationRatio_of_centralizer_doubleCoset (ψF : AddChar F ℂ) (b : A)
    {H : Subgroup G} (θ : H →* ℂˣ) (Y : Set G)
    (hY : ∀ y ∈ Y, y ∈ Subgroup.normalizer (H : Set G) ∧ characterConjugationRatio ψF b θ y)
    (hB : (centralizerUnitGroup b : Set G) ⊆ characterSelfIntertwining θ)
    {x : G} (hx : x ∈ Y * (centralizerUnitGroup b : Set G) * Y) :
    characterConjugationRatio ψF b θ x := by
  obtain ⟨yt, hyt, z, hz, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨y, hy, t, ht, rfl⟩ := Set.mem_mul.mp hyt
  have htR := characterConjugationRatio_of_intertwining ψF b θ (hB ht) (by
    intro u
    have hc : b * (t : A) = (t : A) * b := ht
    have he : (↑t⁻¹ : A) * b * (t : A) - b = 0 := by
      rw [mul_assoc, hc, ← mul_assoc, Units.inv_mul, one_mul, sub_self]
    rw [he]
    simp [elementCharacter_apply])
  have hytR := characterConjugationRatio.mul_of_overlap ψF b θ (hY y hy).2 htR (by
    intro h hh
    apply (Subgroup.mem_normalizer_iff.mp (hY y hy).1 (t * (h : G) * t⁻¹)).mpr
    simpa only [mul_inv_rev, mul_assoc] using hh)
  exact characterConjugationRatio.mul_of_overlap ψF b θ hytR (hY z hz).2
    (fun h _ => (Subgroup.mem_normalizer_iff.mp (hY z hz).1 (h : G)).mp h.property)

variable [ValuativeRel F]

/-- Given the commutator formula for the restriction at `max m (r / 2)`,
the bounds `t < r` and `t / 2 ≤ m` give the trace ratio for mixed units
at depth `r - t`. The calculation for the inverse gives domain normalization. -/
theorem simpleCharacterConjugationRatio_of_mixed (L : LatticeChain 𝒪[F] F V)
    (ψF : AddChar F ℂ) (b : A) (J : ℕ → Subgroup G) {r t m : ℕ} (ht : t < r) (hm : t / 2 ≤ m)
    {H Hdeep : Subgroup G} (hinc : Hdeep ≤ H) (hHJ : H ≤ J (m + 1)) (θ : H →* ℂˣ)
    (hcomm : SimpleCharacterCommutatorAt L ψF b J r (max m (r / 2)) (θ.comp (Subgroup.inclusion hinc)))
    {x : G} (hx : (x : A) - 1 ∈ mixedAdjointLattice L b (r - t : ℕ) (-(r : ℤ))) :
    x ∈ Subgroup.normalizer (H : Set G) ∧ characterConjugationRatio ψF b θ x := by
  have hk : 1 ≤ r - t := by omega
  let X := mixedAdjointUnitGroup L b (r - t) (-(r : ℤ)) hk
  have eval (g : G) (hg : g ∈ X) (u : H) : characterCommutatorFormula ψF b θ g (u : G) := by
    have h := hcomm.mixedJ hk (show 1 ≤ m + 1 by omega)
      (show max m (r / 2) + 1 ≤ (r - t) + (m + 1) by omega)
      (show r + 1 ≤ (r - t) + 2 * (m + 1) by omega) hg (hHJ u.property)
    obtain ⟨hmem, hval⟩ := h
    exact ⟨hinc hmem, hval⟩
  have hdom (g : G) (hg : g ∈ X) (u : G) (hu : u ∈ H) : g * u * g⁻¹ ∈ H := by
    obtain ⟨hc, _⟩ := eval g hg ⟨u, hu⟩
    have he : ⁅g, u⁆ * u = g * u * g⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [← he]
    exact H.mul_mem hc hu
  refine ⟨Subgroup.mem_normalizer_iff.mpr (fun u => ⟨hdom x hx u, ?_⟩), ?_⟩
  · intro hu
    have h := hdom x⁻¹ (X.inv_mem hx) (x * u * x⁻¹) hu
    convert h using 1
    group
  · intro u hu
    obtain ⟨hc, hval⟩ := eval x hx u
    have hprod : (⟨_, hu⟩ : H) = ⟨_, hc⟩ * u := by
      apply Subtype.ext
      change x * (u : G) * x⁻¹ = ⁅x, (u : G)⁆ * (u : G)
      rw [commutatorElement_def]
      group
    rw [hprod, map_mul, Units.val_mul, hval, mul_comm]

end Langlands.BushnellKutzko

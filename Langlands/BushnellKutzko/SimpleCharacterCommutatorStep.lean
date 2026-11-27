import Langlands.BushnellKutzko.TerminalSimpleCharacter

/-! # The relative and deep factors in the simple-character commutator induction -/

noncomputable section

open ValuativeRel
open scoped commutatorElement Pointwise

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "O" => 𝒪[F]
local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem characterCommutatorFormula_of_restriction (ψF : AddChar F ℂ) (b : A)
    {H K : Subgroup G} (hKH : K ≤ H) {θ : H →* ℂˣ} {x y : G}
    (h : characterCommutatorFormula ψF b (θ.comp (Subgroup.inclusion hKH)) x y) :
    characterCommutatorFormula ψF b θ x y := by
  obtain ⟨hc, h⟩ := h
  exact ⟨hKH hc, h⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem relativeUnitFiltration_sub_one_mem_mixed (L : LatticeChain O F V) (b : A)
    {k : ℕ} (hk : 1 ≤ k) (j : ℤ) {u : G} (hu : u ∈ relativeUnitFiltration L b k) :
    (u : A) - 1 ∈ mixedAdjointLattice L b k j :=
  centralizerLattice_le_mixedAdjointLattice L b k j ((mem_relativeUnitFiltration_iff_of_pos L b hk u).mp hu)

theorem relativeUnitFiltration_le_relativeOrderNormalizer (L : LatticeChain O F V)
    (b : A) (k : ℕ) : relativeUnitFiltration L b k ≤ relativeOrderNormalizer L b :=
  fun _ hu => ⟨hu.1, ((normalizer F V L).1 k).1 hu.2⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem relative_commutator_formula (L : LatticeChain O F V) (ψF : AddChar F ℂ) (b : A)
    {H : Subgroup G} (θ : H →* ℂˣ) (hθ : factorsThroughCentralizerDet b θ)
    {m k l : ℕ} (hH : relativeUnitFiltration L b (m + 1) ≤ H) (hkl : m + 1 ≤ k + l)
    {u v : G} (hu : u ∈ relativeUnitFiltration L b k) (hv : v ∈ relativeUnitFiltration L b l) :
    characterCommutatorFormula ψF b θ u v := by
  apply characterCommutatorFormula.of_centralizer ψF hθ hu.1 hv.1
  refine hH ⟨?_, L.unitFiltration_antitone hkl (L.commutatorElement_mem_unitFiltration hu.2 hv.2)⟩
  rw [commutatorElement_def]
  let B := centralizerUnitGroup b
  exact B.mul_mem (B.mul_mem (B.mul_mem hu.1 hv.1) (B.inv_mem hu.1)) (B.inv_mem hv.1)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem trace_conjugationDifference_eq_one_of_centralizer (ψF : AddChar F ℂ) (b : A)
    {u : G} (hu : u ∈ centralizerUnitGroup b) (z : A) :
    traceCharacter ψF (((↑u⁻¹ : A) * b * (u : A) - b) * z) = 1 := by
  have h : b * (u : A) = (u : A) * b := hu
  rw [mul_assoc (↑u⁻¹ : A) b (u : A), h, ← mul_assoc (↑u⁻¹ : A), Units.inv_mul, one_mul,
    sub_self, zero_mul, AddChar.map_zero_eq_one]

/-- The two commutator identities at one character depth, for a mixed first
input and a second input in either the mixed lattice or the J group. -/
structure SimpleCharacterCommutatorAt (L : LatticeChain O F V) (ψF : AddChar F ℂ) (b : A)
    (J : ℕ → Subgroup G) (r m : ℕ) {H : Subgroup G} (θ : H →* ℂˣ) : Prop where
  mixed : ∀ {k l : ℕ}, 1 ≤ k → 1 ≤ l → m + 1 ≤ k + l → r + 1 ≤ k + 2 * l →
    ∀ {x y : G}, (x : A) - 1 ∈ mixedAdjointLattice L b k (-(r : ℤ)) →
      (y : A) - 1 ∈ mixedAdjointLattice L b l (-(r : ℤ)) → characterCommutatorFormula ψF b θ x y
  mixedJ : ∀ {k l : ℕ}, 1 ≤ k → 1 ≤ l → m + 1 ≤ k + l → r + 1 ≤ k + 2 * l →
    ∀ {x y : G}, (x : A) - 1 ∈ mixedAdjointLattice L b k (-(r : ℤ)) →
      y ∈ J l → characterCommutatorFormula ψF b θ x y

/-- The successor calculation for a mixed second input, given its relative
and deeper factors. The inductive commutators are evaluated after restriction
and then combined on the original domain. -/
theorem simpleCharacterCommutatorAt_successor_mixed (L : LatticeChain O F V)
    (ψF : AddChar F ℂ) (b : A) (J : ℕ → Subgroup G) {r s m k l : ℕ}
    (hrs : r < s) (hm : r / 2 ≤ m) (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hkl : m + 1 ≤ k + l) (htrace : r + 1 ≤ k + 2 * l)
    {H Hdeep : Subgroup G} (hinc : Hdeep ≤ H) (θ : H →* ℂˣ)
    (hdet : factorsThroughCentralizerDet b θ) (hnorm : relativeOrderNormalizer L b ≤ characterNormalizerSubgroup θ)
    (hH : relativeUnitFiltration L b (m + 1) ≤ H)
    (ih : SimpleCharacterCommutatorAt L ψF b J s (max m (s / 2)) (θ.comp (Subgroup.inclusion hinc)))
    {x₁ x₂ y₁ y₂ : G} (hx₁ : x₁ ∈ relativeUnitFiltration L b k)
    (hx₂ : (x₂ : A) - 1 ∈ mixedAdjointLattice L b (k + (s - r) : ℕ) (-(s : ℤ)))
    (hy₁ : y₁ ∈ relativeUnitFiltration L b l)
    (hy₂ : (y₂ : A) - 1 ∈ mixedAdjointLattice L b (l + (s - r) : ℕ) (-(s : ℤ)))
    (hy : (↑(y₁ * y₂) : A) - 1 ∈ mixedAdjointLattice L b l (-(s : ℤ))) :
    characterCommutatorFormula ψF b θ (x₁ * x₂) (y₁ * y₂) := by
  have hx₁n := hnorm (relativeUnitFiltration_le_relativeOrderNormalizer L b k hx₁)
  have hy₁n := hnorm (relativeUnitFiltration_le_relativeOrderNormalizer L b l hy₁)
  have h₁₁ := relative_commutator_formula L ψF b θ hdet hH hkl hx₁ hy₁
  have h₁₂ := characterCommutatorFormula_of_restriction ψF b hinc
    (ih.mixed hk (show 1 ≤ l + (s - r) by omega)
      (show max m (s / 2) + 1 ≤ k + (l + (s - r)) by omega)
      (show s + 1 ≤ k + 2 * (l + (s - r)) by omega)
      (relativeUnitFiltration_sub_one_mem_mixed L b hk (-(s : ℤ)) hx₁) hy₂)
  have h₁ := h₁₁.mul_right ψF h₁₂ hy₁n (trace_conjugationDifference_eq_one_of_centralizer ψF b hx₁.1 _)
  have h₂ := characterCommutatorFormula_of_restriction ψF b hinc
    (ih.mixed (show 1 ≤ k + (s - r) by omega) hl
      (show max m (s / 2) + 1 ≤ k + (s - r) + l by omega)
      (show s + 1 ≤ k + (s - r) + 2 * l by omega) hx₂ hy)
  exact characterCommutatorFormula.mul_left_of_centralizer ψF h₁ h₂ hx₁.1 hx₁n

/-- The successor calculation for a J input, using the relative and deep
factors of that input to evaluate its commutator with the relative factor
of the first input. -/
theorem simpleCharacterCommutatorAt_successor_J (L : LatticeChain O F V)
    (ψF : AddChar F ℂ) (b : A) (J : ℕ → Subgroup G) {r s m k l ldeep : ℕ}
    (hrs : r < s) (hm : r / 2 ≤ m) (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hkl : m + 1 ≤ k + l) (htrace : r + 1 ≤ k + 2 * l)
    (hld : max l ((s + 1) / 2) ≤ ldeep)
    {H Hdeep : Subgroup G} (hinc : Hdeep ≤ H) (θ : H →* ℂˣ)
    (hdet : factorsThroughCentralizerDet b θ) (hnorm : relativeOrderNormalizer L b ≤ characterNormalizerSubgroup θ)
    (hH : relativeUnitFiltration L b (m + 1) ≤ H)
    (ih : SimpleCharacterCommutatorAt L ψF b J s (max m (s / 2)) (θ.comp (Subgroup.inclusion hinc)))
    {x₁ x₂ y₁ y₂ : G} (hx₁ : x₁ ∈ relativeUnitFiltration L b k)
    (hx₂ : (x₂ : A) - 1 ∈ mixedAdjointLattice L b (k + (s - r) : ℕ) (-(s : ℤ)))
    (hy₁ : y₁ ∈ relativeUnitFiltration L b l) (hy₂ : y₂ ∈ J ldeep) (hy : y₁ * y₂ ∈ J l) :
    characterCommutatorFormula ψF b θ (x₁ * x₂) (y₁ * y₂) := by
  have hx₁n := hnorm (relativeUnitFiltration_le_relativeOrderNormalizer L b k hx₁)
  have hy₁n := hnorm (relativeUnitFiltration_le_relativeOrderNormalizer L b l hy₁)
  have h₁₁ := relative_commutator_formula L ψF b θ hdet hH hkl hx₁ hy₁
  have h₁₂ := characterCommutatorFormula_of_restriction ψF b hinc
    (ih.mixedJ hk (show 1 ≤ ldeep by omega)
      (show max m (s / 2) + 1 ≤ k + ldeep by omega) (show s + 1 ≤ k + 2 * ldeep by omega)
      (relativeUnitFiltration_sub_one_mem_mixed L b hk (-(s : ℤ)) hx₁) hy₂)
  have h₁ := characterCommutatorFormula.mul_right ψF h₁₁ h₁₂ hy₁n
    (trace_conjugationDifference_eq_one_of_centralizer ψF b hx₁.1 _)
  have h₂ := characterCommutatorFormula_of_restriction ψF b hinc
    (ih.mixedJ (show 1 ≤ k + (s - r) by omega) hl
      (show max m (s / 2) + 1 ≤ k + (s - r) + l by omega)
      (show s + 1 ≤ k + (s - r) + 2 * l by omega) hx₂ hy)
  exact characterCommutatorFormula.mul_left_of_centralizer ψF h₁ h₂ hx₁.1 hx₁n

end Langlands.BushnellKutzko

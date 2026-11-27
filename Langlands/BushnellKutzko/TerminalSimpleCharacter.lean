import Langlands.BushnellKutzko.SimpleCharacterCommutatorAlgebra
import Langlands.BushnellKutzko.SimpleCharacterTransferMinimal

/-! # Domain and relative normalizer of a terminal simple character -/

noncomputable section

open ValuativeRel
open scoped Pointwise commutatorElement

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "O" => 𝒪[F]

/-- At a positive level the relative group is given by the relative lattice. -/
theorem mem_relativeUnitFiltration_iff_of_pos (L : LatticeChain O F V) (b : A) {k : ℕ}
    (hk : 1 ≤ k) (g : G) : g ∈ relativeUnitFiltration L b k ↔ (g : A) - 1 ∈ centralizerLattice L b k := by
  have he : adjointMap O b ((g : A) - 1) = b * (g : A) - (g : A) * b := by
    change b * ((g : A) - 1) - ((g : A) - 1) * b = _
    noncomm_ring
  constructor
  · intro h
    refine ⟨h.2.2.2, ?_⟩
    change adjointMap O b ((g : A) - 1) = 0
    rw [he, sub_eq_zero]
    exact h.1
  · intro h
    refine ⟨?_, (L.mem_unitFiltration_of_sub_one_iff hk).mpr h.1⟩
    have hz : adjointMap O b ((g : A) - 1) = 0 := h.2
    rw [he] at hz
    exact sub_eq_zero.mp hz

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The product form of the terminal domain. -/
theorem simpleHGroup_nil_eq_product (L : LatticeChain O F V) (n : ℤ) (b : A)
    {k : ℕ} (hk : 1 ≤ k) : (simpleHGroup L n b [] k : Set G) =
      (relativeUnitFiltration L b k : Set G) * (L.unitFiltration (max k (simpleHCutoff n).toNat) : Set G) := by
  rw [simpleHGroup_nil_eq_sup L n b k hk]
  apply Subgroup.coe_mul_of_left_le_normalizer_right
  rw [(normalizer F V L).2.2.1]
  exact fun _ hg => ((normalizer F V L).1 k).1 hg.2

/-- The relative order normalizer preserves a terminal simple character,
by the determinant on the relative factor and the trace on the deep factor. -/
theorem relativeOrderNormalizer_le_characterNormalizerSubgroup_nil
    (L : LatticeChain O F V) (n : ℤ) (ψF : AddChar F ℂ) (b : A) (m : ℕ)
    {θ : simpleHGroup L n b [] (m + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF L n b [] m) :
    relativeOrderNormalizer L b ≤ characterNormalizerSubgroup θ := by
  let H := simpleHGroup L n b [] (m + 1)
  let R := relativeUnitFiltration L b (m + 1)
  let D := L.unitFiltration (max (m + 1) (simpleHCutoff n).toNat)
  have hsplit : H = R ⊔ D := simpleHGroup_nil_eq_sup L n b (m + 1) (by omega)
  have hHR : R ≤ H := hsplit.symm ▸ le_sup_left
  have hHD : D ≤ H := hsplit.symm ▸ le_sup_right
  have hprod : (H : Set G) = (R : Set G) * (D : Set G) := simpleHGroup_nil_eq_product L n b (by omega)
  intro g hg
  have hUg (k : ℕ) : g ∈ Subgroup.normalizer (L.unitFiltration k : Set G) := by
    rw [(normalizer F V L).2.2.1]
    exact hg.2
  have hRg : g ∈ Subgroup.normalizer (R : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨(centralizerUnitGroup b).le_normalizer hg.1, hUg _⟩
  have hDg : g ∈ Subgroup.normalizer (D : Set G) := hUg _
  change g ∈ characterNormalizer θ
  refine ⟨?_, ?_⟩
  · change g ∈ Subgroup.normalizer (H : Set G)
    rw [hsplit]
    exact Subgroup.inf_normalizer_le_normalizer_sup R D ⟨hRg, hDg⟩
  · intro h hh
    have homo : (h : G) ∈ (R : Set G) * (D : Set G) := hprod ▸ h.property
    obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.mp homo
    let u₀ : H := ⟨u, hHR hu⟩
    let v₀ : H := ⟨v, hHD hv⟩
    have hgu := (Subgroup.mem_normalizer_iff.mp hRg u).mp hu
    have hgv := (Subgroup.mem_normalizer_iff.mp hDg v).mp hv
    let u₁ : H := ⟨_, hHR hgu⟩
    let v₁ : H := ⟨_, hHD hgv⟩
    have heu : θ u₁ = θ u₀ := hθ.2.conj_eq hg.1 u₀ hu.1 (hHR hgu)
    have hev : θ v₁ = θ v₀ := by
      apply Units.ext
      have hv₀ := hθ.1 v₀ (L.unitFiltration_antitone (le_max_right _ _) hv)
      have hv₁ := hθ.1 v₁ (L.unitFiltration_antitone (le_max_right _ _) hgv)
      rw [hv₁, hv₀]
      change elementCharacter (traceCharacter ψF) b (g * v * g⁻¹) =
        elementCharacter (traceCharacter ψF) b v
      rw [elementCharacter_conj]
      have hgB : b * (g : A) = (g : A) * b := hg.1
      rw [mul_assoc, hgB, ← mul_assoc, Units.inv_mul, one_mul]
    have hleft : (⟨_, hh⟩ : H) = u₁ * v₁ := by
      apply Subtype.ext
      change g * (h : G) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹)
      rw [← huv]
      group
    have hright : h = u₀ * v₀ := Subtype.ext huv.symm
    rw [hleft, hright, map_mul, map_mul, heu, hev]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The commutator of two congruence units belongs to the step at the sum of their depths. -/
theorem LatticeChain.commutatorElement_mem_unitFiltration (L : LatticeChain O F V)
    {k l : ℕ} {x y : G} (hx : x ∈ L.unitFiltration k) (hy : y ∈ L.unitFiltration l) :
    ⁅x, y⁆ ∈ L.unitFiltration (k + l) := by
  have h0 : ⁅x, y⁆ ∈ L.unitFiltration 0 := by
    have hx0 := L.unitFiltration_antitone (Nat.zero_le _) hx
    have hy0 := L.unitFiltration_antitone (Nat.zero_le _) hy
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx0 hy0) (inv_mem hx0)) (inv_mem hy0)
  refine ⟨h0.1, h0.2.1, ?_⟩
  rw [commutatorElement_sub_one, Nat.cast_add]
  have hc := commutator_mem_endFiltration L hx.2.2 hy.2.2
  simpa only [add_zero] using L.mul_mem_endFiltration (L.mul_mem_endFiltration hc hx.2.1) hy.2.1

/-- The commutator identity for a terminal character when the commutator
depth reaches both the character domain and its additive-character range. -/
theorem characterCommutatorFormula_of_terminal (L : LatticeChain O F V)
    (n : ℤ) (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {b : A} (hb : b ∈ L.endFiltration (-n)) {m : ℕ}
    {θ : simpleHGroup L n b [] (m + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF L n b [] m) {k l : ℕ}
    (hkl : max (m + 1) (simpleHCutoff n).toNat ≤ k + l)
    (htrace : n + 1 ≤ (k : ℤ) + 2 * (l : ℤ))
    {x y : G} (hx : x ∈ L.unitFiltration k) (hy : y ∈ L.unitFiltration l) :
    characterCommutatorFormula ψF b θ x y := by
  have hU := L.unitFiltration_antitone hkl (L.commutatorElement_mem_unitFiltration hx hy)
  have hh : ⁅x, y⁆ ∈ simpleHGroup L n b [] (m + 1) := by
    rw [simpleHGroup_nil_eq_sup L n b (m + 1) (by omega)]
    exact Subgroup.mem_sup_right hU
  refine ⟨hh, ?_⟩
  rw [hθ.1 ⟨_, hh⟩ (L.unitFiltration_antitone (le_max_right _ _) hU)]
  exact elementCharacter_commutator_of_depth L ψF hψ hb htrace hx hy

end Langlands.BushnellKutzko

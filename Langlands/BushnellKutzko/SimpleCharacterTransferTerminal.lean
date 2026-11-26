import Langlands.BushnellKutzko.SimpleCharacterTransferGluing
import Langlands.BushnellKutzko.SimpleCharacterTransferHigh
import Langlands.BushnellKutzko.SimpleCharacterTransferRelativeCharacter
import Langlands.BushnellKutzko.PureStratumApproximationCandidateBound

/-! # Transfer for terminal defining sequences -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

private theorem terminal_high_depth (m : ℕ) {n : ℤ} (hn : 0 ≤ n) :
    max (m + 1) (simpleHCutoff n).toNat = max m (n / 2).toNat + 1 := by
  have h : (simpleHCutoff n).toNat = (n / 2).toNat + 1 := by
    unfold simpleHCutoff
    omega
  rw [h]
  omega

/-- The normalized raised index when the cutoff depth is an integral multiple of the period. -/
theorem normalized_max_half_div (e : ℕ) (he : 0 < e)
    {n : ℤ} {t : ℕ} (hn : n = (e : ℤ) * t) (m : ℕ) :
    max m (n / 2).toNat / e = max (m / e) (t / 2) := by
  have hn' : n = (↑(e * t) : ℤ) := by exact_mod_cast hn
  have hcast : (↑((e * t) / 2 : ℕ) : ℤ) = (↑(e * t) : ℤ) / 2 := Int.natCast_ediv (e * t) 2
  rw [hn', ← hcast, Int.toNat_natCast]
  have hmono : Monotone (fun a : ℕ => a / e) := fun _ _ h => Nat.div_le_div_right h
  rw [hmono.map_max, Nat.div_div_eq_div_mul, mul_comm 2 e, ← Nat.div_div_eq_div_mul,
    Nat.mul_div_cancel_left _ he]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Existence and uniqueness of transfer for two terminal defining sequences. -/
theorem simpleCharacterTransfer_nil (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (L M : LatticeChain 𝒪[F] F V) (n₁ n₂ : ℤ) (β : A) (m₁ m₂ : ℕ)
    (hn₁ : (m₁ : ℤ) < n₁) (hn₂ : (m₂ : ℤ) < n₂)
    (hv₁ : L.valuation β = ((-n₁ : ℤ) : WithTop ℤ)) (hv₂ : M.valuation β = ((-n₂ : ℤ) : WithTop ℤ))
    (hf : IsField (elementAlgebra β))
    (hL : letI := hf.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ L.stabilizer)
    (hM : letI := hf.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ M.stabilizer)
    (hm : m₁ / (L.period / elementRamificationIndex F β) =
      m₂ / (M.period / elementRamificationIndex F β))
    (θ₁ : simpleHGroup L n₁ β [] (m₁ + 1) →* ℂˣ)
    (hθ₁ : θ₁ ∈ simpleCharacters ψF L n₁ β [] m₁) :
    ∃! θ₂, θ₂ ∈ simpleCharacters ψF M n₂ β [] m₂ ∧
      characterAgreesOn (simpleHGroup L n₁ β [] (m₁ + 1) ⊓
        simpleHGroup M n₂ β [] (m₂ + 1)) θ₁ θ₂ (fun _ => 1) := by
  classical
  let E := elementAlgebra β
  let : Field E := hf.toField
  let := L.finiteDimensional
  let : FiniteDimensional F E := inferInstanceAs (FiniteDimensional F (elementAlgebra β))
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  let C := L.relativeLatticeChain hL (isIntegral_iff_mem_spectralInteger F E)
  let D := M.relativeLatticeChain hM (isIntegral_iff_mem_spectralInteger F E)
  have hC := L.mem_relativeLatticeChain hL (isIntegral_iff_mem_spectralInteger F E)
  have hD := M.mem_relativeLatticeChain hM (isIntegral_iff_mem_spectralInteger F E)
  have hCp : C.period = L.period / subfieldRamificationIndex F E := L.relativeLatticeChain_period_eq_div hL
  have hDp : D.period = M.period / subfieldRamificationIndex F E := M.relativeLatticeChain_period_eq_div hM
  have hm' : m₁ / (L.period / subfieldRamificationIndex F E) =
      m₂ / (M.period / subfieldRamificationIndex F E) := by
    simpa only [elementRamificationIndex, hf, dite_true] using hm
  let b : E := ⟨β, Algebra.self_mem_adjoin_singleton F β⟩
  have hb : b ≠ 0 := by
    intro hz
    have h : β = 0 := congrArg Subtype.val hz
    rw [h, L.valuation_zero] at hv₁
    exact WithTop.top_ne_coe hv₁
  let j₁ := max m₁ (n₁ / 2).toNat
  let j₂ := max m₂ (n₂ / 2).toNat
  have hj₁ : m₁ + 1 ≤ j₁ + 1 := Nat.succ_le_succ (le_max_left ..)
  have hcut₁ : max (m₁ + 1) (simpleHCutoff n₁).toNat = j₁ + 1 := terminal_high_depth m₁ (by omega)
  have hcut₂ : max (m₂ + 1) (simpleHCutoff n₂).toNat = j₂ + 1 := terminal_high_depth m₂ (by omega)
  have hhigh₁ : n₁ < 2 * ((j₁ + 1 : ℕ) : ℤ) := by
    have hj : (n₁ / 2).toNat ≤ j₁ := le_max_right ..
    omega
  have hhigh₂ : n₂ < 2 * ((j₂ + 1 : ℕ) : ℤ) := by
    have hj : (n₂ / 2).toNat ≤ j₂ := le_max_right ..
    omega
  have hj_norm : j₁ / (L.period / subfieldRamificationIndex F E) =
      j₂ / (M.period / subfieldRamificationIndex F E) := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
    have hs₁ := WithTop.coe_injective ((valuation_subfieldEmbedding_of_relative L C hC b hb hπ).symm.trans hv₁)
    have hs₂ := WithTop.coe_injective ((valuation_subfieldEmbedding_of_relative M D hD b hb hπ).symm.trans hv₂)
    let t := (-ordOf hπ b).toNat
    have ht : 0 ≤ -ordOf hπ b := by
      by_contra! h
      have hh := mul_neg_of_pos_of_neg (show (0 : ℤ) < (C.period : ℤ) by exact_mod_cast C.period_pos) h
      rw [mul_neg, hs₁, neg_neg] at hh
      omega
    have hnt₁ : n₁ = (C.period : ℤ) * (t : ℤ) := by
      simp only [t, Int.toNat_of_nonneg ht, mul_neg, hs₁, neg_neg]
    have hnt₂ : n₂ = (D.period : ℤ) * (t : ℤ) := by
      simp only [t, Int.toNat_of_nonneg ht, mul_neg, hs₂, neg_neg]
    rw [← hCp, ← hDp, normalized_max_half_div C.period C.period_pos hnt₁,
      normalized_max_half_div D.period D.period_pos hnt₂, hCp, hDp, hm']
  let ι := relativeEndUnits (F := F) (V := V) E
  let H₁ := simpleHGroup L n₁ β [] (m₁ + 1)
  let H₂ := simpleHGroup M n₂ β [] (m₂ + 1)
  let U₂ := relativeUnitFiltration M β (m₂ + 1)
  let D₂ := M.unitFiltration (j₂ + 1)
  have hθ₁' := show (∀ g : H₁, (g : G) ∈ L.unitFiltration (simpleHCutoff n₁).toNat →
      (θ₁ g : ℂ) = elementCharacter (traceCharacter ψF) β g) ∧
      factorsThroughCentralizerDet β θ₁ from hθ₁
  obtain ⟨χU, hχUdet, hrel⟩ :=
    exists_relativeCharacter_of_equal_normalized_depth L M n₁ β [] m₁ m₂ hf hL hM hm θ₁ hθ₁'.2
  have hrange : ι.range = centralizerUnitGroup β := relativeEndUnits_range_eq_centralizer β hf
  let χD : D₂ →* ℂˣ := highElementCharacter M ψF hψ n₂ (j₂ + 1) hhigh₂ β
    (PureApproximation.mem_endFiltration_of_le_valuation M (by rw [hv₂]))
  have hnormal : U₂ ≤ Subgroup.normalizer (D₂ : Set G) := by
    change U₂ ≤ Subgroup.normalizer (M.unitFiltration (j₂ + 1) : Set G)
    rw [(normalizer F V M).2.2.1 (j₂ + 1)]
    exact fun _ h => ((normalizer F V M).1 (m₂ + 1)).1 h.2
  have hinv (u : U₂) (v : D₂) (h : (u : G)⁻¹ * (v : G) * u ∈ D₂) : χD ⟨_, h⟩ = χD v := by
    apply Units.ext
    exact elementCharacter_conj_eq ψF β (u : G)⁻¹ v (Commute.units_inv_right u.2.1)
  have hcompat (g : G) (hgU : g ∈ U₂) (hgD : g ∈ D₂) : χU ⟨g, hgU⟩ = χD ⟨g, hgD⟩ := by
    obtain ⟨y, rfl⟩ := (hrange.symm ▸ hgU.1 : g ∈ ι.range)
    obtain ⟨x, hx, heq⟩ := exists_relative_unit_in_inf_with_det L M hL hM j₁ j₂ hj_norm hgD
    have hxC : ι x ∈ centralizerUnitGroup β := hrange ▸ ⟨x, rfl⟩
    have hx₁H : ι x ∈ H₁ := relativeUnitFiltration_le_simpleHGroup L n₁ β [] _
      ⟨hxC, L.unitFiltration_antitone hj₁ hx.1⟩
    have hx₁cut : ι x ∈ L.unitFiltration (simpleHCutoff n₁).toNat :=
      L.unitFiltration_antitone (by rw [← hcut₁]; exact le_max_right ..) hx.1
    have hxTrace := elementCharacter_eq_relativeDet_of_highDepth L C hC ψF hψ b hb n₁
      hv₁ (j₁ + 1) hhigh₁ x ((L.mem_unitFiltration_restrictScalars_iff C hC _ x).mp hx.1)
    have hyTrace := elementCharacter_eq_relativeDet_of_highDepth M D hD ψF hψ b hb n₂
      hv₂ (j₂ + 1) hhigh₂ y ((M.mem_unitFiltration_restrictScalars_iff D hD _ y).mp hgD)
    apply Units.ext
    calc (χU ⟨ι y, hgU⟩ : ℂ) = (θ₁ ⟨ι x, hx₁H⟩ : ℂ) :=
          congrArg Units.val (hrel x y hx₁H hgU heq).symm
      _ = elementCharacter (traceCharacter ψF) β (ι x) := hθ₁'.1 _ hx₁cut
      _ = (χD ⟨ι y, hgD⟩ : ℂ) := by
          change elementCharacter (traceCharacter ψF) (subfieldEmbedding F E V b) (ι x) =
            elementCharacter (traceCharacter ψF) (subfieldEmbedding F E V b) (ι y)
          rw [hxTrace, hyTrace, heq]
  obtain ⟨χ, hχU₂, hχD₂⟩ := exists_monoidHom_of_compatible_restrictions U₂ D₂ χU χD hnormal hinv hcompat
  have hH₂ : H₂ = U₂ ⊔ D₂ := by
    dsimp only [H₂, U₂, D₂]
    rw [simpleHGroup_nil_eq_sup M n₂ β (m₂ + 1) (by omega), hcut₂]
  let θ₂ := χ.comp (MulEquiv.subgroupCongr hH₂).toMonoidHom
  have hHU : U₂ ≤ H₂ := relativeUnitFiltration_le_simpleHGroup M n₂ β [] _
  have hHD : D₂ ≤ H₂ := hH₂.symm ▸ le_sup_right
  have hθ₂U (u : U₂) : θ₂ ⟨u, hHU u.2⟩ = χU u := hχU₂ u
  have hθ₂D (v : D₂) : θ₂ ⟨v, hHD v.2⟩ = χD v := hχD₂ v
  have hmem : θ₂ ∈ simpleCharacters ψF M n₂ β [] m₂ := by
    refine ⟨?_, factorsThroughCentralizerDet_of_restriction M n₂ β [] _ χU θ₂ hχUdet hθ₂U⟩
    · intro g hg
      have hDr : (g : G) ∈ D₂ := by
        change (g : G) ∈ M.unitFiltration (j₂ + 1)
        rw [← hcut₂]
        rcases le_total (m₂ + 1) (simpleHCutoff n₂).toNat with h | h
        · rwa [max_eq_right h]
        · rw [max_eq_left h]
          exact simpleHGroup_le_unitFiltration M n₂ β [] _ g.2
      exact congrArg Units.val (hθ₂D ⟨g, hDr⟩)
  have hagree : characterAgreesOn (H₁ ⊓ H₂) θ₁ θ₂ (fun _ => 1) := by
    apply (characterAgreesOn_inf_iff _ _).mpr
    intro g hg₁ hg₂
    obtain ⟨u, ⟨hu₁, hu₂⟩, v, ⟨hvs₁, hvs₂⟩, rfl⟩ := exists_simpleHGroup_inf_factorization
      L M n₁ n₂ β [] [] (m₁ + 1) (m₂ + 1) (by omega) (by omega) hf hL hM
      (fun h => simpleHGroup_nil_mem_lattice L n₁ β (by omega) h)
      (fun h => simpleHGroup_nil_mem_lattice M n₂ β (by omega) h) hg₁ hg₂
    have hu₁H := relativeUnitFiltration_le_simpleHGroup L n₁ β [] (m₁ + 1) hu₁
    have huEq : θ₁ ⟨u, hu₁H⟩ = θ₂ ⟨u, hHU hu₂⟩ := by
      rw [hθ₂U ⟨u, hu₂⟩]
      obtain ⟨y, rfl⟩ := (hrange.symm ▸ hu₂.1 : u ∈ ι.range)
      exact hrel y y hu₁H hu₂ rfl
    have hv₁D : v ∈ L.unitFiltration (j₁ + 1) := by
      rw [← hcut₁]
      exact simpleHGroup_le_unitFiltration L n₁ β [] _ hvs₁
    have hv₂D : v ∈ D₂ := by
      change v ∈ M.unitFiltration (j₂ + 1)
      rw [← hcut₂]
      exact simpleHGroup_le_unitFiltration M n₂ β [] _ hvs₂
    have hv₁H : v ∈ H₁ := simpleHGroup_antitone L n₁ β [] (le_max_left ..) hvs₁
    have hvEq : θ₁ ⟨v, hv₁H⟩ = θ₂ ⟨v, hHD hv₂D⟩ := by
      rw [hθ₂D ⟨v, hv₂D⟩]
      exact Units.ext (hθ₁'.1 _ (L.unitFiltration_antitone (by rw [← hcut₁]; exact le_max_right ..) hv₁D))
    change θ₁ (⟨u, hu₁H⟩ * ⟨v, hv₁H⟩) = θ₂ (⟨u, hHU hu₂⟩ * ⟨v, hHD hv₂D⟩)
    rw [map_mul, map_mul, huEq, hvEq]
  exact ⟨θ₂, ⟨hmem, hagree⟩, fun θ' hθ' => simpleCharacterTransfer_unique_nil ψF L M n₁ n₂ β []
    m₁ m₂ hf hL hM hm hθ'.1 hmem hθ'.2 hagree⟩

end Langlands.BushnellKutzko

import Langlands.BushnellKutzko.SimpleCharacterTransferRelativeCharacter
import Langlands.BushnellKutzko.SimpleCharacterTransferGluing

/-! # Extending an agreeing high restriction -/

open ValuativeRel
open scoped Pointwise

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uG uC

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

private theorem relativeOrderNormalizer_le_normalizer_relativeUnitFiltration
    (L : LatticeChain 𝒪[F] F V) (β : A) (k : ℕ) :
    relativeOrderNormalizer L β ≤ Subgroup.normalizer (relativeUnitFiltration L β k : Set G) := by
  intro g hg
  have hC := Subgroup.le_normalizer (H := centralizerUnitGroup β) hg.1
  have hU : g ∈ Subgroup.normalizer (L.unitFiltration k : Set G) :=
    ((normalizer F V L).2.2.1 k).symm ▸ hg.2
  exact Subgroup.mem_normalizer_iff.mpr fun x => and_congr
    (Subgroup.mem_normalizer_iff.mp hC x) (Subgroup.mem_normalizer_iff.mp hU x)

/-- Two characters on a subgroup join agree if their restrictions to both
of the generating subgroups agree. -/
theorem monoidHom_eq_of_agree_on_generators {P : Type uG} [Group P] {Q : Type uC} [Monoid Q]
    {H U D : Subgroup P} (hH : H = U ⊔ D) (hU : U ≤ H) (hD : D ≤ H) (χ χ' : H →* Q)
    (hu : ∀ u : U, χ ⟨u, hU u.2⟩ = χ' ⟨u, hU u.2⟩)
    (hd : ∀ d : D, χ ⟨d, hD d.2⟩ = χ' ⟨d, hD d.2⟩) : χ = χ' := by
  let K := (χ.eqLocus χ').map H.subtype
  have hUK : U ≤ K := fun u hu' => ⟨⟨u, hU hu'⟩, hu ⟨u, hu'⟩, rfl⟩
  have hDK : D ≤ K := fun d hd' => ⟨⟨d, hD hd'⟩, hd ⟨d, hd'⟩, rfl⟩
  have hK : H ≤ K := hH.symm ▸ sup_le hUK hDK
  apply DFunLike.ext
  intro x
  obtain ⟨y, hy, heq⟩ := hK x.2
  have h : y = x := Subtype.ext heq
  subst y
  exact hy

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 150000 in
/-- A high character agreeing over the common high subgroup extends to a character
on the second chain with the required relative determinant and full agreement. -/
theorem exists_agreeing_extension_of_high (L M : LatticeChain 𝒪[F] F V)
    (n₁ n₂ : ℤ) (β : A) (tail₁ tail₂ : List A) (m₁ m₂ j₁ j₂ : ℕ)
    (hf : IsField (elementAlgebra β))
    (hL : letI := hf.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ L.stabilizer)
    (hM : letI := hf.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ M.stabilizer)
    (hm : m₁ / (L.period / elementRamificationIndex F β) =
      m₂ / (M.period / elementRamificationIndex F β))
    (hj : j₁ / (L.period / elementRamificationIndex F β) =
      j₂ / (M.period / elementRamificationIndex F β))
    (hc₁ : j₁ + 1 = max (m₁ + 1)
      (simpleHCutoff (if tail₁.isEmpty then n₁ else finiteCriticalDepth L n₁ β)).toNat)
    (hc₂ : j₂ + 1 = max (m₂ + 1)
      (simpleHCutoff (if tail₂.isEmpty then n₂ else finiteCriticalDepth M n₂ β)).toNat) :
    let H₁ := simpleHGroup L n₁ β tail₁ (m₁ + 1)
    let H₂ := simpleHGroup M n₂ β tail₂ (m₂ + 1)
    let D₁ := simpleHGroup L n₁ β tail₁ (j₁ + 1)
    let D₂ := simpleHGroup M n₂ β tail₂ (j₂ + 1)
    let U₂ := relativeUnitFiltration M β (m₂ + 1)
    let K := relativeOrderNormalizer M β
    ∀ (_ : ∀ {g}, g ∈ H₁ → (g : A) ∈ simpleHLattice L n₁ β tail₁)
      (_ : ∀ {g}, g ∈ H₂ → (g : A) ∈ simpleHLattice M n₂ β tail₂)
      (_ : H₂ = U₂ ⊔ D₂) (_ : K ≤ Subgroup.normalizer (H₂ : Set G))
      (θ₁ : H₁ →* ℂˣ) (χHigh : D₂ →* ℂˣ),
      factorsThroughCentralizerDet β θ₁ → factorsThroughCentralizerDet β χHigh →
      (K : Set G) ⊆ characterNormalizer χHigh →
      (∀ g (_hg₁ : g ∈ D₁) (hg₂ : g ∈ D₂), ∃ h : g ∈ H₁, θ₁ ⟨g, h⟩ = χHigh ⟨g, hg₂⟩) →
      ∃ θ₂ : H₂ →* ℂˣ, factorsThroughCentralizerDet β θ₂ ∧
        (K : Set G) ⊆ characterNormalizer θ₂ ∧
        (∀ g : D₂, ∃ h : (g : G) ∈ H₂, θ₂ ⟨g, h⟩ = χHigh g) ∧
        characterAgreesOn (H₁ ⊓ H₂) θ₁ θ₂ (fun _ => 1) := by
  dsimp only
  intro hcar₁ hcar₂ hjoin hKH θ₁ χHigh hθ₁ hHighDet hKHigh hagree
  let E := elementAlgebra β
  let : Field E := hf.toField
  let := L.finiteDimensional
  let : FiniteDimensional F E := inferInstanceAs (FiniteDimensional F (elementAlgebra β))
  let ι := relativeEndUnits (F := F) (V := V) E
  let H₁ := simpleHGroup L n₁ β tail₁ (m₁ + 1)
  let H₂ := simpleHGroup M n₂ β tail₂ (m₂ + 1)
  let D₁ := simpleHGroup L n₁ β tail₁ (j₁ + 1)
  let D₂ := simpleHGroup M n₂ β tail₂ (j₂ + 1)
  let U₂ := relativeUnitFiltration M β (m₂ + 1)
  let K := relativeOrderNormalizer M β
  change H₂ = U₂ ⊔ D₂ at hjoin
  have hU₂H₂ : U₂ ≤ H₂ := hjoin.symm ▸ le_sup_left
  have hD₂H₂ : D₂ ≤ H₂ := hjoin.symm ▸ le_sup_right
  have hj' : j₁ / (L.period / subfieldRamificationIndex F E) =
      j₂ / (M.period / subfieldRamificationIndex F E) := by
    simpa only [elementRamificationIndex, hf, dite_true] using hj
  obtain ⟨χU, hχUdet, hrel⟩ :=
    exists_relativeCharacter_of_equal_normalized_depth L M n₁ β tail₁ m₁ m₂ hf hL hM hm θ₁ hθ₁
  have hR : ι.range = centralizerUnitGroup β := relativeEndUnits_range_eq_centralizer β hf
  have hU₂K : U₂ ≤ K := fun _ hu => ⟨hu.1, ((normalizer F V M).1 (m₂ + 1)).1 hu.2⟩
  have hU₂D₂ : U₂ ≤ Subgroup.normalizer (D₂ : Set G) := fun _ hu => (hKHigh (hU₂K hu)).1
  have hDU (u : U₂) (v : D₂) (h : (u : G)⁻¹ * (v : G) * u ∈ D₂) : χHigh ⟨_, h⟩ = χHigh v := by
    exact (hKHigh (K.inv_mem (hU₂K u.2))).2 v (by simpa only [inv_inv] using h)
  have hcompat (g : G) (hU : g ∈ U₂) (hD : g ∈ D₂) : χU ⟨g, hU⟩ = χHigh ⟨g, hD⟩ := by
    obtain ⟨y, rfl⟩ := (hR.symm ▸ hU.1 : g ∈ ι.range)
    have hy := simpleHGroup_le_unitFiltration M n₂ β tail₂ (j₂ + 1) hD
    obtain ⟨x, hx, hdet⟩ := exists_relative_unit_in_inf_with_det L M hL hM j₁ j₂ hj' hy
    have hxC : ι x ∈ centralizerUnitGroup β := hR ▸ ⟨x, rfl⟩
    have hx₁ : ι x ∈ D₁ := relativeUnitFiltration_le_simpleHGroup L n₁ β tail₁ _ ⟨hxC, hx.1⟩
    have hx₂ : ι x ∈ D₂ := relativeUnitFiltration_le_simpleHGroup M n₂ β tail₂ _ ⟨hxC, hx.2⟩
    obtain ⟨hxH, heq⟩ := hagree (ι x) hx₁ hx₂
    calc χU ⟨ι y, hU⟩ = θ₁ ⟨ι x, hxH⟩ := (hrel x y hxH hU hdet).symm
      _ = χHigh ⟨ι x, hx₂⟩ := heq
      _ = χHigh ⟨ι y, hD⟩ := factorsThroughCentralizerDet_apply_eq hHighDet hf x y hx₂ hD hdet
  obtain ⟨χ, hχU, hχD⟩ := exists_monoidHom_of_compatible_restrictions U₂ D₂ χU χHigh hU₂D₂ hDU hcompat
  let θ₂ : H₂ →* ℂˣ := χ.comp (MulEquiv.subgroupCongr hjoin).toMonoidHom
  have hθ₂U (u : U₂) : θ₂ ⟨u, hU₂H₂ u.2⟩ = χU u := hχU u
  have hθ₂D (v : D₂) : θ₂ ⟨v, hD₂H₂ v.2⟩ = χHigh v := hχD v
  refine ⟨θ₂, factorsThroughCentralizerDet_of_restriction M n₂ β tail₂ _ χU θ₂ hχUdet hθ₂U,
    ?_, fun v => ⟨hD₂H₂ v.2, hθ₂D v⟩, ?_⟩
  · intro k hk
    refine ⟨hKH hk, ?_⟩
    intro g hg
    have hg' : (g : G) ∈ (H₂ : Set G) := g.2
    rw [hjoin, Subgroup.coe_mul_of_left_le_normalizer_right U₂ D₂ hU₂D₂] at hg'
    obtain ⟨u, hu, v, hv, hprod⟩ := hg'
    have hu' : k * u * k⁻¹ ∈ U₂ := (Subgroup.mem_normalizer_iff.mp
      (relativeOrderNormalizer_le_normalizer_relativeUnitFiltration M β _ hk) u).mp hu
    have hv' : k * v * k⁻¹ ∈ D₂ := (Subgroup.mem_normalizer_iff.mp (hKHigh hk).1 v).mp hv
    have hgu : (⟨k * (g : G) * k⁻¹, hg⟩ : H₂) =
        ⟨k * u * k⁻¹, hU₂H₂ hu'⟩ * ⟨k * v * k⁻¹, hD₂H₂ hv'⟩ := by
      apply Subtype.ext
      change k * (g : G) * k⁻¹ = (k * u * k⁻¹) * (k * v * k⁻¹)
      rw [← hprod]
      group
    have hgprod : g = (⟨u, hU₂H₂ hu⟩ : H₂) * ⟨v, hD₂H₂ hv⟩ := Subtype.ext hprod.symm
    calc θ₂ ⟨_, hg⟩ = χU ⟨k * u * k⁻¹, hu'⟩ * χHigh ⟨k * v * k⁻¹, hv'⟩ := by
          rw [hgu, map_mul, hθ₂U ⟨_, hu'⟩, hθ₂D ⟨_, hv'⟩]
      _ = χU ⟨u, hu⟩ * χHigh ⟨v, hv⟩ := by
          rw [factorsThroughCentralizerDet_conj_eq hχUdet hf hk.1 (x := ⟨u, hu⟩) hu' hu.1,
            (hKHigh hk).2 ⟨v, hv⟩ hv']
      _ = θ₂ g := by rw [hgprod, map_mul, hθ₂U ⟨_, hu⟩, hθ₂D ⟨_, hv⟩]
  · apply (characterAgreesOn_inf_iff _ _).mpr
    intro g hg₁ hg₂
    obtain ⟨u, ⟨hu₁, hu₂⟩, v, ⟨hv₁, hv₂⟩, rfl⟩ := exists_simpleHGroup_inf_factorization L M
      n₁ n₂ β tail₁ tail₂ (m₁ + 1) (m₂ + 1) (by omega) (by omega) hf hL hM hcar₁ hcar₂ hg₁ hg₂
    have hv₁' : v ∈ D₁ := by
      change v ∈ simpleHGroup L n₁ β tail₁ (j₁ + 1)
      rw [hc₁]
      exact hv₁
    have hv₂' : v ∈ D₂ := by
      change v ∈ simpleHGroup M n₂ β tail₂ (j₂ + 1)
      rw [hc₂]
      exact hv₂
    obtain ⟨hv₁H, hv⟩ := hagree v hv₁' hv₂'
    have hu₁H := relativeUnitFiltration_le_simpleHGroup L n₁ β tail₁ (m₁ + 1) hu₁
    have hu : θ₁ ⟨u, hu₁H⟩ = χU ⟨u, hu₂⟩ := by
      obtain ⟨y, rfl⟩ := (hR.symm ▸ hu₂.1 : u ∈ ι.range)
      exact hrel y y hu₁H hu₂ rfl
    change θ₁ (⟨u, hu₁H⟩ * ⟨v, hv₁H⟩) = θ₂ (⟨u, hU₂H₂ hu₂⟩ * ⟨v, hD₂H₂ hv₂'⟩)
    rw [map_mul, map_mul, hu, hv, hθ₂U ⟨u, hu₂⟩, hθ₂D ⟨v, hv₂'⟩]

end Langlands.BushnellKutzko

import Langlands.BushnellKutzko.SimpleCharacterExtension
import Langlands.BushnellKutzko.SimpleCharacterRestrictionHigh
import Langlands.BushnellKutzko.NormalizerProof
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesStatement
import Langlands.BushnellKutzko.StratumEquivalenceCritical

/-! # Restriction and its fibres at and below the critical cutoff -/

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

noncomputable section

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem terminal_subgroup_at_cutoff (L : LatticeChain 𝒪[F] F V) (n : ℤ)
    (hn : 0 ≤ n) (β : A) (hdepth : finiteCriticalDepth L n β = n) :
    simpleHGroup L n β [] ((n / 2).toNat + 1) = L.unitFiltration (simpleHCutoff n).toNat := by
  have h : (n / 2).toNat + 1 = (simpleHCutoff n).toNat := by unfold simpleHCutoff; omega
  conv => rhs; rw [← h]
  exact simpleHGroup_eq_unitFiltration_of_cutoffs L n _ (by unfold simpleHCutoff; omega) β []
    (by intro x hx; simp at hx; subst x; rw [hdepth])

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem subgroup_product_at_intermediate {U H D D' : Subgroup G} (hD : D ≤ D')
    (hH : D' ≤ H) (hprod : (H : Set G) = (U : Set G) * (D : Set G)) :
    U ≤ H ∧ (H : Set G) = (U : Set G) * (D' : Set G) := by
  have hU : U ≤ H := by
    intro g hg
    change g ∈ (H : Set G)
    rw [hprod]
    exact Set.mem_mul.mpr ⟨g, hg, 1, D.one_mem, mul_one _⟩
  refine ⟨hU, Set.Subset.antisymm (fun g hg => ?_) (fun g hg => ?_)⟩
  · rw [hprod] at hg
    obtain ⟨u, hu, d, hd, rfl⟩ := Set.mem_mul.mp hg
    exact Set.mem_mul.mpr ⟨u, hu, d, hD hd, rfl⟩
  · obtain ⟨u, hu, d, hd, rfl⟩ := Set.mem_mul.mp hg
    exact H.mul_mem (hU hu) (hH hd)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem mul_relativeUnits_eq_of_product (L : LatticeChain 𝒪[F] F V) (β : A)
    {H D : Subgroup G} {i : ℕ} (hH : H ≤ L.unitFiltration i)
    (hprod : (H : Set G) = (relativeUnitFiltration L β i : Set G) * (D : Set G)) :
    (H : Set G) = ((H ⊓ centralizerUnitGroup β : Subgroup G) : Set G) * (D : Set G) := by
  have hU := (subgroup_product_at_intermediate le_rfl
    (show D ≤ H from by
      intro x hx
      change x ∈ (H : Set G)
      rw [hprod]
      exact Set.mem_mul.mpr ⟨1, (relativeUnitFiltration L β i).one_mem, x, hx, one_mul _⟩)
    hprod).1
  have he : relativeUnitFiltration L β i = H ⊓ centralizerUnitGroup β := by
    exact le_antisymm (le_inf hU inf_le_left) (le_inf inf_le_right (inf_le_left.trans hH))
  rwa [he] at hprod

/-- For two indices at or below the cutoff the restriction is onto. Its fibres are translates
of the characters trivial at the larger index and factoring through the determinant. -/
theorem simpleCharacters_restrict_low_of_products (ψF : AddChar F ℂ)
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (hn : 0 ≤ n) (β : A) (tail : List A) {m j : ℕ}
    (hmj : m ≤ j) :
    let H := fun i : ℕ => simpleHGroup L n β tail (i + 1)
    let C := simpleCharacters ψF L n β tail
    let K := relativeOrderNormalizer L β
    let r := finiteCriticalDepth L n β
    let d := (r / 2).toNat
    j ≤ d → (d : ℤ) < r → (tail = [] → r = n) →
    (∀ i, K ≤ Subgroup.normalizer (H i : Set G)) →
    (∀ i ≤ d, (H i : Set G) = (relativeUnitFiltration L β (i + 1) : Set G) * (H d : Set G)) →
    let res := fun χ : H m →* ℂˣ => χ.comp (Subgroup.inclusion
      (simpleHGroup_antitone L n β tail (Nat.succ_le_succ hmj)))
    let X : Set (H m →* ℂˣ) := {χ | res χ = 1 ∧ factorsThroughCentralizerDet β χ}
    res '' C m = C j ∧ ∀ θ ∈ C m, {χ ∈ C m | res χ = res θ} = (fun χ => θ * χ) '' X := by
  intro H C K r d hj hrd hterm hnorm hprod res X
  have hle {i i' : ℕ} (hi : i ≤ i') : H i' ≤ H i :=
    simpleHGroup_antitone L n β tail (Nat.succ_le_succ hi)
  have hjr : (j : ℤ) < r := by omega
  have hmr : (m : ℤ) < r := by omega
  have hprod' (i i' : ℕ) (hi : i ≤ i') (hi' : i' ≤ d) :
      (H i : Set G) = ((H i ⊓ centralizerUnitGroup β : Subgroup G) : Set G) * (H i' : Set G) :=
    mul_relativeUnits_eq_of_product L β (simpleHGroup_le_unitFiltration L n β tail (i + 1))
      (subgroup_product_at_intermediate (hle hi') (hle hi) (hprod i (hi.trans hi'))).2
  have hK : K ≤ centralizerUnitGroup β := inf_le_left
  have hUK : H m ⊓ centralizerUnitGroup β ≤ K := by
    intro g hg
    refine ⟨hg.2, ?_⟩
    exact ((normalizer F V L).1 (m + 1)).1
      (simpleHGroup_le_unitFiltration L n β tail (m + 1) hg.1)
  have hfactor {i : ℕ} (hi : (i : ℤ) < r) {θ : H i →* ℂˣ} (hθ : θ ∈ C i) :
      factorsThroughCentralizerDet β θ := by
    cases tail with
    | nil =>
      change θ ∈ simpleCharacters ψF L n β [] i at hθ
      rw [simpleCharacters] at hθ
      exact hθ.2
    | cons γ rest =>
      change θ ∈ simpleCharacters ψF L n β (γ :: rest) i at hθ
      change (i : ℤ) < finiteCriticalDepth L n β at hi
      simp only [simpleCharacters, ite_eq_left hi] at hθ
      exact hθ.1
  have hrestrict {θ : H m →* ℂˣ} (hθ : θ ∈ C m) : res θ ∈ C j := by
    cases tail with
    | nil => exact simpleCharacters_restrict_nil L ψF n β hmj hθ
    | cons γ rest =>
      exact simpleCharacters_restrict_cons_of_le_cutoff L ψF n β γ rest hmj hj hjr (hnorm j) hθ
  have hC' (θ : H j →* ℂˣ) (hθ : θ ∈ C j) :
      factorsThroughCentralizerDet β θ ∧ (K : Set G) ⊆ characterNormalizer θ := by
    have hdet := hfactor hjr hθ
    refine ⟨hdet, ?_⟩
    cases tail with
    | nil =>
      have hh : H d = L.unitFiltration (simpleHCutoff n).toNat := by
        have hd : d = (n / 2).toNat := congrArg (fun t : ℤ => (t / 2).toNat) (hterm rfl)
        simpa only [hd] using terminal_subgroup_at_cutoff L n hn β (hterm rfl)
      apply relativeDet_character_normalized_of_product (hle hj) (hprod' j d hj le_rfl)
        hK (hnorm j) hdet
      refine characterNormalizer_of_trace_values ψF hK (hnorm d) (fun g => ?_)
      change θ ∈ simpleCharacters ψF L n β [] j at hθ
      rw [simpleCharacters] at hθ
      exact hθ.1 _ (hh ▸ g.prop)
    | cons γ rest =>
      change θ ∈ simpleCharacters ψF L n β (γ :: rest) j at hθ
      change (j : ℤ) < finiteCriticalDepth L n β at hjr
      simp only [simpleCharacters, ite_eq_left hjr] at hθ
      exact hθ.2.1
  change res '' C m = C j ∧ ∀ θ ∈ C m, {χ ∈ C m | res χ = res θ} = (fun χ => θ * χ) '' X
  refine image_fibres_of_relativeDet_extension (hle hmj) (hprod' m j hmj hj) hUK (C m) (C j)
    (fun χ => ⟨fun h => ⟨hfactor hmr h, hrestrict h⟩, fun ⟨hχ, hχ'⟩ => ?_⟩) hC'
  have hχnorm := relativeDet_character_normalized_of_product (hle hmj) (hprod' m j hmj hj)
    hK (hnorm m) hχ (hC' _ hχ').2
  cases tail with
  | nil =>
    have hh : H d = L.unitFiltration (simpleHCutoff n).toNat := by
      have hd : d = (n / 2).toNat := congrArg (fun t : ℤ => (t / 2).toNat) (hterm rfl)
      simpa only [hd] using terminal_subgroup_at_cutoff L n hn β (hterm rfl)
    change res χ ∈ simpleCharacters ψF L n β [] j at hχ'
    change χ ∈ simpleCharacters ψF L n β [] m
    rw [simpleCharacters] at hχ' ⊢
    exact ⟨fun g hg => hχ'.1 ⟨g, hle hj (hh.symm ▸ hg)⟩ hg, hχ⟩
  | cons γ rest =>
    change res χ ∈ simpleCharacters ψF L n β (γ :: rest) j at hχ'
    change χ ∈ simpleCharacters ψF L n β (γ :: rest) m
    change (j : ℤ) < finiteCriticalDepth L n β at hjr
    change (m : ℤ) < finiteCriticalDepth L n β at hmr
    simp only [simpleCharacters, ite_eq_left hjr, ite_eq_left hmr] at hχ' ⊢
    rw [max_eq_right hj] at hχ'
    rw [max_eq_right (hmj.trans hj)]
    obtain ⟨_, _, θ₀, hθ₀, ha⟩ := hχ'
    refine ⟨hχ, hχnorm, θ₀, hθ₀, fun g => ?_⟩
    obtain ⟨hg, hg₀, hv⟩ := ha g
    exact ⟨hle hmj hg, hg₀, hv⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- At level zero the finite critical depth is positive, including the scalar fallback. -/
theorem finiteCriticalDepth_pos_of_simple {S : Stratum 𝒪[F] F V} (h0 : S.r = 0)
    (hS : S.IsSimple) : 0 < finiteCriticalDepth S.chain S.n S.b := by
  have hn := S.r_lt_n
  rw [h0] at hn
  have hcrit := hS.2
  rw [h0, neg_zero] at hcrit
  rcases he : criticalExponent S.chain S.b with _ | k
  · simpa [finiteCriticalDepth, simpleCriticalDepth, he] using hn
  · rw [he] at hcrit
    have hk : k < 0 := WithBot.coe_lt_coe.1 hcrit
    have hk' : criticalExponent S.chain S.b = (k : WithBot ℤ) := he
    rw [finiteCriticalDepth_of_criticalExponent_eq _ _ (-k) _ (by simpa only [neg_neg] using hk')]
    exact neg_pos.mpr hk

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- In the scalar case the defining sequence has no further term. -/
theorem Stratum.DefiningSequenceChoice.tail_eq_nil_of_scalar {S : Stratum 𝒪[F] F V}
    (q : S.DefiningSequenceChoice) (hβ : elementAlgebra S.b = ⊥) : q.tail = [] := by
  have hsteps : q.steps = 0 := by
    by_contra h
    let i : Fin q.steps := ⟨0, Nat.pos_of_ne_zero h⟩
    obtain ⟨_, _, _, _, _, hs, _, _⟩ := q.isDefiningSequence
    have hcrit := (hs i).1
    rw [show i.castSucc = 0 from rfl, q.firstElement, criticalExponent, ite_eq_left hβ] at hcrit
    exact WithBot.bot_ne_coe hcrit
  apply List.eq_nil_of_length_eq_zero
  simpa [Stratum.DefiningSequenceChoice.tail] using hsteps

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem scalar_domains (L : LatticeChain 𝒪[F] F V) (n : ℤ) {β : A}
    (hβ : elementAlgebra β = ⊥) (k : ℕ) :
    simpleHGroup L n β [] k = L.unitFiltration k ∧
      relativeUnitFiltration L β k = L.unitFiltration k := by
  constructor
  · apply le_antisymm (simpleHGroup_le_unitFiltration L n β [] k)
    intro g hg
    refine Subgroup.subset_closure ⟨hg, Submodule.mem_sup_left ?_⟩
    rw [StratumEquivalence.centralizerLattice_zero_of_bot L hβ]
    exact hg.1
  · have hb : β ∈ (⊥ : Subalgebra F A) := hβ ▸ Algebra.self_mem_adjoin_singleton F β
    obtain ⟨a, rfl⟩ := Algebra.mem_bot.mp hb
    refine le_antisymm inf_le_right (fun g hg => ⟨?_, hg⟩)
    exact Algebra.commutes a (g : A)

/-- The relative-unit product and domain normalizers imply the full restriction and fibre
calculation at and below the cutoff of a simple stratum. The product is immediate for a
scalar parameter. -/
theorem simpleCharacterRestriction_low_of_groupProperties
    (hGroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (ψF : AddChar F ℂ) {S : Stratum 𝒪[F] F V} (h0 : S.r = 0) (hS : S.IsSimple)
    (q : S.DefiningSequenceChoice)
    {m j : ℕ} (hmj : m ≤ j) :
    let H := fun i : ℕ => simpleHGroup S.chain S.n S.b q.tail (i + 1)
    let C := simpleCharacters ψF S.chain S.n S.b q.tail
    let d := (finiteCriticalDepth S.chain S.n S.b / 2).toNat
    j ≤ d →
    let res := simpleCharacterRestriction S q hmj
    let X : Set (H m →* ℂˣ) := {χ | res χ = 1 ∧ factorsThroughCentralizerDet S.b χ}
    res '' C m = C j ∧ ∀ θ ∈ C m, {χ ∈ C m | res χ = res θ} = (fun χ => θ * χ) '' X := by
  intro H C d hj res X
  have hn := S.r_lt_n
  rw [h0] at hn
  let r := finiteCriticalDepth S.chain S.n S.b
  have hr : 0 < r := finiteCriticalDepth_pos_of_simple h0 hS
  have hrd : (d : ℤ) < r := by
    change (((r / 2).toNat : ℕ) : ℤ) < r
    omega
  obtain ⟨_, hprod, hnorm, _, _⟩ := hGroups F V S h0 hS q
  have hd : (simpleHCutoff r).toNat = d + 1 := by
    change (simpleHCutoff r).toNat = (r / 2).toNat + 1
    unfold simpleHCutoff
    omega
  have hprod' (i : ℕ) (hi : i ≤ d) :
      (H i : Set G) = (relativeUnitFiltration S.chain S.b (i + 1) : Set G) * (H d : Set G) := by
    by_cases hβ : elementAlgebra S.b = ⊥
    · have hdom := scalar_domains S.chain S.n hβ (i + 1)
      have htail := q.tail_eq_nil_of_scalar hβ
      have hu : relativeUnitFiltration S.chain S.b (i + 1) = H i := by
        simp only [H, htail, hdom.1, hdom.2]
      rw [hu]
      ext g
      constructor
      · intro hg
        exact Set.mem_mul.mpr ⟨g, hg, 1, (H d).one_mem, mul_one g⟩
      · intro hg
        obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hg
        exact (H i).mul_mem ha (simpleHGroup_antitone S.chain S.n S.b q.tail
          (Nat.succ_le_succ hi) hb)
    · have hle : ((i + 1 : ℕ) : ℤ) ≤ simpleHCutoff r := by
        change i ≤ (r / 2).toNat at hi
        unfold simpleHCutoff
        omega
      have hd' : (simpleHCutoff (finiteCriticalDepth S.chain S.n S.b)).toNat = d + 1 := hd
      simpa only [hd', H] using (hprod hβ).1 (i + 1) hle
  exact simpleCharacters_restrict_low_of_products ψF S.chain S.n hn.le S.b q.tail hmj
    hj hrd q.finiteCriticalDepth_of_tail_nil (fun i => (hnorm (i + 1)).1) hprod'

end

end Langlands.BushnellKutzko

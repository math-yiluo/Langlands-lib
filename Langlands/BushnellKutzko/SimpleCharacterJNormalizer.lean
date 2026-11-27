import Langlands.BushnellKutzko.SimpleCharacterCommutatorProof
import Langlands.BushnellKutzko.SimpleCharacterNormalizer

/-! # The subgroup J normalizes a simple character -/

noncomputable section

open ValuativeRel
open scoped Classical Pointwise commutatorElement

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "O" => 𝒪[F]
local notation "A" => Module.End F V
local notation "G" => Aˣ
local notation "H[" S "," q "]" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "J[" S "," q "]" => simpleJGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "C[" ψ "," S "," q "]" => simpleCharacters ψ (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)

/-- At complementary depths the conjugation of a unit does not change the
value of the element character on it. -/
theorem elementCharacter_conj_eq_of_depth (L : LatticeChain O F V) (ψF : AddChar F ℂ)
    (hψ : IsBKAdditiveCharacter ψF) {b : A} {r : ℤ} (hb : b ∈ L.endFiltration (-r))
    {k l : ℕ} (hk : 1 ≤ k) (hdepth : 1 ≤ (k : ℤ) + l - r) {x y : G}
    (hx : x ∈ L.unitFiltration k) (hy : y ∈ L.unitFiltration l) :
    elementCharacter (traceCharacter ψF) b (x * y * x⁻¹) = elementCharacter (traceCharacter ψF) b y := by
  have hmix : x ∈ mixedAdjointUnitGroup L b k (-r) hk := by
    refine ⟨hx.2.2, ?_⟩
    change b * ((x : A) - 1) - ((x : A) - 1) * b ∈ L.endFiltration ((k : ℤ) + -r)
    simpa only [add_comm] using commutator_mem_endFiltration L hb hx.2.2
  have hd := conjugation_sub_mem_of_mem_mixedAdjointUnitGroup hmix
  rw [elementCharacter_conj]
  let d := (↑x⁻¹ : A) * b * (x : A) - b
  have he : (↑x⁻¹ : A) * b * (x : A) = b + d := by dsimp [d]; abel
  rw [he, elementCharacter_add, elementCharacter_eq_one_of_depth L ψF hψ hd (by omega) hy, mul_one]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem mem_characterNormalizerSubgroup_of_factors {H D R : Subgroup G} {θ : H →* ℂˣ}
    (hDH : D ≤ H) (hRH : R ≤ H) (hH : (H : Set G) = (R : Set G) * (D : Set G))
    {x : G} (hx : x ∈ Subgroup.normalizer (H : Set G))
    (hxD : x ∈ characterNormalizerSubgroup (θ.comp (Subgroup.inclusion hDH)))
    (hxR : ∀ u (hu : u ∈ R), ∃ hv : x * u * x⁻¹ ∈ H, θ ⟨_, hv⟩ = θ ⟨u, hRH hu⟩) :
    x ∈ characterNormalizerSubgroup θ := by
  refine ⟨hx, ?_⟩
  intro h hh
  have hmem : (h : G) ∈ (H : Set G) := h.property
  rw [hH] at hmem
  obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.mp hmem
  obtain ⟨hu', hval⟩ := hxR u hu
  have hv' := (Subgroup.mem_normalizer_iff.mp hxD.1 v).mp hv
  have hvval := hxD.2 ⟨v, hv⟩ hv'
  change θ ⟨x * v * x⁻¹, hDH hv'⟩ = θ ⟨v, hDH hv⟩ at hvval
  have heq : (⟨_, hh⟩ : H) = ⟨_, hu'⟩ * ⟨_, hDH hv'⟩ := by
    apply Subtype.ext
    change x * (h : G) * x⁻¹ = (x * u * x⁻¹) * (x * v * x⁻¹)
    rw [← huv]
    group
  have heq' : h = ⟨u, hRH hu⟩ * ⟨v, hDH hv⟩ := Subtype.ext huv.symm
  rw [heq, map_mul, hval, hvval, heq', map_mul]

/-- The whole subgroup `J` preserves the domain and values of a simple
character, as in BK93 (3.3.1). -/
theorem simpleJ_le_characterNormalizerSubgroup
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    (m : ℕ) (hmn : (m : ℤ) < S.n) (hmc : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {θ : H[S,q] (m + 1) →* ℂˣ} (hθ : θ ∈ C[ψF,S,q] m) :
    J[S,q] 0 ≤ characterNormalizerSubgroup θ := by
  have bounded (d : ℕ) : ∀ (S : Stratum O F V), S.r = 0 → S.IsSimple → ∀ (q : S.DefiningSequenceChoice),
      q.steps < d → ∀ (m : ℕ), (m : ℤ) < S.n →
      ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b → ∀ θ ∈ C[ψF,S,q] m,
      J[S,q] 0 ≤ characterNormalizerSubgroup θ := by
    induction d with
    | zero =>
      intro S hS0 hS q hq
      omega
    | succ d ih =>
      intro S hS0 hS q hq m hmn hmc θ hθ
      by_cases hb : elementAlgebra S.b = ⊥
      · have hN := (simpleCharacterIntertwining_of_scalar ψF S q hb m hθ).2
        simp only [simpleCharacterIntertwiningFactor, ite_eq_left hb] at hN
        intro x hx
        change x ∈ characterNormalizer θ
        rw [hN]
        have hu : Commute S.b (x : A) := by
          have hb' : S.b ∈ (⊥ : Subalgebra F A) := hb ▸ Algebra.self_mem_adjoin_singleton F S.b
          obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hb'
          rw [← ha]
          exact Algebra.commutes a _
        exact Set.mem_mul.mpr ⟨1, rfl, x, relativeUnitFiltration_le_relativeOrderNormalizer S.chain S.b 0
          ⟨hu, simpleJGroup_le_unitFiltration _ _ _ _ _ hx⟩, one_mul x⟩
      · obtain ⟨r, hr, hrn, hcrit⟩ := criticalDepth_of_simple S hS0 hS q hb
        have hdepth := finiteCriticalDepth_of_criticalExponent_eq S.chain S.n (r : ℤ) S.b hcrit
        rw [SimpleStratumLattice.simpleCriticalDepth_eq _ hcrit, WithTop.coe_lt_coe] at hmc
        have hmr : m < r := by exact_mod_cast hmc
        let j := (r + 1) / 2
        have hj : 1 ≤ j := by dsimp [j]; omega
        have hgroup := simpleStratumGroupProperties F V S hS0 hS q
        have high (i : ℕ) (hi : r / 2 ≤ i) (hir : i < r) {χ : H[S,q] (i + 1) →* ℂˣ}
            (hχ : χ ∈ C[ψF,S,q] i) : J[S,q] j ≤ characterNormalizerSubgroup χ := by
          intro x hx
          have hxH : x ∈ Subgroup.normalizer (H[S,q] (i + 1) : Set G) :=
            (hgroup.2.2.2.1 i).2.2 (simpleJGroup_antitone _ _ _ _ (Nat.zero_le _) hx)
          have hxU : x ∈ S.chain.unitFiltration j := simpleJGroup_le_unitFiltration _ _ _ _ _ hx
          refine ⟨hxH, ?_⟩
          intro u hu
          have huU := simpleHGroup_le_unitFiltration S.chain S.n S.b q.tail (i + 1) u.prop
          have hsum : 1 ≤ (j : ℤ) + ((i + 1 : ℕ) : ℤ) - (r : ℤ) := by dsimp [j]; omega
          by_cases hq0 : q.steps = 0
          · have hn' : S.n = r := level_eq_of_terminal_of_criticalExponent_eq q hq0 hcrit
            have hi' : S.n / 2 ≤ (i : ℤ) := by rw [hn']; omega
            have hv := simpleCharacters_high_values ψF hψ q hi' hχ
            have hbP := (SimpleStratumLattice.parameter_of_pure S.chain hS.1 rfl).mem
            rw [hn'] at hbP
            apply Units.ext
            rw [hv ⟨_, hu⟩, hv u]
            exact elementCharacter_conj_eq_of_depth S.chain ψF hψ hbP hj hsum hxU huU
          · obtain ⟨T, q', s, hL, hN, hT0, hT, _, hs, hcr, hδ, htail, hlt, hH, hJ⟩ :=
              exists_simpleCharacterSuffix S hS0 hS q (Nat.pos_of_ne_zero hq0)
            have hrs : r = s := by
              exact_mod_cast neg_injective (WithBot.coe_injective (hcrit.symm.trans hs))
            subst s
            rcases T with ⟨L', n', t', c, hlt', hval'⟩
            change L' = S.chain at hL
            change n' = S.n at hN
            change t' = 0 at hT0
            subst L' n' t'
            let T : Stratum O F V := ⟨S.chain, S.n, 0, c, hlt', hval'⟩
            have hiC : (i : ℤ) < finiteCriticalDepth S.chain S.n S.b := by rw [hdepth]; omega
            have hfhalf : (finiteCriticalDepth S.chain S.n S.b / 2).toNat = r / 2 := by rw [hdepth]; omega
            have hxJ₀ : x ∈ J[T,q'] 0 := simpleJGroup_antitone _ _ _ _ (Nat.zero_le j) ((hJ j le_rfl).le hx)
            clear huU
            revert u
            generalize htt : q.tail = tail at χ hχ ⊢
            have ht' : tail = c :: q'.tail := htt.symm.trans htail
            clear htt
            subst tail
            simp only [simpleCharacters, ite_eq_left hiC] at hχ
            rw [hfhalf, max_eq_left hi] at hχ
            obtain ⟨_, _, χ₀, hχ₀, htwist⟩ := hχ
            have hi' : ((i : ℤ) : WithTop ℤ) < simpleCriticalDepth T.chain T.b :=
              simpleCriticalDepth_gt_of_criticalExponent_lt (L := S.chain) (β := c)
                (hcr.trans_le (WithBot.coe_le_coe.mpr (by omega)))
            have hNx := ih T rfl hT q' (by omega) i (by change (i : ℤ) < S.n; omega) hi' χ₀ hχ₀ hxJ₀
            intro u hu
            have huU := simpleHGroup_le_unitFiltration S.chain S.n S.b (c :: q'.tail) (i + 1) u.prop
            obtain ⟨_, hu₀, hv₀⟩ := htwist u
            obtain ⟨_, hxu₀, hv₁⟩ := htwist ⟨_, hu⟩
            apply Units.ext
            rw [hv₁, hv₀, hNx.2 ⟨u, hu₀⟩ hxu₀]
            exact congrArg ((χ₀ ⟨u, hu₀⟩ : ℂ) * ·)
              (elementCharacter_conj_eq_of_depth S.chain ψF hψ hδ hj hsum hxU huU)
        have hmC : (m : ℤ) < finiteCriticalDepth S.chain S.n S.b := by rw [hdepth]; omega
        obtain ⟨_, hK⟩ := character_determinant_normalizer_finite S.chain S.n ψF S.b q.tail m hmC hθ
        have hJ : J[S,q] j ≤ characterNormalizerSubgroup θ := by
          rcases le_or_gt (r / 2) m with hm | hm
          · exact high m hm hmr hθ
          · let D := H[S,q] (r / 2 + 1)
            let R := relativeUnitFiltration S.chain S.b (m + 1)
            have hD : D ≤ H[S,q] (m + 1) := simpleHGroup_antitone _ _ _ _ (by omega)
            have hR : R ≤ H[S,q] (m + 1) := relativeUnitFiltration_le_simpleHGroup _ _ _ _ _
            have hcut : simpleHCutoff (finiteCriticalDepth S.chain S.n S.b) = ((r / 2 + 1 : ℕ) : ℤ) := by
              rw [hdepth]; unfold simpleHCutoff; omega
            have hprod := (hgroup.2.1 hb).1 (m + 1) (by rw [hcut]; omega)
            rw [hcut, Int.toNat_natCast] at hprod
            have hcutC : (((r / 2 : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b := by
              rw [SimpleStratumLattice.simpleCriticalDepth_eq _ hcrit, WithTop.coe_lt_coe]
              omega
            have hχ := simpleCharacters_restrict_forward ψF S hS0 hS q hm.le (by omega) hcutC hθ
            have hcomm := simpleCharacterCommutatorAt ψF hψ S hS0 hS q hcrit le_rfl (by omega) hχ
            intro x hx
            have hxH : x ∈ Subgroup.normalizer (H[S,q] (m + 1) : Set G) :=
              (hgroup.2.2.2.1 m).2.2 (simpleJGroup_antitone _ _ _ _ (Nat.zero_le _) hx)
            refine mem_characterNormalizerSubgroup_of_factors hD hR hprod hxH (high _ le_rfl (by omega) hχ hx) ?_
            intro u hu
            obtain ⟨hc, hval⟩ := hcomm.mixedJ (show 1 ≤ m + 1 by omega) hj (by dsimp [j]; omega)
              (by dsimp [j]; omega) (relativeUnitFiltration_sub_one_mem_mixed S.chain S.b (by omega) _ hu) hx
            have he : (↑u⁻¹ : A) * S.b * (u : A) - S.b = 0 := by
              have h : S.b * (u : A) = (u : A) * S.b := hu.1
              rw [mul_assoc, h, ← mul_assoc, Units.inv_mul, one_mul, sub_self]
            rw [he, elementCharacter_apply, zero_mul, AddChar.map_zero_eq_one] at hval
            have hcθ : θ ⟨_, hD hc⟩ = 1 := Units.ext hval
            have hv : ⁅x, u⁆ = ⁅u, x⁆⁻¹ := by rw [commutatorElement_def, commutatorElement_def]; group
            have hxv : x * u * x⁻¹ = ⁅u, x⁆⁻¹ * u := by rw [← hv, commutatorElement_def]; group
            let y : H[S,q] (m + 1) := (⟨_, hD hc⟩ : H[S,q] (m + 1))⁻¹ * ⟨u, hR hu⟩
            have hy : (y : G) = x * u * x⁻¹ := hxv.symm
            refine ⟨hy ▸ y.prop, ?_⟩
            rw [show (⟨_, hy ▸ y.prop⟩ : H[S,q] (m + 1)) = y from Subtype.ext hy.symm]
            simp only [y, map_mul, map_inv, hcθ, inv_one, one_mul]
        have hjcut : simpleJCutoff (finiteCriticalDepth S.chain S.n S.b) = (j : ℤ) := by
          rw [hdepth]; unfold simpleJCutoff j; omega
        have hdecomp := (hgroup.2.1 hb).2 0 (by rw [hjcut]; omega)
        rw [hjcut, Int.toNat_natCast] at hdecomp
        intro x hx
        have hx' : x ∈ (J[S,q] 0 : Set G) := hx
        rw [hdecomp] at hx'
        obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hx'
        exact (characterNormalizerSubgroup θ).mul_mem
          (hK (relativeUnitFiltration_le_relativeOrderNormalizer S.chain S.b 0 hu)) (hJ hv)
  exact bounded (q.steps + 1) S hS0 hS q (by omega) m hmn hmc θ hθ

end Langlands.BushnellKutzko

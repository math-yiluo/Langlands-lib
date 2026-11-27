import Langlands.BushnellKutzko.SimpleCharacterCommutatorAlgebra
import Langlands.BushnellKutzko.SimpleCharacterPairingEvaluation
import Langlands.BushnellKutzko.SimpleCharacterCentralizer
import Langlands.BushnellKutzko.SimpleCharacterRestrictionCutoff
import Langlands.BushnellKutzko.SimpleCharacterRestrictionHigh

/-! # Centralizer units acting on simple characters -/

open ValuativeRel
open scoped commutatorElement Pointwise

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => Aˣ
local notation "O" => 𝒪[F]
local notation "H[" s "," q "]" => simpleHGroup (Stratum.chain s) (Stratum.n s) (Stratum.b s)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "J[" s "," q "]" => simpleJGroup (Stratum.chain s) (Stratum.n s) (Stratum.b s)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "R[" s "]" => relativeUnitFiltration (Stratum.chain s) (Stratum.b s)
local notation "K[" s "]" => relativeOrderNormalizer (Stratum.chain s) (Stratum.b s)
local notation "depth[" s "]" => finiteCriticalDepth (Stratum.chain s) (Stratum.n s) (Stratum.b s)
local notation "jcut[" s "]" => Int.toNat (simpleJCutoff depth[s])
local notation "hcut[" s "]" => Int.toNat (simpleHCutoff depth[s])
local notation "C[" ps "," s "," q "]" => simpleCharacters ps (Stratum.chain s) (Stratum.n s)
  (Stratum.b s) (Stratum.DefiningSequenceChoice.tail q)

/-- The mixed `J` commutator calculation of BK93 (3.2.8) specialized to a
supplied defining sequence and a finite critical depth. -/
def SimpleCharacterMixedJCommutator : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψ : AddChar F ℂ), IsBKAdditiveCharacter ψ →
    ∀ (S : Stratum 𝒪[F] F V), S.r = 0 → S.IsSimple → ∀ q : S.DefiningSequenceChoice,
      ∀ r i k l : ℕ, criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ) →
      r / 2 ≤ i → i < r → 1 ≤ k → 1 ≤ l → i + 1 ≤ k + l → r + 1 ≤ k + 2*l →
      ∀ θ ∈ C[ψ,S,q] i, ∀ x y : (Module.End F V)ˣ,
        (x : Module.End F V) - 1 ∈ mixedAdjointLattice S.chain S.b k (-(r : ℤ)) →
        y ∈ J[S,q] l → ∃ hc : ⁅x,y⁆ ∈ H[S,q] (i+1),
          (θ ⟨_, hc⟩ : ℂ) =
            elementCharacter (traceCharacter ψ) ((↑x⁻¹ : Module.End F V) * S.b * (x : Module.End F V) - S.b) y

namespace SimpleStratum

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem simple_character_det (ψ : AddChar F ℂ) (L : LatticeChain O F V)
    (n : ℤ) (b : A) (tail : List A) (i : ℕ) (hi : (i : ℤ) < finiteCriticalDepth L n b)
    {θ : simpleHGroup L n b tail (i+1) →* ℂˣ} (hθ : θ ∈ simpleCharacters ψ L n b tail i) :
    factorsThroughCentralizerDet b θ := by
  cases tail with
  | nil => exact hθ.2
  | cons c tail =>
    simp only [simpleCharacters, ite_eq_left hi, Set.mem_ofPred_eq] at hθ
    exact hθ.1

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem simple_character_normalizer_of_cons (ψ : AddChar F ℂ) (L : LatticeChain O F V)
    (n : ℤ) (b : A) (tail : List A) (i : ℕ) (hne : tail ≠ []) (hi : (i : ℤ) < finiteCriticalDepth L n b)
    {θ : simpleHGroup L n b tail (i+1) →* ℂˣ} (hθ : θ ∈ simpleCharacters ψ L n b tail i) :
    (relativeOrderNormalizer L b : Set G) ⊆ characterNormalizer θ := by
  cases tail with
  | nil => exact (hne rfl).elim
  | cons c tail =>
    simp only [simpleCharacters, ite_eq_left hi, Set.mem_ofPred_eq] at hθ
    exact hθ.2.1

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem simple_character_trace_of_nil (ψ : AddChar F ℂ) (L : LatticeChain O F V)
    (n : ℤ) (b : A) (tail : List A) (i : ℕ) (hzero : tail = [])
    {θ : simpleHGroup L n b tail (i+1) →* ℂˣ} (hθ : θ ∈ simpleCharacters ψ L n b tail i)
    (x : simpleHGroup L n b tail (i+1)) (hx : (x : G) ∈ L.unitFiltration (simpleHCutoff n).toNat) :
    (θ x : ℂ) = elementCharacter (traceCharacter ψ) b x := by
  subst tail
  exact hθ.1 x hx

private theorem relativeUnit_normalizes_of_terminal (hG : SimpleStratumGroupPropertiesStatement.{uF,uV})
    (ψ : AddChar F ℂ) (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple)
    (q : S.DefiningSequenceChoice) (hzero : q.steps = 0)
    (i : ℕ) (hi : (i : ℤ) < depth[S]) {θ : H[S,q] (i+1) →* ℂˣ} (hθ : θ ∈ C[ψ,S,q] i)
    {g : G} (hg : g ∈ K[S]) : g ∈ characterNormalizer θ := by
  have htail := (tail_nil_iff S q).mpr hzero
  have hdn := terminal_depth S q hzero
  have hNorm := ((hG F V S hS0 hS q).2.2.1 (i+1)).1 hg
  refine ⟨hNorm, ?_⟩
  intro x hx
  have hDet := simple_character_det ψ S.chain S.n S.b q.tail i hi hθ
  let t := (simpleHCutoff S.n).toNat
  have evalHigh (z : H[S,q] (i+1)) (hz : (z : G) ∈ S.chain.unitFiltration t)
      (hgz : g * (z : G) * g⁻¹ ∈ H[S,q] (i+1)) : θ ⟨_, hgz⟩ = θ z := by
    have hgn : g ∈ Subgroup.normalizer (S.chain.unitFiltration t : Set G) := by
      rw [(normalizer F V S.chain).2.2.1 t]
      exact hg.2
    have hgzU := (Subgroup.mem_normalizer_iff.mp hgn _).mp hz
    apply Units.ext
    rw [simple_character_trace_of_nil ψ S.chain S.n S.b q.tail i htail hθ ⟨_, hgz⟩ hgzU,
      simple_character_trace_of_nil ψ S.chain S.n S.b q.tail i htail hθ z hz]
    exact elementCharacter_conj_of_centralizer ψ hg.1 z
  by_cases hxh : (x : G) ∈ S.chain.unitFiltration t
  · exact evalHigh x hxh hx
  have hlev : i + 1 ≤ t := by
    by_contra! h
    apply hxh
    exact S.chain.unitFiltration_antitone h.le (simpleHGroup_le_unitFiltration S.chain S.n S.b
      q.tail (i+1) x.property)
  by_cases hs : elementAlgebra S.b = ⊥
  · have hx0 := simpleHGroup_le_unitFiltration S.chain S.n S.b q.tail (i+1) x.property
    have hxC : ((x : G) : A) ∈ centralizerLattice S.chain S.b 0 := by
      rw [StratumEquivalence.centralizerLattice_zero_of_bot S.chain hs]
      exact S.chain.mem_order_iff_mem_endFiltration.mp hx0.1
    exact hDet.conj_eq hg.1 x (sub_eq_zero.mp hxC.2) hx
  have hle : ((i + 1 : ℕ) : ℤ) ≤ simpleHCutoff depth[S] := by
    have hni : 0 < S.n := hS0 ▸ S.r_lt_n
    have ht : (t : ℤ) = simpleHCutoff S.n := Int.toNat_of_nonneg (by unfold simpleHCutoff; omega)
    rw [hdn, ← ht]
    exact_mod_cast hlev
  have hprod := ((hG F V S hS0 hS q).2.1 hs).1 (i+1) hle
  rw [hdn] at hprod
  have hxprod : (x : G) ∈ (R[S] (i+1) : Set G) * (H[S,q] t : Set G) :=
    hprod ▸ (show (x : G) ∈ (H[S,q] (i+1) : Set G) from x.property)
  obtain ⟨u, hu, w, hw, heq⟩ := Set.mem_mul.mp hxprod
  let uH : H[S,q] (i+1) := ⟨u, relativeUnitFiltration_le_simpleHGroup S.chain S.n S.b q.tail (i+1) hu⟩
  let wH : H[S,q] (i+1) := ⟨w, simpleHGroup_antitone S.chain S.n S.b q.tail hlev hw⟩
  have hU := (Subgroup.mem_normalizer_iff.mp hNorm u).mp uH.property
  have hW := (Subgroup.mem_normalizer_iff.mp hNorm w).mp wH.property
  have hX : x = uH*wH := Subtype.ext heq.symm
  have hX' : (⟨_, hx⟩ : H[S,q] (i+1)) = ⟨_, hU⟩ * ⟨_, hW⟩ := by
    apply Subtype.ext
    change g * (x : G) * g⁻¹ = (g*u*g⁻¹)*(g*w*g⁻¹)
    rw [← heq]
    group
  rw [hX', hX, map_mul, map_mul, hDet.conj_eq hg.1 uH hu.1 hU,
    evalHigh wH (simpleHGroup_le_unitFiltration S.chain S.n S.b q.tail t hw) hW]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem restrict_to_high_of_cons (ψ : AddChar F ℂ) (L : LatticeChain O F V)
    (n : ℤ) (b : A) (tail : List A) (i : ℕ) (hne : tail ≠ []) (hi : (i : ℤ) < finiteCriticalDepth L n b)
    {θ : simpleHGroup L n b tail (i+1) →* ℂˣ} (hθ : θ ∈ simpleCharacters ψ L n b tail i)
    (p : ℕ) (hpdef : p = max i ((finiteCriticalDepth L n b) / 2).toNat)
    (hNorm : relativeOrderNormalizer L b ≤
      Subgroup.normalizer (simpleHGroup L n b tail (p+1) : Set G)) :
    let hle := simpleHGroup_antitone L n b tail (show i+1 ≤ p+1 by rw [hpdef]; omega)
    θ.comp (Subgroup.inclusion hle) ∈ simpleCharacters ψ L n b tail p := by
  intro hle
  have hp : (p : ℤ) < finiteCriticalDepth L n b := by rw [hpdef]; omega
  have hpmax : max p ((finiteCriticalDepth L n b) / 2).toNat = p :=
    max_eq_left (by rw [hpdef]; exact le_max_right _ _)
  cases tail with
  | nil => exact (hne rfl).elim
  | cons c tail =>
    simp only [simpleCharacters, ite_eq_left hi, Set.mem_ofPred_eq] at hθ
    rw [← hpdef] at hθ
    simp only [simpleCharacters, ite_eq_left hp, Set.mem_ofPred_eq, hpmax]
    refine ⟨factorsThroughCentralizerDet_restrict hle hθ.1, ?_, ?_⟩
    · intro g hg
      refine ⟨hNorm hg, ?_⟩
      intro z hz
      exact (hθ.2.1 hg).2 ⟨z, hle z.property⟩ (hle hz)
    · obtain ⟨η, hη, he⟩ := hθ.2.2
      rw [hpmax]
      refine ⟨η, hη, ?_⟩
      intro z
      obtain ⟨_, hz, hv⟩ := he z
      exact ⟨z.property, hz, hv⟩

/-- The determinant and normalization laws, and the vanishing of the mixed
commutator used to compute the equal-depth pairing. -/
theorem relativeCommutatorLaws_of_mixedJ
    (hG : SimpleStratumGroupPropertiesStatement.{uF,uV})
    (hM : SimpleCharacterMixedJCommutator.{uF,uV}) :
    SimpleCharacterRelativeCommutatorLaws.{uF,uV} := by
  intro F _ _ _ _ V _ _ ψ hψ S hS0 hS q i hi θ hθ
  have hdet := simple_character_det ψ S.chain S.n S.b q.tail i hi hθ
  refine ⟨?_, fun _ _ hu hv hc => factorsThroughCentralizerDet.commutator_eq_one hdet hu hv hc, ?_⟩
  · intro k u hu
    have huK : u ∈ K[S] := ⟨hu.1, ((normalizer F V S.chain).1 k).1 hu.2⟩
    by_cases hzero : q.steps = 0
    · exact relativeUnit_normalizes_of_terminal hG ψ S hS0 hS q hzero i hi hθ huK
    · exact simple_character_normalizer_of_cons ψ S.chain S.n S.b q.tail i
        (fun h => hzero ((tail_nil_iff S q).mp h)) hi hθ huK
  · intro k hk hkj hip u w hu hw hc
    have hd := depth_pos S hS0 hS
    have hj : (jcut[S] : ℤ) = simpleJCutoff depth[S] := Int.toNat_of_nonneg (by unfold simpleJCutoff; omega)
    have hh : (hcut[S] : ℤ) = simpleHCutoff depth[S] := Int.toNat_of_nonneg (by unfold simpleHCutoff; omega)
    have hj₁ : 1 ≤ jcut[S] := hk.trans hkj.le
    have hdepth : depth[S] < (k : ℤ)+2*(jcut[S] : ℤ) := by rw [hj]; unfold simpleJCutoff; omega
    have hhc : hcut[S] ≤ k+jcut[S] := by
      have h : (hcut[S] : ℤ) ≤ (k : ℤ) + (jcut[S] : ℤ) := by
        rw [hj, hh]
        unfold simpleJCutoff simpleHCutoff
        omega
      exact_mod_cast h
    by_cases hzero : q.steps = 0
    · have htail := (tail_nil_iff S q).mpr hzero
      have hdn := terminal_depth S q hzero
      have hwU := simpleJGroup_le_unitFiltration S.chain S.n S.b q.tail _ hw
      have hcU := LatticeChain.commutatorElement_mem_unitFiltration S.chain hu.2 hwU
      have hcUH : ⁅u,w⁆ ∈ S.chain.unitFiltration (simpleHCutoff S.n).toNat := by
        rw [← hdn]
        exact S.chain.unitFiltration_antitone hhc hcU
      have hb : S.b ∈ S.chain.endFiltration (-S.n) := by
        apply (StratumEquivalence.mem_of_valuation_eq (m := -S.n) ?_).1
        exact hS.1.2
      have hnDepth : S.n < (k : ℤ)+2*(jcut[S] : ℤ) := by
        calc
          S.n = depth[S] := hdn.symm
          _ < _ := hdepth
      apply Units.ext
      rw [simple_character_trace_of_nil ψ S.chain S.n S.b q.tail i htail hθ ⟨_, hc⟩ hcUH,
        elementCharacter_commutator_eq_one_of_commute S.chain ψ hψ hb hu.2 hwU hu.1 hnDepth,
        Units.val_one]
    · obtain ⟨T, q', r, -, -, -, -, hr, -, hcrit, -, -, -, -⟩ :=
        q.exists_suffix hS0 (Nat.pos_of_ne_zero hzero)
      have hdr := finiteCriticalDepth_eq_of_criticalExponent S.chain S.n S.b r hcrit
      let n := r.toNat
      have hnr : (n : ℤ) = r := Int.toNat_of_nonneg hr.le
      let p := max i (depth[S] / 2).toNat
      have hp : p < n := by dsimp [p]; omega
      have hpHr : n / 2 ≤ p := by dsimp [p]; omega
      have hpK : p+1 ≤ k+jcut[S] := by dsimp [p]; unfold simpleHCutoff at hh; omega
      have hle := simpleHGroup_antitone S.chain S.n S.b q.tail (show i+1 ≤ p+1 by dsimp [p]; omega)
      have hmem : θ.comp (Subgroup.inclusion hle) ∈ C[ψ,S,q] p :=
        restrict_to_high_of_cons ψ S.chain S.n S.b q.tail i (fun h => hzero ((tail_nil_iff S q).mp h))
          hi hθ p rfl (((hG F V S hS0 hS q).2.2.1 (p+1)).1)
      have huM : (u : Module.End F V)-1 ∈ mixedAdjointLattice S.chain S.b k (-(n : ℤ)) := by
        refine centralizerLattice_le_mixedAdjointLattice S.chain S.b k _ ?_
        refine ⟨hu.2.2.2, ?_⟩
        change adjointMap 𝒪[F] S.b ((u : Module.End F V)-1) = 0
        rw [map_sub, StratumEquivalence.adjointMap_apply, StratumEquivalence.adjointMap_apply,
          mul_one, one_mul, sub_self, sub_zero, sub_eq_zero]
        exact hu.1
      have hcCrit : criticalExponent S.chain S.b = ((-(n : ℤ) : ℤ) : WithBot ℤ) := by rwa [hnr]
      obtain ⟨hc', he⟩ := hM F V ψ hψ S hS0 hS q n p k jcut[S] hcCrit hpHr hp hk hj₁
        hpK (by omega) _ hmem u w huM hw
      have hzero' : (↑u⁻¹ : Module.End F V) * S.b * (u : Module.End F V) - S.b = 0 := by
        rw [mul_assoc, hu.1, ← mul_assoc, Units.inv_mul, one_mul, sub_self]
      apply Units.ext
      change ((θ.comp (Subgroup.inclusion hle)) ⟨_, hc'⟩ : ℂ) = (1 : ℂ)
      rw [he, hzero', elementCharacter_apply, zero_mul, AddChar.map_zero_eq_one]

end SimpleStratum

end Langlands.BushnellKutzko

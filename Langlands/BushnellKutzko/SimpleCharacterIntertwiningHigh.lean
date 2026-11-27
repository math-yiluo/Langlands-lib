import Langlands.BushnellKutzko.SimpleCharacterCoreRestriction
import Langlands.BushnellKutzko.SimpleCharacterCovarianceProof

/-! # Intertwining of a simple character at or above its cutoff -/

noncomputable section

open ValuativeRel
open scoped Classical Pointwise

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "O" => 𝒪[F]
local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "P" => LatticeChain.endFiltration
local notation "J[" S "," q "]" => simpleJGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "H[" S "," q "]" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "Hₗ[" S "," q "]" => simpleHLayer (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "C[" ψ "," S "," q "]" => simpleCharacters ψ (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "Y[" S "," q "," m "]" => simpleCharacterIntertwiningFactor S q m
local notation "B[" S "]" => (centralizerUnitGroup (Stratum.b S) : Set G)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel F] in
/-- A restriction, with an inclusion into the original domain, can only enlarge
self-intertwining. -/
theorem characterSelfIntertwining_subset_of_agrees {H D : Subgroup G} (hD : D ≤ H)
    (θ : H →* ℂˣ) (χ : D →* ℂˣ) (hχ : ∀ u : D, θ ⟨u, hD u.prop⟩ = χ u) :
    characterSelfIntertwining θ ⊆ characterSelfIntertwining χ := by
  intro g hg u hu
  have he := hg ⟨u, hD u.prop⟩ (hD hu)
  change θ ⟨g * (u : G) * g⁻¹, hD hu⟩ = θ ⟨u, hD u.prop⟩ at he
  rw [hχ ⟨_, hu⟩, hχ u] at he
  exact he

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel F] in
/-- Multiplication on both sides by character normalizers preserves containment
in the character self-intertwining set. -/
theorem sandwich_subset_characterSelfIntertwining {H K : Subgroup G} (θ : H →* ℂˣ)
    (hK : K ≤ characterNormalizerSubgroup θ) {I : Set G} (hI : I ⊆ characterSelfIntertwining θ) :
    (K : Set G) * I * (K : Set G) ⊆ characterSelfIntertwining θ := by
  intro g hg
  obtain ⟨ku, hku, v, hv, rfl⟩ := Set.mem_mul.mp hg
  obtain ⟨k, hk, u, hu, rfl⟩ := Set.mem_mul.mp hku
  exact (mem_characterSelfIntertwining_mul_right_iff (hK hv)).mpr
    ((mem_characterSelfIntertwining_mul_left_iff (hK hk)).mpr (hI hu))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The middle centralizer is contained in the outer double coset. -/
theorem centralizer_subset_simpleCharacterDoubleCoset (S : Stratum O F V)
    (q : S.DefiningSequenceChoice) (m : ℕ) : B[S] ⊆ Y[S,q,m] * B[S] * Y[S,q,m] := by
  intro g hg
  have h := one_mem_simpleCharacterIntertwiningFactor S q m
  exact Set.mem_mul.mpr ⟨g, Set.mem_mul.mpr ⟨1, h, g, hg, one_mul _⟩, 1, h, mul_one _⟩

/-- Formal intertwining of the ordinary stratum coset embeds into the
character double coset at the same depth. -/
theorem formalCoset_subset_simpleCharacterDoubleCoset
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    (m : ℕ) (hmn : (m : ℤ) < S.n) (hmc : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b) :
    latticeCosetIntertwining S.b (P S.chain (-(m : ℤ))) ⊆ Y[S,q,m] * B[S] * Y[S,q,m] := by
  by_cases hb : elementAlgebra S.b = ⊥
  · intro x hx
    let := S.chain.finiteDimensional
    apply centralizer_subset_simpleCharacterDoubleCoset S q m
    change Commute S.b (x : A)
    exact sub_eq_zero.mp (commute_of_elementAlgebra_eq_bot S.b hb (x : A))
  · obtain ⟨r, hr, hrn, hcrit⟩ := criticalDepth_of_simple S hS0 hS q hb
    have hmr : m < r := by
      rw [SimpleStratumLattice.simpleCriticalDepth_eq S.chain hcrit, WithTop.coe_lt_coe] at hmc
      exact_mod_cast hmc
    rw [latticeCosetIntertwining_filtration_eq_mixed_doubleCoset S hS.1 hmn hmr hcrit,
      ← coe_simpleCharacterIntertwiningSubgroup S hS0 hS q hr hmr hcrit]
    have hX : (mixedAdjointUnitGroup S.chain S.b (r - m) (-(r : ℤ)) (by omega) : Set G) ⊆
        (simpleCharacterIntertwiningSubgroup S q r m hmr : Set G) := by
      change mixedAdjointUnitGroup S.chain S.b (r - m) (-(r : ℤ)) (by omega) ≤ _
      exact le_sup_left
    exact Set.mul_subset_mul (Set.mul_subset_mul hX (Set.Subset.refl _)) hX

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem simpleCharacters_exists_high_twist (ψF : AddChar F ℂ) (S : Stratum O F V)
    (q : S.DefiningSequenceChoice) {c : A} {tail : List A} (ht : q.tail = c :: tail)
    {r m : ℕ} (hcrit : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ))
    (hm : r / 2 ≤ m) (hmr : m < r) {θ : H[S,q] (m + 1) →* ℂˣ} (hθ : θ ∈ C[ψF,S,q] m) :
    ∃ θ₀ ∈ simpleCharacters ψF S.chain S.n c tail m,
      characterAgreesOn (H[S,q] (m + 1)) θ θ₀ (elementCharacter (traceCharacter ψF) (S.b - c)) := by
  have hf := finiteCriticalDepth_of_criticalExponent_eq S.chain S.n (r : ℤ) S.b hcrit
  have h₁ : (m : ℤ) < finiteCriticalDepth S.chain S.n S.b := by rw [hf]; omega
  have h₂ : (finiteCriticalDepth S.chain S.n S.b / 2).toNat = r / 2 := by rw [hf]; omega
  generalize hu : q.tail = t at θ hθ ⊢
  have he : t = c :: tail := hu.symm.trans ht
  clear hu
  subst t
  simp only [simpleCharacters, ite_eq_left h₁] at hθ
  rw [h₂, max_eq_left hm] at hθ
  exact hθ.2.2

/-- For `r / 2 ≤ m`, a terminal character is the element character.
At a successor step, the intertwining set of the restriction to `H^{r+1}`
supplies the units on whose overlaps the trace ratio is applied. -/
theorem simpleCharacterIntertwining_high_of_successor
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    (ih : ∀ (T : Stratum O F V), T.r = 0 → T.IsSimple → ∀ (q' : T.DefiningSequenceChoice),
      q'.steps < q.steps → ∀ i : ℕ, (i : ℤ) < T.n → ((i : ℤ) : WithTop ℤ) < simpleCriticalDepth T.chain T.b →
      ∀ χ ∈ C[ψF,T,q'] i, characterSelfIntertwining χ = Y[T,q',i] * B[T] * Y[T,q',i])
    {r m : ℕ} (hr : 0 < r) (hmn : (m : ℤ) < S.n) (hmr : m < r) (hm : r / 2 ≤ m)
    (hcrit : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ))
    {θ : H[S,q] (m + 1) →* ℂˣ} (hθ : θ ∈ C[ψF,S,q] m) :
    characterSelfIntertwining θ = Y[S,q,m] * B[S] * Y[S,q,m] := by
  have hFormal := simpleCharacter_formalIntertwining_eq_doubleCoset S hS0 hS q ψF hψ hr hmn hmr hcrit
  dsimp only at hFormal
  by_cases hq : q.steps = 0
  · have hn : S.n = (r : ℤ) := level_eq_of_terminal_of_criticalExponent_eq q hq hcrit
    have hv := simpleCharacters_high_values ψF hψ q (by rw [hn]; omega) hθ
    have hcov (g : G) : characterConjugationRatio ψF S.b θ g := by
      intro u hu
      rw [hv ⟨_, hu⟩, hv u, elementCharacter_conj]
      rw [← elementCharacter_add]
      congr 1
      abel
    rw [← hFormal]
    exact Set.ext fun g => simpleCharacter_intertwining_iff_formal_of_ratio S hS0 hS q ψF hψ θ (hcov g)
  · obtain ⟨T, q', s, hL, hn, hT0, hT, hrn, hs, hTc, hδ, htail, hlt, hH, hJ⟩ :=
      exists_simpleCharacterSuffix S hS0 hS q (Nat.pos_of_ne_zero hq)
    have hrs : r = s := by
      exact_mod_cast neg_injective (WithBot.coe_injective (hcrit.symm.trans hs))
    subst s
    rcases T with ⟨L', n', t', c, hlt', hval'⟩
    change L' = S.chain at hL
    change n' = S.n at hn
    change t' = 0 at hT0
    subst L' n' t'
    let T : Stratum O F V := ⟨S.chain, S.n, 0, c, hlt', hval'⟩
    have hcr : ((r : ℤ) : WithTop ℤ) < simpleCriticalDepth T.chain T.b :=
      simpleCriticalDepth_gt_of_criticalExponent_lt (L := S.chain) (β := c) hTc
    have hcm : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth T.chain T.b :=
      (WithTop.coe_lt_coe.mpr (by exact_mod_cast hmr : (m : ℤ) < r)).trans hcr
    obtain ⟨θ₀, hθ₀, hagree⟩ := simpleCharacters_exists_high_twist ψF S q htail hcrit hm hmr hθ
    let inc := simpleHGroup_antitone S.chain S.n c q'.tail (Nat.succ_le_succ hmr.le)
    let θr := θ₀.comp (Subgroup.inclusion inc)
    have hθr : θr ∈ C[ψF,T,q'] r := simpleCharacters_restrict_forward ψF T rfl hT q' hmr.le hrn hcr hθ₀
    have hI₀ := ih T rfl hT q' hlt m hmn hcm θ₀ hθ₀
    have hIr := ih T rfl hT q' hlt r hrn hcr θr hθr
    have hB : B[T] ⊆ characterSelfIntertwining θ₀ := hI₀.symm ▸ centralizer_subset_simpleCharacterDoubleCoset T q' m
    have hrestr : H[T,q'] (r + 1) ≤ H[S,q] (m + 1) :=
      (hH r (by omega)).ge.trans (simpleHGroup_antitone S.chain S.n S.b q.tail (Nat.succ_le_succ hmr.le))
    have hIr_sub : characterSelfIntertwining θ ⊆ characterSelfIntertwining θr := by
      apply characterSelfIntertwining_subset_of_agrees hrestr θ θr
      intro u
      obtain ⟨_, _, hv⟩ := hagree ⟨u, hrestr u.prop⟩
      have hu := simpleHGroup_le_unitFiltration T.chain T.n T.b q'.tail (r + 1) u.prop
      have hδu := elementCharacter_eq_one_of_depth S.chain ψF hψ hδ (by omega) hu
      change elementCharacter (traceCharacter ψF) (S.b - c) (u : G) = 1 at hδu
      change (θ ⟨u, hrestr u.prop⟩ : ℂ) = (θr u : ℂ) *
        elementCharacter (traceCharacter ψF) (S.b - c) (u : G) at hv
      apply Units.ext
      simpa only [hδu, mul_one] using hv
    have hcov (g : G) (hg : g ∈ characterSelfIntertwining θr) : characterConjugationRatio ψF S.b θ g := by
      have h₀ := simpleCharacter_covariance_of_centralizer_intertwining ψF hψ T rfl hT q'
        hmn hcm hcr hm hθ₀ hB (hIr ▸ hg)
      let hHC := (hH m hm).le
      let θ₀' := θ₀.comp (Subgroup.inclusion hHC)
      have h₀' : characterConjugationRatio ψF c θ₀' g := fun u hu => h₀ ⟨u, hHC u.prop⟩ (hHC hu)
      have htwist (u : H[S,q] (m + 1)) : (θ u : ℂ) = (θ₀' u : ℂ) *
          elementCharacter (traceCharacter ψF) (S.b - c) (u : G) := by
        obtain ⟨_, _, hv⟩ := hagree u
        exact hv
      simpa only [add_sub_cancel] using characterConjugationRatio.of_twist ψF h₀' htwist
    have hOrd : latticeCosetIntertwining S.b (P S.chain (-(m : ℤ))) ⊆ characterSelfIntertwining θr := by
      refine ((latticeCosetIntertwining_mono S.b) (S.chain.endFiltration_antitone (by omega : -(r : ℤ) ≤ -m))).trans ?_
      rw [latticeCosetIntertwining_eq_of_sub_mem hδ, hIr]
      exact formalCoset_subset_simpleCharacterDoubleCoset T rfl hT q' r hrn hcr
    have hJNorm : J[S,q] ((r + 1) / 2) ≤ characterNormalizerSubgroup θr := fun x hx =>
      simpleJ_le_characterNormalizerSubgroup ψF hψ T rfl hT q' r hrn hcr hθr
        (simpleJGroup_antitone T.chain T.n T.b q'.tail (Nat.zero_le _) ((hJ _ le_rfl).le hx))
    have hFormal_sub : latticeCosetIntertwining S.b (traceDualLattice ψF (Hₗ[S,q] (m + 1))) ⊆
        characterSelfIntertwining θr := by
      rw [simpleCharacter_formalIntertwining_eq_sandwich S hS0 hS q ψF hψ hr hcrit]
      exact sandwich_subset_characterSelfIntertwining θr hJNorm hOrd
    rw [← hFormal]
    ext g
    exact ⟨fun hg => (simpleCharacter_intertwining_iff_formal_of_ratio S hS0 hS q ψF hψ θ
      (hcov g (hIr_sub hg))).mp hg, fun hg => (simpleCharacter_intertwining_iff_formal_of_ratio S hS0 hS q ψF hψ θ
      (hcov g (hFormal_sub hg))).mpr hg⟩

end Langlands.BushnellKutzko

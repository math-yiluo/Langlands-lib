import Langlands.BushnellKutzko.SimpleCharacterCoreRestriction
import Langlands.BushnellKutzko.StratumEquivalenceProof
import Langlands.BushnellKutzko.SimpleCharacterIntertwiningStatement
import Langlands.BushnellKutzko.SimpleCharacterPairs
import Langlands.BushnellKutzko.SimpleCharacterRestrictionHigh

/-! # Comparing `𝔅 + 𝔓` through intertwining sets

Lattice comparisons for the proof of BK93 (3.5.1), printed p. 117: equal intertwining
double cosets give equal images of the centralizer orders modulo `𝔓`, these images
determine the ramification index and residue degree, and they detect the first jump of a
defining sequence. The results that use BK93 (3.3.2) take
`SimpleCharacterIntertwiningStatement` as a hypothesis.
-/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

namespace CentralizerResidue

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

section Comparison

variable (L : LatticeChain 𝒪[F] F V)

/-- A unit of `End_F(V)` congruent to `1` modulo `𝔓` lies in `U^1(𝔄)`. -/
theorem mem_unitFiltration_one_of_sub_mem {g : G} (hg : (g : A) - 1 ∈ L.endFiltration 1) :
    g ∈ L.unitFiltration 1 := by
  obtain ⟨g', hg', he⟩ := L.exists_mem_unitFiltration le_rfl hg
  have : g' = g := Units.ext (by rw [he]; abel)
  rwa [← this]

/-- A scalar from `𝔬_F` lies in the centralizer order `𝔅` of every element. -/
theorem algebraMap_mem_centralizerLattice (β : A) (t : 𝒪[F]) :
    algebraMap F A (t : F) ∈ centralizerLattice L β 0 := by
  refine ⟨?_, ?_⟩
  · have h1 : (1 : A) ∈ L.endFiltration 0 := L.order.one_mem
    have h := (L.endFiltration 0).smul_mem t h1
    have heq : t • (1 : A) = algebraMap F A (t : F) := by
      rw [Algebra.algebraMap_eq_smul_one]
      rfl
    rwa [heq] at h
  · change adjointMap 𝒪[F] β (algebraMap F A (t : F)) = 0
    rw [StratumEquivalence.adjointMap_apply, Algebra.commutes, sub_self]

/-- If `y, y' ∈ U^1(𝔄)` and `b ∈ 𝔄`, then `y b y' ≡ b` modulo `𝔓`. -/
theorem mul_mul_sub_mem {y y' : G} (hy : y ∈ L.unitFiltration 1)
    (hy' : y' ∈ L.unitFiltration 1) {b : A} (hb : b ∈ L.endFiltration 0) :
    (y : A) * b * y' - b ∈ L.endFiltration 1 := by
  have h : (y : A) * b * y' - b = ((y : A) - 1) * b * y' + b * ((y' : A) - 1) := by
    noncomm_ring
  rw [h]
  refine add_mem ?_ ?_
  · have h1 := L.mul_mem_endFiltration (L.mul_mem_endFiltration hy.2.2 hb) hy'.1
    simpa using h1
  · have h1 := L.mul_mem_endFiltration hb hy'.2.2
    simpa using h1

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- If `𝔬_F` is infinite, every endomorphism `x` of the finite-dimensional space `V` is the
difference of a scalar `t ∈ 𝔬_F` and a unit of `End_F(V)`: any `t` avoiding the finitely
many eigenvalues of `x` will do. -/
theorem exists_algebraMap_sub_isUnit [Infinite 𝒪[F]] [FiniteDimensional F V] (x : A) :
    ∃ t : 𝒪[F], IsUnit (algebraMap F A (t : F) - x) := by
  have hfin : Set.Finite {t : 𝒪[F] | x.HasEigenvalue (t : F)} :=
    (Module.End.finite_hasEigenvalue x).preimage (Subtype.val_injective.injOn)
  obtain ⟨t, ht⟩ := hfin.infinite_compl.nonempty
  refine ⟨t, ?_⟩
  have ht' : ¬ (t : F) ∈ spectrum F x := fun h =>
    ht (Module.End.hasEigenvalue_iff_mem_spectrum.mpr h)
  rw [spectrum.mem_iff, not_not] at ht'
  exact ht'

/-- The ring of integers of a nonarchimedean local field is infinite. -/
theorem infinite_integers : Infinite 𝒪[F] := by
  by_contra h
  rw [not_infinite_iff_finite] at h
  exact IsDiscreteValuationRing.not_isField 𝒪[F] (Finite.isField_of_domain 𝒪[F])

/-- **Residue comparison.** Suppose every element of `Y ⊆ G` is congruent to `1` modulo `𝔓`
and `B_{β₁}^× ⊆ Y B_{β₂}^× Y`. Then `𝔅_{β₁} ⊆ 𝔅_{β₂} + 𝔓`. Each `x ∈ 𝔅_{β₁}` is `t − u`
with `t ∈ 𝔬_F` and `u ∈ 𝔅_{β₁} ∩ B_{β₁}^×`; writing `u = y b y'` gives `b ∈ 𝔅_{β₂}` and
`u ≡ b` modulo `𝔓`. -/
theorem centralizerLattice_le_sup {β₁ β₂ : A} {Y : Set G}
    (hY : ∀ y ∈ Y, (y : A) - 1 ∈ L.endFiltration 1)
    (hB : (centralizerUnitGroup β₁ : Set G) ⊆ Y * (centralizerUnitGroup β₂ : Set G) * Y) :
    centralizerLattice L β₁ 0 ≤ centralizerLattice L β₂ 0 ⊔ L.endFiltration 1 := by
  have := L.finiteDimensional
  have : Infinite 𝒪[F] := infinite_integers
  intro x hx
  obtain ⟨hx0, hxc⟩ := hx
  have hxc' : β₁ * x = x * β₁ := by
    have h : adjointMap 𝒪[F] β₁ x = 0 := hxc
    rw [StratumEquivalence.adjointMap_apply, sub_eq_zero] at h
    exact h
  obtain ⟨t, ht⟩ := exists_algebraMap_sub_isUnit x
  set u : G := ht.unit with hu
  have hu' : (u : A) = algebraMap F A (t : F) - x := ht.unit_spec
  have htB := algebraMap_mem_centralizerLattice L β₁ t
  have huB₁ : u ∈ centralizerUnitGroup β₁ := by
    change β₁ * (u : A) = (u : A) * β₁
    rw [hu', mul_sub, sub_mul, hxc', Algebra.commutes]
  obtain ⟨a, ⟨y, hyY, b, hb, rfl⟩, y', hy'Y, hyb⟩ := hB huB₁
  have hy := mem_unitFiltration_one_of_sub_mem L (hY y hyY)
  have hy' := mem_unitFiltration_one_of_sub_mem L (hY y' hy'Y)
  have hu0 : (u : A) ∈ L.endFiltration 0 := by
    rw [hu']
    exact sub_mem htB.1 hx0
  have hb0 : (b : A) ∈ L.endFiltration 0 := by
    have hbu : (b : A) = ((y⁻¹ : G) : A) * (u : A) * ((y'⁻¹ : G) : A) := by
      rw [← hyb]
      simp only [Units.val_mul]
      rw [show ((y⁻¹ : G) : A) * ((y : A) * (b : A) * (y' : A)) * ((y'⁻¹ : G) : A) =
          (((y⁻¹ : G) : A) * (y : A)) * (b : A) * ((y' : A) * ((y'⁻¹ : G) : A)) by noncomm_ring]
      simp
    rw [hbu]
    have h1 := L.mul_mem_endFiltration (L.mul_mem_endFiltration hy.2.1 hu0) hy'.2.1
    simpa using h1
  have hbB : (b : A) ∈ centralizerLattice L β₂ 0 := by
    refine ⟨hb0, ?_⟩
    change adjointMap 𝒪[F] β₂ (b : A) = 0
    rw [StratumEquivalence.adjointMap_apply, sub_eq_zero]
    exact hb
  have hub : (u : A) - (b : A) ∈ L.endFiltration 1 := by
    rw [← hyb]
    simpa using mul_mul_sub_mem L hy hy' hb0
  have hx_eq : x = (algebraMap F A (t : F) - (b : A)) + -((u : A) - (b : A)) := by
    rw [hu']
    abel
  rw [hx_eq]
  exact Submodule.add_mem_sup
    (sub_mem (algebraMap_mem_centralizerLattice L β₂ t) hbB) (neg_mem hub)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- If `1 ∈ Y`, then `B ⊆ Y B Y`. -/
theorem subset_mul_mul {Y : Set G} (h1 : (1 : G) ∈ Y) (B : Set G) : B ⊆ Y * B * Y := by
  intro b hb
  exact ⟨1 * b, ⟨1, h1, b, hb, rfl⟩, 1, h1, by simp⟩

/-- **Equality of `𝔅 + 𝔓` from equal double-coset products.** If `Y₁ B_{β₁}^× Y₁ =
Y₂ B_{β₂}^× Y₂`, where `1 ∈ Y_i` and every element of `Y_i` is congruent to `1`
modulo `𝔓`, then `𝔅_{β₁} + 𝔓 = 𝔅_{β₂} + 𝔓`. -/
theorem sup_eq_of_mul_mul_eq {β₁ β₂ : A} {Y₁ Y₂ : Set G}
    (h₁ : (1 : G) ∈ Y₁) (h₂ : (1 : G) ∈ Y₂)
    (hY₁ : ∀ y ∈ Y₁, (y : A) - 1 ∈ L.endFiltration 1)
    (hY₂ : ∀ y ∈ Y₂, (y : A) - 1 ∈ L.endFiltration 1)
    (h : Y₁ * (centralizerUnitGroup β₁ : Set G) * Y₁ =
      Y₂ * (centralizerUnitGroup β₂ : Set G) * Y₂) :
    centralizerLattice L β₁ 0 ⊔ L.endFiltration 1 =
      centralizerLattice L β₂ 0 ⊔ L.endFiltration 1 := by
  apply le_antisymm
  · refine sup_le (centralizerLattice_le_sup L hY₂ ?_) le_sup_right
    rw [← h]
    exact subset_mul_mul h₁ _
  · refine sup_le (centralizerLattice_le_sup L hY₁ ?_) le_sup_right
    rw [h]
    exact subset_mul_mul h₂ _

end Comparison

section Factor

/-- If `m < n` and `m` is below the critical depth of `β`, then `m` is below its finite
critical depth (which is `n` when `β` is scalar). -/
theorem lt_finiteCriticalDepth (L : LatticeChain 𝒪[F] F V) {n : ℤ} {β : A} {m : ℤ}
    (hn : m < n) (hm : (m : WithTop ℤ) < simpleCriticalDepth L β) :
    m < finiteCriticalDepth L n β := by
  unfold finiteCriticalDepth
  cases h : simpleCriticalDepth L β with
  | top => simpa using hn
  | coe r =>
    rw [h] at hm
    simpa using WithTop.coe_lt_coe.mp hm

/-- The critical depth determines the critical exponent. -/
theorem criticalExponent_eq_of_simpleCriticalDepth_eq (L : LatticeChain 𝒪[F] F V) {β β' : A}
    (h : simpleCriticalDepth L β = simpleCriticalDepth L β') :
    criticalExponent L β = criticalExponent L β' := by
  unfold simpleCriticalDepth at h
  cases hβ : criticalExponent L β <;> cases hβ' : criticalExponent L β' <;>
    simp only [hβ, hβ'] at h
  · rfl
  · exact absurd h WithTop.top_ne_coe
  · exact absurd h WithTop.coe_ne_top
  · rw [WithTop.coe_inj, neg_inj] at h
    rw [h]

/-- Below the critical depth, every element of the outer factor of BK93 (3.3.2) is
congruent to `1` modulo `𝔓`. -/
theorem sub_one_mem_of_mem_simpleCharacterIntertwiningFactor (S : Stratum 𝒪[F] F V)
    (q : S.DefiningSequenceChoice) {m : ℕ} (hn : (m : ℤ) < S.n)
    (hm : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b) :
    ∀ y ∈ simpleCharacterIntertwiningFactor S q m,
      (y : A) - 1 ∈ S.chain.endFiltration 1 := by
  intro y hy
  unfold simpleCharacterIntertwiningFactor at hy
  split_ifs at hy with hbot
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [Units.val_one, sub_self]
    exact zero_mem _
  · have hr := lt_finiteCriticalDepth S.chain hn hm
    set r := finiteCriticalDepth S.chain S.n S.b with hr_def
    have hQN : centralizerLattice S.chain S.b (r - (m : ℤ)) *
        adjointLattice S.chain S.b (-r) ≤ S.chain.endFiltration 1 := by
      rw [Submodule.mul_le]
      intro a ha c hc
      have h := S.chain.mul_mem_endFiltration ha.1 hc.1
      exact S.chain.endFiltration_antitone (by omega) h
    have hJ : simpleJLayer S.chain S.n S.b q.tail (simpleJCutoff r).toNat ≤
        S.chain.endFiltration 1 := by
      refine inf_le_right.trans (S.chain.endFiltration_antitone ?_)
      unfold simpleJCutoff
      omega
    exact sup_le hQN hJ hy

end Factor

section Invariants

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V]

/-- **Invariants from `𝔅 + 𝔓`.** Two pure strata on one lattice chain with the same
`𝔅 + 𝔓` generate fields with the same ramification index and residue degree
(BK93 (2.1.4)(iii), printed p. 50). -/
theorem invariants_eq_of_sup_eq {S T : Stratum 𝒪[F] F V} (hc : S.chain = T.chain)
    (hS : S.IsPure) (hT : T.IsPure)
    (hsup : centralizerLattice S.chain S.b 0 ⊔ S.chain.endFiltration 1 =
      centralizerLattice S.chain T.b 0 ⊔ S.chain.endFiltration 1) :
    elementRamificationIndex F S.b = elementRamificationIndex F T.b ∧
      elementResidueDegree F S.b = elementResidueDegree F T.b := by
  obtain ⟨⟨hfS, huS⟩, -⟩ := hS
  obtain ⟨⟨hfT, huT⟩, -⟩ := hT
  unfold elementRamificationIndex elementResidueDegree
  simp only [hfS, hfT, ↓reduceDIte]
  let _ := hfS.toField
  let _ := hfT.toField
  have huT' : ∀ a : (elementAlgebra T.b)ˣ,
      subfieldUnits F (elementAlgebra T.b) V a ∈ S.chain.stabilizer := by
    rw [hc]
    exact huT
  have hM : StratumEquivalence.fieldOrder S.chain (elementAlgebra S.b) ⊔
        S.chain.endFiltration 1 =
      StratumEquivalence.fieldOrder S.chain (elementAlgebra T.b) ⊔ S.chain.endFiltration 1 := by
    rw [StratumEquivalence.fieldOrder_elementAlgebra S.chain hfS,
      StratumEquivalence.fieldOrder_elementAlgebra S.chain hfT, hsup]
  have : FiniteDimensional F (elementAlgebra S.b) :=
    FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule (elementAlgebra S.b))
  have : FiniteDimensional F (elementAlgebra T.b) :=
    FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule (elementAlgebra T.b))
  exact ⟨StratumEquivalence.ramificationIndex_eq_of_sup_eq S.chain huS huT' hM,
    StratumEquivalence.residueDegree_eq_of_sup_eq S.chain huS huT' hM⟩

/-- A pure stratum with `𝔅 + 𝔓 = 𝔄` has scalar parameter: its critical index set is
empty, since `𝔑_k ⊆ 𝔄` for every `k`. -/
theorem elementAlgebra_eq_bot_of_sup_eq_top {S : Stratum 𝒪[F] F V} (hS : S.IsPure)
    (hsup : centralizerLattice S.chain S.b 0 ⊔ S.chain.endFiltration 1 =
      S.chain.endFiltration 0) :
    elementAlgebra S.b = ⊥ := by
  by_contra hns
  obtain ⟨⟨k, hk⟩, -⟩ := StratumEquivalence.criticalIndexSet_nonempty_bddAbove hS hns
  apply hk
  rw [hsup]
  exact inf_le_left

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V] in
/-- `𝔅 + 𝔓 = 𝔄` for a scalar parameter. -/
theorem sup_eq_top_of_elementAlgebra_eq_bot (L : LatticeChain 𝒪[F] F V) {β : A}
    (hβ : elementAlgebra β = ⊥) :
    centralizerLattice L β 0 ⊔ L.endFiltration 1 = L.endFiltration 0 := by
  rw [StratumEquivalence.centralizerLattice_zero_of_bot L hβ]
  exact sup_eq_left.mpr (L.endFiltration_antitone (by norm_num))

/-- **The first jump is detected by `𝔅 + 𝔓`.** Let `[𝔄,n,r,β]` be pure with
`k₀(β,𝔄) = −r`, and let `γ` be a pure parameter on the same chain with `β − γ ∈ 𝔓^{−r}`
and `k₀(γ,𝔄) < −r`. Then `𝔅_γ + 𝔓 ≠ 𝔅_β + 𝔓`: otherwise
`𝔑_{−r}(β) = 𝔑_{−r}(γ) ⊆ 𝔅_γ + 𝔓 = 𝔅_β + 𝔓`, so `−r` would not be a critical index. -/
theorem sup_ne_of_criticalExponent_eq {S T : Stratum 𝒪[F] F V} (hc : T.chain = S.chain)
    (hS : S.IsPure) (hT : T.IsPure) {r : ℤ}
    (hk : criticalExponent S.chain S.b = ((-r : ℤ) : WithBot ℤ))
    (hsub : S.b - T.b ∈ S.chain.endFiltration (-r))
    (hkT : criticalExponent S.chain T.b < ((-r : ℤ) : WithBot ℤ)) :
    centralizerLattice S.chain T.b 0 ⊔ S.chain.endFiltration 1 ≠
      centralizerLattice S.chain S.b 0 ⊔ S.chain.endFiltration 1 := by
  intro hsup
  have hns : elementAlgebra S.b ≠ ⊥ := by
    intro hbot
    simp only [criticalExponent, hbot, ↓reduceIte] at hk
    exact WithBot.bot_ne_coe hk
  obtain ⟨hne, hbdd⟩ := StratumEquivalence.criticalIndexSet_nonempty_bddAbove hS hns
  have hmem := Int.csSup_mem hne hbdd
  have hsSup : sSup (criticalIndexSet S.chain S.b) = -r := by
    simp only [criticalExponent, hns, ↓reduceIte] at hk
    exact WithBot.coe_injective hk
  rw [hsSup] at hmem
  apply hmem
  have hTfacts : elementAlgebra T.b = ⊥ ∨ BddAbove (criticalIndexSet S.chain T.b) := by
    by_cases hbot : elementAlgebra T.b = ⊥
    · exact Or.inl hbot
    · right
      have h := (StratumEquivalence.criticalIndexSet_nonempty_bddAbove hT hbot).2
      rwa [hc] at h
  rw [StratumEquivalence.adjointLattice_eq_of_sub_mem S.chain le_rfl hsub, ← hsup]
  exact StratumEquivalence.adjointLattice_le_of_criticalExponent_lt S.chain hTfacts hkT le_rfl

end Invariants


section Pairs

omit [ValuativeRel F]

/-- Two characters on equal subgroups with equal values form equal pairs. -/
theorem pair_eq_of_apply {K₁ K₂ : Subgroup G} {χ₁ : K₁ →* ℂˣ} {χ₂ : K₂ →* ℂˣ}
    (hK : K₁ = K₂)
    (hv : ∀ (g : G) (h₁ : g ∈ K₁) (h₂ : g ∈ K₂), χ₁ ⟨g, h₁⟩ = χ₂ ⟨g, h₂⟩) :
    (⟨K₁, χ₁⟩ : CharacterPair G) = ⟨K₂, χ₂⟩ := by
  subst hK
  have : χ₁ = χ₂ := MonoidHom.ext fun g => hv g g.2 g.2
  rw [this]

/-- Restricting equal pairs to equal subgroups gives equal pairs. -/
theorem pair_restrict_eq {H₁ H₂ K₁ K₂ : Subgroup G} {θ₁ : H₁ →* ℂˣ} {θ₂ : H₂ →* ℂˣ}
    (h : (⟨H₁, θ₁⟩ : CharacterPair G) = ⟨H₂, θ₂⟩) (hK : K₁ = K₂) (h₁ : K₁ ≤ H₁)
    (h₂ : K₂ ≤ H₂) :
    (⟨K₁, θ₁.comp (Subgroup.inclusion h₁)⟩ : CharacterPair G) =
      ⟨K₂, θ₂.comp (Subgroup.inclusion h₂)⟩ := by
  obtain ⟨rfl, hθ⟩ := Sigma.mk.inj_iff.mp h
  cases hθ
  subst hK
  rfl

/-- The self-intertwining set of a character depends only on its pair. -/
theorem characterSelfIntertwining_eq_of_pair_eq {H₁ H₂ : Subgroup G} {θ₁ : H₁ →* ℂˣ}
    {θ₂ : H₂ →* ℂˣ} (h : (⟨H₁, θ₁⟩ : CharacterPair G) = ⟨H₂, θ₂⟩) :
    characterSelfIntertwining θ₁ = characterSelfIntertwining θ₂ :=
  congrArg (fun P : CharacterPair G => characterSelfIntertwining P.2) h

end Pairs

section CommonPair

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A simple stratum at level `m` has critical depth greater than `m`. -/
theorem lt_simpleCriticalDepth_of_isSimple {S : Stratum 𝒪[F] F V} (hS : S.IsSimple) :
    (S.r : WithTop ℤ) < simpleCriticalDepth S.chain S.b := by
  have h := hS.2
  unfold simpleCriticalDepth
  cases hk : criticalExponent S.chain S.b with
  | bot => exact WithTop.coe_lt_top _
  | coe k =>
    rw [hk] at h
    have h' : k < -S.r := WithBot.coe_lt_coe.mp h
    exact WithTop.coe_lt_coe.mpr (by omega)

/-- **`𝔅 + 𝔓` from a common simple character, given (3.3.2).** Let `[𝔄,n,0,β]` and
`[𝔄,n',0,β']` be simple strata on one lattice chain, with defining sequences. If
`θ ∈ C(𝔄,m,β)` and `θ' ∈ C(𝔄,m,β')` form the same pair, for `m` below both levels and
both critical depths, then, under BK93 (3.3.2) (`SimpleCharacterIntertwiningStatement`),
`𝔅_β + 𝔓 = 𝔅_{β'} + 𝔓`. Both self-intertwining sets equal `I_G(θ)`. -/
theorem sup_eq_of_pair_eq (hI : SimpleCharacterIntertwiningStatement.{uF, uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {S T : Stratum 𝒪[F] F V} (hS0 : S.r = 0) (hT0 : T.r = 0) (hS : S.IsSimple)
    (hT : T.IsSimple) (hc : T.chain = S.chain) (q : S.DefiningSequenceChoice)
    (q' : T.DefiningSequenceChoice) {m : ℕ} (hmS : (m : ℤ) < S.n) (hmT : (m : ℤ) < T.n)
    (hcS : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    (hcT : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth T.chain T.b)
    {θ : simpleHGroup S.chain S.n S.b q.tail (m + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail m)
    {θ' : simpleHGroup T.chain T.n T.b q'.tail (m + 1) →* ℂˣ}
    (hθ' : θ' ∈ simpleCharacters ψF T.chain T.n T.b q'.tail m)
    (hP : (⟨_, θ⟩ : CharacterPair G) = ⟨_, θ'⟩) :
    centralizerLattice S.chain S.b 0 ⊔ S.chain.endFiltration 1 =
      centralizerLattice S.chain T.b 0 ⊔ S.chain.endFiltration 1 := by
  obtain ⟨h₁, -⟩ := hI F V ψF hψ S hS0 hS q m hmS hcS θ hθ
  obtain ⟨h₂, -⟩ := hI F V ψF hψ T hT0 hT q' m hmT hcT θ' hθ'
  have hY₂ := sub_one_mem_of_mem_simpleCharacterIntertwiningFactor T q' hmT hcT
  rw [hc] at hY₂
  exact sup_eq_of_mul_mul_eq S.chain (Langlands.BushnellKutzko.one_mem_simpleCharacterIntertwiningFactor S q m)
    (Langlands.BushnellKutzko.one_mem_simpleCharacterIntertwiningFactor T q' m)
    (sub_one_mem_of_mem_simpleCharacterIntertwiningFactor S q hmS hcS) hY₂
    (h₁.symm.trans ((characterSelfIntertwining_eq_of_pair_eq hP).trans h₂))

/-- **Passing to the first jump.** Let `θ ∈ C(𝔄,m,β)` be computed from the tail `γ :: tail`,
where `r = −k₀(β,𝔄) > m` is finite, `β − γ ∈ 𝔓^{−r}` and `H^{r+1}(β) = H^{r+1}(γ)`. If
simple characters for `γ` restrict to simple characters at index `r`, then the restriction
of `θ` to `H^{r+1}(β)` is a simple character for `γ` at index `r` (as a pair). The defining
twist `ψ_{β−γ}` is trivial on `U^{r+1}(𝔄)`. -/
theorem exists_pair_eq_at_jump (L : LatticeChain 𝒪[F] F V) (ψF : AddChar F ℂ)
    (hψ : IsBKAdditiveCharacter ψF) (n : ℤ) {β γ : A} {tail : List A} {m R : ℕ}
    (hmR : m < R) (hr : finiteCriticalDepth L n β = R)
    (hsub : β - γ ∈ L.endFiltration (-(R : ℤ)))
    (hH : simpleHGroup L n β (γ :: tail) (R + 1) = simpleHGroup L n γ tail (R + 1))
    (hfwd : ∀ j : ℕ, j ≤ R → ∀ θ₀ ∈ simpleCharacters ψF L n γ tail j,
      ∀ h : simpleHGroup L n γ tail (R + 1) ≤ simpleHGroup L n γ tail (j + 1),
        θ₀.comp (Subgroup.inclusion h) ∈ simpleCharacters ψF L n γ tail R)
    {θ : simpleHGroup L n β (γ :: tail) (m + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF L n β (γ :: tail) m) :
    ∃ θ' ∈ simpleCharacters ψF L n γ tail R,
      (⟨simpleHGroup L n β (γ :: tail) (R + 1),
        θ.comp (Subgroup.inclusion
          (simpleHGroup_antitone L n β (γ :: tail) (by omega)))⟩ : CharacterPair G) =
        ⟨simpleHGroup L n γ tail (R + 1), θ'⟩ := by
  have hm : (m : ℤ) < finiteCriticalDepth L n β := by rw [hr]; exact_mod_cast hmR
  simp only [simpleCharacters, ite_eq_left hm] at hθ
  obtain ⟨-, -, θ₀, hθ₀, hagree⟩ := hθ
  have hjR : max m (finiteCriticalDepth L n β / 2).toNat ≤ R := by
    rw [hr]
    omega
  have hle : simpleHGroup L n γ tail (R + 1) ≤
      simpleHGroup L n γ tail (max m (finiteCriticalDepth L n β / 2).toNat + 1) :=
    simpleHGroup_antitone L n γ tail (by omega)
  refine ⟨θ₀.comp (Subgroup.inclusion hle), hfwd _ hjR θ₀ hθ₀ hle, ?_⟩
  refine pair_eq_of_apply hH fun g h₁ h₂ => ?_
  have hgj : g ∈ simpleHGroup L n β (γ :: tail)
      (max m (finiteCriticalDepth L n β / 2).toNat + 1) :=
    simpleHGroup_antitone L n β (γ :: tail) (by omega) h₁
  obtain ⟨h₁', h₂', hv⟩ := hagree ⟨g, hgj⟩
  have hg : g ∈ L.unitFiltration (R + 1) :=
    simpleHGroup_le_unitFiltration L n β (γ :: tail) (R + 1) h₁
  have htw : elementCharacter (traceCharacter ψF) (β - γ) g = 1 :=
    elementCharacter_eq_one_of_depth L ψF hψ hsub (by push_cast; omega) hg
  apply Units.ext
  change (θ ⟨g, h₁'⟩ : ℂ) = (θ₀ ⟨g, h₂'⟩ : ℂ)
  rw [hv]
  change _ * elementCharacter (traceCharacter ψF) (β - γ) g = _
  rw [htw, mul_one]

end CommonPair

end CentralizerResidue

end Langlands.BushnellKutzko

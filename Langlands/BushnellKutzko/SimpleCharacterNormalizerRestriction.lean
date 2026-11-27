import Langlands.BushnellKutzko.SimpleCharacterNormalizerLattice
import Langlands.BushnellKutzko.SimpleCharacterLoweringSets
import Langlands.BushnellKutzko.SimpleCharacterRestrictionHigh

/-! # The normalizer of a restricted simple character (BK93 (3.5.10))

This module states `SimpleCharacterNormalizerRestrictionStatement` (BK93 (3.5.10) with the
normalization of `H^m` used with it in the proof of (3.5.9)), and
`simpleCharacterNormalizerRestrictionReduction` derives it from the restriction statement,
the intertwining and normalizer formulas, and the conjugation formula (3.3.9) of BK93. -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

open StratumEquivalence

universe u v uF uV

/-- **BK93 (3.5.10)**, together with the normalization of `H^m` used with it in the proof of
(3.5.9). Let `[𝔄,n,0,β]` be simple, `m = i + 1` with `m < n` and `m < −k₀(β,𝔄)` (the
`simpleCriticalDepth`, infinite when `β` is scalar), and
`θ ∈ C(𝔄,m−1,β)`. Every `x` normalizing the restriction of `θ` to `H^{m+1}(β,𝔄)` normalizes
`H^m(β,𝔄)`, and `θ(xux⁻¹) = θ(u)` for `u ∈ U^m(𝔅_β)`. -/
def SimpleCharacterNormalizerRestrictionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S : Stratum 𝒪[F] F V), S.r = 0 → S.IsSimple → ∀ q : S.DefiningSequenceChoice,
    ∀ i : ℕ, (i : ℤ) + 1 < S.n →
      (((i + 1 : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b →
    ∀ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail i,
      let H := simpleHGroup S.chain S.n S.b q.tail (i + 1)
      let θ₀ := θ.comp (Subgroup.inclusion (simpleHGroup_antitone S.chain S.n S.b q.tail
        (Nat.le_succ (i + 1))))
      ∀ x ∈ characterNormalizer θ₀,
        x ∈ Subgroup.normalizer (H : Set (Module.End F V)ˣ) ∧
        ∀ (y : (Module.End F V)ˣ) (hy : y ∈ H) (hxy : x * y * x⁻¹ ∈ H),
          y ∈ relativeUnitFiltration S.chain S.b (i + 1) → θ ⟨_, hxy⟩ = θ ⟨y, hy⟩

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type v} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Characters on a subgroup take equal values at equal elements. -/
theorem character_congr {H : Subgroup G} (ζ : H →* ℂˣ) {g₁ g₂ : G} (h : g₁ = g₂)
    (h₁ : g₁ ∈ H) (h₂ : g₂ ∈ H) : ζ ⟨g₁, h₁⟩ = ζ ⟨g₂, h₂⟩ := by
  subst h
  rfl

/-! ### Conjugation by elements of `𝔎(𝔄)` -/

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Conjugation by an element of `𝔎(𝔄)` preserves every `𝔓^k`. -/
theorem LatticeChain.conj_mem_endFiltration_of_mem_stabilizer (L : LatticeChain 𝒪[F] F V)
    {g : G} (hg : g ∈ L.stabilizer) {k : ℤ} {x : A} (hx : x ∈ L.endFiltration k) :
    (g : A) * x * (↑g⁻¹ : A) ∈ L.endFiltration k := by
  set d := L.stabilizerValuation ⟨g, hg⟩ with hd
  have hg' : (g : A) ∈ L.endFiltration d := L.mem_endFiltration.mpr fun i z hz => by
    rw [← L.map_lattice_stabilizer ⟨g, hg⟩ i]
    exact Submodule.mem_map_of_mem hz
  have hgi : (↑g⁻¹ : A) ∈ L.endFiltration (-d) := L.mem_endFiltration.mpr fun i z hz => by
    have h := L.map_lattice_stabilizer ⟨g, hg⟩ (i - d)
    change (L.lattice (i - d)).map ((g : A).restrictScalars 𝒪[F]) = L.lattice (i - d + d) at h
    rw [sub_add_cancel] at h
    rw [← h] at hz
    obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp hz
    change (g : A) y = z at he
    rw [← he, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply, ← sub_eq_add_neg]
    exact hy
  have h := L.mul_mem_endFiltration (L.mul_mem_endFiltration hg' hx) hgi
  rwa [show d + k + -d = k by omega] at h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `𝔎(𝔄)` normalizes every `U^m(𝔄)`. -/
theorem LatticeChain.conj_mem_unitFiltration_of_mem_stabilizer (L : LatticeChain 𝒪[F] F V)
    {g : G} (hg : g ∈ L.stabilizer) {m : ℕ} {u : G} (hu : u ∈ L.unitFiltration m) :
    g * u * g⁻¹ ∈ L.unitFiltration m := by
  obtain ⟨hu0, hui, hu1⟩ := hu
  refine ⟨?_, ?_, ?_⟩
  · rw [L.mem_order_iff_mem_endFiltration] at hu0 ⊢
    simpa using L.conj_mem_endFiltration_of_mem_stabilizer hg hu0
  · rw [L.mem_order_iff_mem_endFiltration] at hui ⊢
    simpa [mul_assoc] using L.conj_mem_endFiltration_of_mem_stabilizer hg hui
  · have h := L.conj_mem_endFiltration_of_mem_stabilizer hg hu1
    have he : (g : A) * ((u : A) - 1) * (↑g⁻¹ : A) = ((g * u * g⁻¹ : G) : A) - 1 := by
      simp [mul_sub, sub_mul]
    rwa [he] at h

/-! ### Normalizing a generated subgroup -/

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- If conjugation by `g` maps a generating set into the generated subgroup, it maps the
generated subgroup into itself. -/
theorem conj_mem_closure_of_forall {C : Set G} {g : G}
    (hC : ∀ h ∈ C, g * h * g⁻¹ ∈ Subgroup.closure C) {h : G} (hh : h ∈ Subgroup.closure C) :
    g * h * g⁻¹ ∈ Subgroup.closure C := by
  have hle : Subgroup.closure C ≤ (Subgroup.closure C).comap (MulAut.conj g).toMonoidHom :=
    (Subgroup.closure_le _).mpr fun x hx => by simpa using hC x hx
  simpa using hle hh

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- An element whose conjugation and inverse conjugation both map a generating set into the
generated subgroup normalizes it. -/
theorem mem_normalizer_closure_of_forall {C : Set G} {g : G}
    (h₁ : ∀ h ∈ C, g * h * g⁻¹ ∈ Subgroup.closure C)
    (h₂ : ∀ h ∈ C, g⁻¹ * h * g⁻¹⁻¹ ∈ Subgroup.closure C) :
    g ∈ Subgroup.normalizer (Subgroup.closure C : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => conj_mem_closure_of_forall h₁ hh,
    fun hh => ?_⟩
  have := conj_mem_closure_of_forall h₂ hh
  simpa [mul_assoc] using this

/-! ### Units close to `1` in `𝔑_{−k}` -/

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- If `g − 1 ∈ 𝔑_{−k} ∩ 𝔓^e` with `e ≥ 0` and `g⁻¹ ∈ 𝔄`, then also
`g⁻¹ − 1 ∈ 𝔑_{−k} ∩ 𝔓^e`. -/
theorem inv_sub_one_mem_adjointLattice (L : LatticeChain 𝒪[F] F V) (β : A) {k e : ℤ}
    (he : 0 ≤ e) {g : G} (hg : (g : A) - 1 ∈ adjointLattice L β (-k))
    (hge : (g : A) - 1 ∈ L.endFiltration e) (hgi : (↑g⁻¹ : A) ∈ L.endFiltration 0) :
    (↑g⁻¹ : A) - 1 ∈ adjointLattice L β (-k) ∧ (↑g⁻¹ : A) - 1 ∈ L.endFiltration e := by
  have hsub : (↑g⁻¹ : A) - 1 = -((↑g⁻¹ : A) * ((g : A) - 1)) := by
    rw [mul_sub, Units.inv_mul, mul_one]
    abel
  have hmem : (↑g⁻¹ : A) - 1 ∈ L.endFiltration e := by
    rw [hsub]
    exact neg_mem (by simpa using L.mul_mem_endFiltration hgi hge)
  refine ⟨⟨L.endFiltration_antitone he hmem, ?_⟩, hmem⟩
  change adjointMap 𝒪[F] β ((↑g⁻¹ : A) - 1) ∈ L.endFiltration (-k)
  have ha : adjointMap 𝒪[F] β ((g : A) - 1) ∈ L.endFiltration (-k) := hg.2
  have e1 : (↑g⁻¹ : A) * (adjointMap 𝒪[F] β ((g : A) - 1)) * (↑g⁻¹ : A) =
      (↑g⁻¹ : A) * β * ((g : A) * (↑g⁻¹ : A)) - ((↑g⁻¹ : A) * (g : A)) * β * (↑g⁻¹ : A) := by
    simp only [adjointMap_apply]
    noncomm_ring
  rw [Units.mul_inv, Units.inv_mul] at e1
  have e2 : adjointMap 𝒪[F] β ((↑g⁻¹ : A) - 1) =
      -((↑g⁻¹ : A) * (adjointMap 𝒪[F] β ((g : A) - 1)) * (↑g⁻¹ : A)) := by
    rw [e1]
    simp only [adjointMap_apply]
    noncomm_ring
  rw [e2]
  refine neg_mem ?_
  have h := L.mul_mem_endFiltration (L.mul_mem_endFiltration hgi ha) hgi
  simpa using h

/-- The additive factor of the conjugation formula vanishes on `U^m(𝔅_β)`: if `g − 1 ∈ 𝔓^e`
with `e ≥ 1`, `g⁻¹ ∈ 𝔄`, `a_β(g − 1) ∈ 𝔓^{−m}`, and `u − 1 ∈ 𝔓^m` commutes with `β`, then
`ψ_{g⁻¹βg − β}(u) = 1`. -/
theorem elementCharacter_conj_sub_eq_one (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) (β : A) {m e : ℤ} (he : 1 ≤ e) {g : G}
    (hge : (g : A) - 1 ∈ L.endFiltration e) (hgi : (↑g⁻¹ : A) ∈ L.endFiltration 0)
    (hga : adjointMap 𝒪[F] β ((g : A) - 1) ∈ L.endFiltration (-m)) {u : G}
    (hu : (u : A) - 1 ∈ L.endFiltration m) (hcomm : β * ((u : A) - 1) = ((u : A) - 1) * β) :
    elementCharacter (traceCharacter ψF) ((↑g⁻¹ : A) * β * (g : A) - β) u = 1 := by
  set a : A := (g : A) - 1 with ha_def
  set c : A := adjointMap 𝒪[F] β a with hc_def
  have hg : (g : A) = a + 1 := by rw [ha_def]; abel
  have hgi1 : (↑g⁻¹ : A) * (g : A) = 1 := Units.inv_mul g
  have hgia : (↑g⁻¹ : A) * a = 1 - (↑g⁻¹ : A) := by
    rw [ha_def, mul_sub, hgi1, mul_one]
  have hsplit : (↑g⁻¹ : A) * β * (g : A) - β = c + -((↑g⁻¹ : A) * a * c) := by
    calc (↑g⁻¹ : A) * β * (g : A) - β = (↑g⁻¹ : A) * (β * (g : A) - (g : A) * β) := by
          rw [mul_sub, ← mul_assoc, ← mul_assoc, hgi1, one_mul]
      _ = (↑g⁻¹ : A) * c := by
          rw [hc_def, adjointMap_apply, hg]
          noncomm_ring
      _ = c + -((↑g⁻¹ : A) * a * c) := by
          rw [hgia]
          noncomm_ring
  rw [hsplit, elementCharacter_add]
  have h1 : elementCharacter (traceCharacter ψF) c u = 1 := by
    rw [elementCharacter_apply, traceCharacter_apply, hc_def, adjointMap_apply]
    have htr : LinearMap.trace F V ((β * a - a * β) * ((u : A) - 1)) = 0 := by
      rw [sub_mul, map_sub, mul_assoc, LinearMap.trace_mul_comm F β (a * ((u : A) - 1)),
        mul_assoc a β, hcomm, ← mul_assoc, sub_self]
    rw [htr, AddChar.map_zero_eq_one]
  have h2 : elementCharacter (traceCharacter ψF) (-((↑g⁻¹ : A) * a * c)) u = 1 := by
    refine elementCharacter_eq_one_of_mem_endFiltration ψF hψ L (j := e + -m) (k := m)
      (by omega) (neg_mem ?_) hu
    have h := L.mul_mem_endFiltration (L.mul_mem_endFiltration hgi hge) hga
    simpa using h
  rw [h1, h2, mul_one]

/-! ### Conjugating the generators of `H^m` -/

/-- Let `k < r = finiteCriticalDepth` and `⌊k/2⌋ + 1 ≤ m`. A unit `g` with `g − 1` and
`g⁻¹ − 1` in `𝔑_{−k}(β,𝔄)` conjugates the generating set `ℌ(β,𝔄) ∩ U^m(𝔄)` of `H^m(β,𝔄)`
into itself. -/
theorem conj_mem_simpleHCarrier (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice)
    (k m : ℕ) (hk : (k : ℤ) < finiteCriticalDepth S.chain S.n S.b) (hkm : k / 2 + 1 ≤ m)
    {g : G} (hg : (g : A) - 1 ∈ adjointLattice S.chain S.b (-(k : ℤ)))
    (hg' : (↑g⁻¹ : A) - 1 ∈ adjointLattice S.chain S.b (-(k : ℤ)))
    {h : G} (hh : h ∈ simpleHCarrier S.chain S.n S.b q.tail m) :
    g * h * g⁻¹ ∈ simpleHCarrier S.chain S.n S.b q.tail m := by
  obtain ⟨hhU, hhH⟩ := hh
  have one0 : (1 : A) ∈ S.chain.endFiltration 0 :=
    (S.chain.mem_order_iff_mem_endFiltration).1 S.chain.order.one_mem
  have hg0 : (g : A) ∈ S.chain.endFiltration 0 := by simpa using add_mem hg.1 one0
  have hgi0 : (↑g⁻¹ : A) ∈ S.chain.endFiltration 0 := by simpa using add_mem hg'.1 one0
  have hgU : g ∈ S.chain.unitFiltration 0 :=
    ⟨(S.chain.mem_order_iff_mem_endFiltration).2 hg0,
      (S.chain.mem_order_iff_mem_endFiltration).2 hgi0, by simpa using hg.1⟩
  refine ⟨S.chain.conj_mem_unitFiltration_of_mem_stabilizer
    (mem_stabilizer_of_mem_unitFiltration S.chain hgU) hhU, ?_⟩
  set a : A := (g : A) - 1 with ha_def
  set a' : A := (↑g⁻¹ : A) - 1 with ha'_def
  set e : A := (h : A) - 1 with he_def
  have heH : e ∈ simpleHLattice S.chain S.n S.b q.tail :=
    sub_mem hhH (one_mem_simpleHLattice S.chain S.n S.b q.tail)
  have hem : e ∈ S.chain.endFiltration m := hhU.2.2
  have hk2 : ((k : ℤ) / 2 + 1) ≤ (m : ℤ) := by omega
  have hek : e ∈ S.chain.endFiltration ((k : ℤ) / 2 + 1) := S.chain.endFiltration_antitone hk2 hem
  have hae := (mul_mem_simpleHLattice_of_mem_adjointLattice S q k hk hg heH hek).1
  set e₁ : A := e + a * e with he₁_def
  have he₁H : e₁ ∈ simpleHLattice S.chain S.n S.b q.tail := add_mem heH hae
  have he₁m : e₁ ∈ S.chain.endFiltration m :=
    add_mem hem (by simpa using S.chain.mul_mem_endFiltration hg.1 hem)
  have he₁a := (mul_mem_simpleHLattice_of_mem_adjointLattice S q k hk hg' he₁H
    (S.chain.endFiltration_antitone hk2 he₁m)).2
  have key : (1 : A) + (e₁ + e₁ * a') =
      (g : A) * (h : A) * (↑g⁻¹ : A) + (1 - (g : A) * (↑g⁻¹ : A)) := by
    rw [he₁_def, ha_def, ha'_def, he_def]
    noncomm_ring
  rw [Units.mul_inv, sub_self, add_zero] at key
  have hval : ((g * h * g⁻¹ : G) : A) = (g : A) * (h : A) * (↑g⁻¹ : A) := by simp
  rw [hval, ← key]
  exact add_mem (one_mem_simpleHLattice S.chain S.n S.b q.tail) (add_mem he₁H he₁a)

/-- Under the hypotheses of `conj_mem_simpleHCarrier`, `g` normalizes `H^m(β,𝔄)`. -/
theorem mem_normalizer_simpleHGroup (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice)
    (k m : ℕ) (hk : (k : ℤ) < finiteCriticalDepth S.chain S.n S.b) (hkm : k / 2 + 1 ≤ m)
    {g : G} (hg : (g : A) - 1 ∈ adjointLattice S.chain S.b (-(k : ℤ)))
    (hg' : (↑g⁻¹ : A) - 1 ∈ adjointLattice S.chain S.b (-(k : ℤ))) :
    g ∈ Subgroup.normalizer (simpleHGroup S.chain S.n S.b q.tail m : Set G) := by
  refine mem_normalizer_closure_of_forall (fun h hh => Subgroup.subset_closure
    (conj_mem_simpleHCarrier S q k m hk hkm hg hg' hh)) (fun h hh => Subgroup.subset_closure
    (conj_mem_simpleHCarrier S q k m hk hkm hg' (by simpa using hg) hh))

/-! ### The normalizer of the restricted character -/

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- An index below `simpleCriticalDepth` and below `n` is below `finiteCriticalDepth`. -/
theorem lt_finiteCriticalDepth_of_lt (L : LatticeChain 𝒪[F] F V) (n : ℤ) (b : A) {k : ℤ}
    (hk : (k : WithTop ℤ) < simpleCriticalDepth L b) (hkn : k < n) :
    k < finiteCriticalDepth L n b := by
  unfold finiteCriticalDepth
  cases hd : simpleCriticalDepth L b with
  | top => simpa using hkn
  | coe d =>
    rw [hd] at hk
    simpa using WithTop.coe_lt_coe.mp hk

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `𝔔^{r−m} 𝔑_{−r} ⊆ 𝔑_{−m} ∩ 𝔓^{r−m}` for `m ≤ r`. -/
theorem centralizerLattice_mul_adjointLattice_le_inf (L : LatticeChain 𝒪[F] F V) (β : A) {r m : ℤ}
    (hmr : m ≤ r) :
    centralizerLattice L β (r - m) * adjointLattice L β (-r) ≤
      adjointLattice L β (-m) ⊓ L.endFiltration (r - m) := by
  apply Submodule.mul_le.mpr
  intro c hc z hz
  have hcz : c * z ∈ L.endFiltration (r - m) := by
    simpa using L.mul_mem_endFiltration hc.1 hz.1
  refine ⟨⟨L.endFiltration_antitone (by omega) hcz, ?_⟩, hcz⟩
  change adjointMap 𝒪[F] β (c * z) ∈ L.endFiltration (-m)
  have hc' : β * c - c * β = 0 := hc.2
  have he : adjointMap 𝒪[F] β (c * z) = c * adjointMap 𝒪[F] β z := by
    simp only [adjointMap_apply]
    rw [mul_sub, ← mul_assoc, sub_eq_zero.mp hc', mul_assoc, mul_assoc]
  rw [he]
  have h := L.mul_mem_endFiltration hc.1 hz.2
  rwa [show r - m + -r = -m by ring] at h

/-- **The outer factor at depth `m`.** Let `θ ∈ C(𝔄,m−1,β)` with `m = i + 1`. Every element
`y` of the outer factor `Y` of BK93 (3.3.2) at depth `m` normalizes `H^m(β,𝔄)` and satisfies
`θ(yuy⁻¹) = θ(u)` for `u ∈ H^m(β,𝔄) ∩ U^m(𝔅_β)`. -/
theorem simpleCharacterIntertwiningFactor_restriction
    (hint : SimpleCharacterIntertwiningStatement.{u, v})
    (hcov : SimpleCharacterCovarianceStatement.{u, v})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum 𝒪[F] F V) (h0 : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    (i : ℕ) (hin : (i : ℤ) + 1 < S.n)
    (hcrit : (((i + 1 : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {θ : simpleHGroup S.chain S.n S.b q.tail (i + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail i) {y : G}
    (hy : y ∈ simpleCharacterIntertwiningFactor S q (i + 1)) :
    y ∈ Subgroup.normalizer (simpleHGroup S.chain S.n S.b q.tail (i + 1) : Set G) ∧
      ∀ (u : G) (hu : u ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1))
        (hyu : y * u * y⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1)),
        u ∈ relativeUnitFiltration S.chain S.b (i + 1) → θ ⟨_, hyu⟩ = θ ⟨u, hu⟩ := by
  have hin' : (i : ℤ) < S.n := by omega
  have hcrit_i : ((i : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b :=
    lt_of_le_of_lt (WithTop.coe_le_coe.mpr (by push_cast; omega)) hcrit
  by_cases hb : elementAlgebra S.b = ⊥
  · have hy1 : y = 1 := by
      unfold simpleCharacterIntertwiningFactor at hy
      rw [ite_eq_left hb] at hy
      exact hy
    subst hy1
    exact ⟨Subgroup.one_mem _, fun u hu hyu _ => character_congr θ (by group) hyu hu⟩
  · set r := finiteCriticalDepth S.chain S.n S.b with hr_def
    have hmr : ((i + 1 : ℕ) : ℤ) < r := lt_finiteCriticalDepth_of_lt S.chain S.n S.b hcrit (by omega)
    have hy' : (y : A) - 1 ∈ centralizerLattice S.chain S.b (r - ((i + 1 : ℕ) : ℤ)) *
        adjointLattice S.chain S.b (-r) ⊔
        simpleJLayer S.chain S.n S.b q.tail (simpleJCutoff r).toNat := by
      unfold simpleCharacterIntertwiningFactor at hy
      rw [ite_eq_right hb] at hy
      exact hy
    obtain ⟨a, ha, w, hw, hsum⟩ := Submodule.mem_sup.mp hy'
    obtain ⟨haN, har⟩ := centralizerLattice_mul_adjointLattice_le_inf S.chain S.b hmr.le ha
    obtain ⟨g, hgU, hg⟩ := S.chain.exists_mem_unitFiltration (n := 1) le_rfl
      (S.chain.endFiltration_antitone (by omega : ((1 : ℕ) : ℤ) ≤ r - ((i + 1 : ℕ) : ℤ)) har)
    have hga : (g : A) - 1 = a := by rw [hg]; abel
    have hgN : (g : A) - 1 ∈ adjointLattice S.chain S.b (-((i + 1 : ℕ) : ℤ)) := hga ▸ haN
    have hgr : (g : A) - 1 ∈ S.chain.endFiltration (r - ((i + 1 : ℕ) : ℤ)) := hga ▸ har
    have hgi0 : (↑g⁻¹ : A) ∈ S.chain.endFiltration 0 :=
      (S.chain.mem_order_iff_mem_endFiltration).1 hgU.2.1
    obtain ⟨hgN', -⟩ := inv_sub_one_mem_adjointLattice S.chain S.b
      (by omega : (0 : ℤ) ≤ r - ((i + 1 : ℕ) : ℤ)) hgN hgr hgi0
    -- the factor `j = y g⁻¹` lies in `J^t`
    have hgiN : (↑g⁻¹ : A) ∈ adjointLattice S.chain S.b (-r) := by
      refine ⟨hgi0, ?_⟩
      change adjointMap 𝒪[F] S.b (↑g⁻¹ : A) ∈ S.chain.endFiltration (-r)
      have h1 : adjointMap 𝒪[F] S.b (↑g⁻¹ : A) = adjointMap 𝒪[F] S.b ((↑g⁻¹ : A) - 1) := by
        simp only [adjointMap_apply]
        noncomm_ring
      rw [h1]
      exact S.chain.endFiltration_antitone (by omega) hgN'.2
    have hwg := mul_mem_simpleJLayer_of_mem_adjointLattice S q (by omega) hw hgiN
    set j : G := y * g⁻¹ with hj_def
    have hyg : (y : A) = (g : A) + w := by
      rw [hg, add_assoc, hsum]
      abel
    have hj1 : (j : A) - 1 = w * (↑g⁻¹ : A) := by
      rw [hj_def, Units.val_mul, hyg, add_mul, Units.mul_inv]
      abel
    have hjY : j ∈ simpleCharacterIntertwiningFactor S q i := by
      unfold simpleCharacterIntertwiningFactor
      rw [ite_eq_right hb]
      show (j : A) - 1 ∈ centralizerLattice S.chain S.b (r - (i : ℤ)) *
        adjointLattice S.chain S.b (-r) ⊔
        simpleJLayer S.chain S.n S.b q.tail (simpleJCutoff r).toNat
      rw [hj1]
      exact Submodule.mem_sup_right hwg
    have hjN := simpleCharacterIntertwiningFactor_subset_normalizer hint ψF hψ S h0 hs q i hin'
      hcrit_i hθ hjY
    -- `g` normalizes `H^m`
    have hgNorm : g ∈ Subgroup.normalizer (simpleHGroup S.chain S.n S.b q.tail (i + 1) : Set G) :=
      mem_normalizer_simpleHGroup S q (i + 1) (i + 1) hmr (by omega) hgN hgN'
    -- the covariance formula at `g`
    have hgY : g ∈ simpleCharacterIntertwiningFactor S q (i + 1) := by
      unfold simpleCharacterIntertwiningFactor
      rw [ite_eq_right hb]
      show (g : A) - 1 ∈ centralizerLattice S.chain S.b (r - ((i + 1 : ℕ) : ℤ)) *
        adjointLattice S.chain S.b (-r) ⊔
        simpleJLayer S.chain S.n S.b q.tail (simpleJCutoff r).toNat
      rw [hga]
      exact Submodule.mem_sup_left ha
    have hcovg := hcov F V ψF hψ S h0 hs q i (i + 1) hin' (by omega) hcrit_i hcrit (by omega) θ hθ g
      (Set.mem_mul.mpr ⟨g, Set.mem_mul.mpr ⟨g, hgY, 1, (centralizerUnitGroup S.b).one_mem,
        mul_one g⟩, 1, simpleCharacterIntertwiningFactor_one_mem S q (i + 1), mul_one g⟩)
    have hyjg : j * g = y := by rw [hj_def]; group
    refine ⟨hyjg ▸ Subgroup.mul_mem _ hjN.1 hgNorm, fun u hu hyu huB => ?_⟩
    have hgu : g * u * g⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1) :=
      (Subgroup.mem_normalizer_iff.mp hgNorm u).mp hu
    have hjgu : j * (g * u * g⁻¹) * j⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1) := by
      have he : j * (g * u * g⁻¹) * j⁻¹ = y * u * y⁻¹ := by rw [hj_def]; group
      rw [he]
      exact hyu
    rw [character_congr θ (show y * u * y⁻¹ = j * (g * u * g⁻¹) * j⁻¹ by rw [hj_def]; group)
      hyu hjgu, hjN.2 ⟨_, hgu⟩ hjgu]
    have hcomm : S.b * ((u : A) - 1) = ((u : A) - 1) * S.b := by
      have h := huB.1
      change S.b * (u : A) = (u : A) * S.b at h
      rw [mul_sub, sub_mul, h, mul_one, one_mul]
    have hψ1 : elementCharacter (traceCharacter ψF) ((↑g⁻¹ : A) * S.b * (g : A) - S.b)
        ((⟨u, hu⟩ : simpleHGroup S.chain S.n S.b q.tail (i + 1)) : G) = 1 :=
      elementCharacter_conj_sub_eq_one ψF hψ S.chain S.b (by omega : (1 : ℤ) ≤ r - ((i + 1 : ℕ) : ℤ)) hgr hgi0
        hgN.2 huB.2.2.2 hcomm
    apply Units.ext
    refine (hcovg ⟨u, hu⟩ hgu).trans ?_
    rw [hψ1, mul_one]

/-- **BK93 (3.5.10)** for a single character, from the restriction, intertwining and
covariance statements. -/
theorem simpleCharacter_normalizer_restriction
    (hrestriction : SimpleCharacterRestrictionStatement.{u, v})
    (hint : SimpleCharacterIntertwiningStatement.{u, v})
    (hcov : SimpleCharacterCovarianceStatement.{u, v})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum 𝒪[F] F V) (h0 : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    (i : ℕ) (hin : (i : ℤ) + 1 < S.n)
    (hcrit : (((i + 1 : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {θ : simpleHGroup S.chain S.n S.b q.tail (i + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail i) {x : G}
    (hx : x ∈ characterNormalizer (θ.comp (Subgroup.inclusion
      (simpleHGroup_antitone S.chain S.n S.b q.tail (Nat.le_succ (i + 1)))))) :
    x ∈ Subgroup.normalizer (simpleHGroup S.chain S.n S.b q.tail (i + 1) : Set G) ∧
      ∀ (y : G) (hy : y ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1))
        (hxy : x * y * x⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1)),
        y ∈ relativeUnitFiltration S.chain S.b (i + 1) → θ ⟨_, hxy⟩ = θ ⟨y, hy⟩ := by
  have hin' : (i : ℤ) < S.n := by omega
  have hcrit_i : ((i : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b :=
    lt_of_le_of_lt (WithTop.coe_le_coe.mpr (by push_cast; omega)) hcrit
  have hθ₀ : θ.comp (Subgroup.inclusion (simpleHGroup_antitone S.chain S.n S.b q.tail
      (Nat.le_succ (i + 1)))) ∈ simpleCharacters ψF S.chain S.n S.b q.tail (i + 1) := by
    rw [← simpleCharacters_restriction_image hrestriction ψF hψ hs (by rw [h0]) q i hin]
    exact ⟨θ, hθ, rfl⟩
  have hN₀ := (hint F V ψF hψ S h0 hs q (i + 1) (by push_cast; omega) hcrit _ hθ₀).2
  rw [hN₀] at hx
  obtain ⟨y, hy, k, hk, rfl⟩ := Set.mem_mul.mp hx
  have hkN : k ∈ characterNormalizer θ := by
    rw [(hint F V ψF hψ S h0 hs q i hin' hcrit_i θ hθ).2]
    exact Set.mem_mul.mpr ⟨1, simpleCharacterIntertwiningFactor_one_mem S q i, k, hk, one_mul k⟩
  obtain ⟨hyN, hyθ⟩ := simpleCharacterIntertwiningFactor_restriction hint hcov ψF hψ S h0 hs q i
    hin hcrit hθ hy
  refine ⟨Subgroup.mul_mem _ hyN hkN.1, fun u hu hxu huB => ?_⟩
  have hku : k * u * k⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1) :=
    (Subgroup.mem_normalizer_iff.mp hkN.1 u).mp hu
  have hkuB : k * u * k⁻¹ ∈ relativeUnitFiltration S.chain S.b (i + 1) :=
    ⟨(centralizerUnitGroup S.b).mul_mem ((centralizerUnitGroup S.b).mul_mem hk.1 huB.1)
      ((centralizerUnitGroup S.b).inv_mem hk.1),
      S.chain.conj_mem_unitFiltration_of_mem_stabilizer hk.2 huB.2⟩
  have hyku : y * (k * u * k⁻¹) * y⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1) := by
    have he : y * (k * u * k⁻¹) * y⁻¹ = y * k * u * (y * k)⁻¹ := by group
    rw [he]
    exact hxu
  rw [character_congr θ (show y * k * u * (y * k)⁻¹ = y * (k * u * k⁻¹) * y⁻¹ by group) hxu hyku,
    hyθ _ hku hyku hkuB]
  exact hkN.2 ⟨u, hu⟩ hku

/-- **BK93 (3.5.10) from its inputs.** The restriction statement (U3), the intertwining and
normalizer formulas (U5), and the conjugation formula (3.3.9) imply
`SimpleCharacterNormalizerRestrictionStatement`. -/
def SimpleCharacterNormalizerRestrictionReductionStatement : Prop :=
  SimpleCharacterRestrictionStatement.{u, v} → SimpleCharacterIntertwiningStatement.{u, v} →
    SimpleCharacterCovarianceStatement.{u, v} → SimpleCharacterNormalizerRestrictionStatement.{u, v}

theorem simpleCharacterNormalizerRestrictionReduction :
    SimpleCharacterNormalizerRestrictionReductionStatement.{u, v} := by
  intro hrestriction hint hcov F _ _ _ _ V _ _ ψF hψ S h0 hs q i hin hcrit θ hθ H θ₀ x hx
  exact simpleCharacter_normalizer_restriction hrestriction hint hcov ψF hψ S h0 hs q i hin hcrit
    hθ hx

end Langlands.BushnellKutzko

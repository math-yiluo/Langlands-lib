import Langlands.BushnellKutzko.LowerBlockSubgroup
import Langlands.BushnellKutzko.UnequalSplitTypeRadical
import Langlands.BushnellKutzko.BlockLatticeCharacter
import Langlands.BushnellKutzko.PairingTransfer
import Langlands.BushnellKutzko.SimpleCharacterNormalizerLattice
import Langlands.BushnellKutzko.UnequalSplitTypeShiftElement
import Langlands.BushnellKutzko.SimpleCharacterLoweringSets
import Langlands.BushnellKutzko.SimpleHGroupSquareZero
import Langlands.BushnellKutzko.StratumEquivalenceResidue

/-! # The transfer across the shallow part of the `(2,1)`-block

For the split type `(H^m, θ ψ_c)`, `m = i + 1`, the subgroup `H_d ⊆ H^m` of elements whose
`(2,1)`-block lies in `𝔓^{m+1}` is enlarged to `H^m` by conjugating with the units
`1 + e₁ y e₂`, `y ∈ 𝔔^{r−m} 𝔑_{−r} + 𝔅`. These lie in `Y_m B^×`, so the conjugation formula
BK93 (3.3.9) computes the conjugate characters, and the orthogonality criterion
`mem_simpleHLayer_succ_of_orthogonal` shows that they separate the cosets of `H_d`. -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The block part `e₁ y e₂` of an element of `𝔑_k` lies in `𝔑_k` when `e₁, e₂ ∈ 𝔅`. -/
theorem block_mem_adjointLattice (L : LatticeChain 𝒪[F] F V) (β : A) {k : ℤ} {e₁ e₂ y : A}
    (he₁B : e₁ ∈ centralizerLattice L β 0) (he₂B : e₂ ∈ centralizerLattice L β 0)
    (hy : y ∈ adjointLattice L β k) : e₁ * y * e₂ ∈ adjointLattice L β k := by
  have hadj : ∀ a b : A, adjointMap 𝒪[F] a b = a * b - b * a := fun _ _ => rfl
  have hc : ∀ e ∈ centralizerLattice L β 0, β * e = e * β := fun e he => by
    have h : adjointMap 𝒪[F] β e = 0 := LinearMap.mem_ker.mp he.2
    rw [hadj] at h
    exact sub_eq_zero.mp h
  refine ⟨mul_mul_mem_endFiltration L he₁B.1 hy.1 he₂B.1 (by ring), ?_⟩
  have hy2 : β * y - y * β ∈ L.endFiltration k := by
    have := hy.2
    rw [SetLike.mem_coe, Submodule.mem_comap, hadj] at this
    exact this
  change adjointMap 𝒪[F] β (e₁ * y * e₂) ∈ L.endFiltration k
  rw [hadj]
  have : β * (e₁ * y * e₂) - e₁ * y * e₂ * β = e₁ * (β * y - y * β) * e₂ := by
    have h1 : β * (e₁ * y * e₂) = e₁ * β * y * e₂ := by
      rw [← hc e₁ he₁B]; noncomm_ring
    have h2 : e₁ * y * e₂ * β = e₁ * y * β * e₂ := by
      rw [mul_assoc (e₁ * y) e₂ β, ← hc e₂ he₂B]; noncomm_ring
    rw [h1, h2]; noncomm_ring
  rw [this]
  exact mul_mul_mem_endFiltration L he₁B.1 hy2 he₂B.1 (by ring)

/-- **Block unipotents from `𝔑_{−m}` normalize `H^m`.** For `[𝔄, n, 0, β]` simple, `m = i + 1`
below the critical depth, complementary idempotents `e₁, e₂ ∈ 𝔅` and `y ∈ 𝔑_{−m}`, the unit
`1 + e₁ y e₂` normalizes `H^m`. -/
theorem blockUnit_mem_normalizer_simpleHGroup (S : Stratum 𝒪[F] F V) (h0 : S.r = 0)
    (hs : S.IsSimple) (q : S.DefiningSequenceChoice) (i : ℕ)
    (hcrit : ((i + 1 : ℕ) : ℤ) < finiteCriticalDepth S.chain S.n S.b) {e₁ e₂ : A}
    (h₂₁ : e₂ * e₁ = 0) (he₁B : e₁ ∈ centralizerLattice S.chain S.b 0)
    (he₂B : e₂ ∈ centralizerLattice S.chain S.b 0) {y : A}
    (hy : y ∈ adjointLattice S.chain S.b (-((i + 1 : ℕ) : ℤ))) :
    blockUnit e₁ e₂ h₂₁ y ∈
      Subgroup.normalizer (simpleHGroup S.chain S.n S.b q.tail (i + 1) : Set G) := by
  set w := e₁ * y * e₂ with hw
  have hwN := block_mem_adjointLattice S.chain S.b he₁B he₂B hy
  have hww : w * w = 0 := by
    rw [hw]
    calc e₁ * y * e₂ * (e₁ * y * e₂) = e₁ * y * (e₂ * e₁) * y * e₂ := by noncomm_ring
      _ = 0 := by rw [h₂₁]; noncomm_ring
  have hleft : ∀ x ∈ simpleHLayer S.chain S.n S.b q.tail (i + 1),
      w * x ∈ simpleHLayer S.chain S.n S.b q.tail (i + 1) ∧
        x * w ∈ simpleHLayer S.chain S.n S.b q.tail (i + 1) := by
    intro x hx
    have hk : ((i + 1 : ℕ) : ℤ) < finiteCriticalDepth S.chain S.n S.b := hcrit
    have hxk : x ∈ S.chain.endFiltration (((i + 1 : ℕ) : ℤ) / 2 + 1) :=
      S.chain.endFiltration_antitone (by omega) hx.2
    obtain ⟨h1, h2⟩ := mul_mem_simpleHLattice_of_mem_adjointLattice S q (i + 1) hk hwN hx.1 hxk
    exact ⟨⟨h1, by simpa using S.chain.mul_mem_endFiltration hwN.1 hx.2⟩,
      ⟨h2, by simpa using S.chain.mul_mem_endFiltration hx.2 hwN.1⟩⟩
  refine mem_normalizer_simpleHGroup_of_sq_eq_zero S h0 hs q (by omega)
    (blockUnit e₁ e₂ h₂₁ y) (blockUnit_val e₁ e₂ h₂₁ y) hww (fun x hx => ?_)
  obtain ⟨h1, h2⟩ := hleft x hx
  exact ⟨h1, h2, (hleft _ h1).2⟩

/-- **The conjugate character under `1 + e₁ y e₂`, `y ∈ 𝔔^{r−m} 𝔑_{−r} + 𝔅`.** For
`ϑ = θ ψ_c` with `c` commuting with `e₁, e₂` and `b = β + c`, the conjugation formula BK93 (3.3.9)
gives `ϑ(g k g⁻¹) ψ_A(e₁ y e₂ (b x − x b)) = ϑ(k)` for `k = 1 + x ∈ H^m`. -/
theorem blockUnit_conj_ratio (S : Stratum 𝒪[F] F V) (h0 : S.r = 0) (hs : S.IsSimple)
    (q : S.DefiningSequenceChoice) (i : ℕ) (hin : (i : ℤ) + 1 < S.n)
    (hcrit : (((i + 1 : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {ψF : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψF)
    {θ : simpleHGroup S.chain S.n S.b q.tail (i + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail i)
    (ϑ : simpleHGroup S.chain S.n S.b q.tail (i + 1) →* ℂˣ) {c : A}
    (hϑ : ∀ h, (ϑ h : ℂ) = (θ h : ℂ) * elementCharacter (traceCharacter ψF) c (h : G))
    {e₁ e₂ : A} (h₂₁ : e₂ * e₁ = 0) (he₁B : e₁ ∈ centralizerLattice S.chain S.b 0)
    (he₂B : e₂ ∈ centralizerLattice S.chain S.b 0) (hc₁ : e₁ * c = c * e₁)
    {y : A} (hy : y ∈ centralizerLattice S.chain S.b
        (finiteCriticalDepth S.chain S.n S.b - ((i + 1 : ℕ) : ℤ)) *
        adjointLattice S.chain S.b (-finiteCriticalDepth S.chain S.n S.b) ⊔
      centralizerLattice S.chain S.b 0)
    (k : simpleHGroup S.chain S.n S.b q.tail (i + 1))
    (hk : blockUnit e₁ e₂ h₂₁ y * (k : G) * (blockUnit e₁ e₂ h₂₁ y)⁻¹ ∈
      simpleHGroup S.chain S.n S.b q.tail (i + 1)) :
    (ϑ ⟨_, hk⟩ : ℂ) * traceCharacter ψF (e₁ * y * e₂ *
      ((S.b + c) * (((k : G) : A) - 1) - (((k : G) : A) - 1) * (S.b + c))) = ϑ k := by
  have hadj : ∀ a b : A, adjointMap 𝒪[F] a b = a * b - b * a := fun _ _ => rfl
  have hcomm : ∀ e ∈ centralizerLattice S.chain S.b 0, S.b * e = e * S.b := fun e he => by
    have h : adjointMap 𝒪[F] S.b e = 0 := LinearMap.mem_ker.mp he.2
    rw [hadj] at h
    exact sub_eq_zero.mp h
  set g := blockUnit e₁ e₂ h₂₁ y with hg
  have hgYB : g ∈ simpleCharacterIntertwiningFactor S q (i + 1) *
      (centralizerUnitGroup S.b : Set G) * simpleCharacterIntertwiningFactor S q (i + 1) := by
    have hYone := simpleCharacterIntertwiningFactor_one_mem S q (i + 1)
    by_cases hb : elementAlgebra S.b = ⊥
    · have hgB : g ∈ centralizerUnitGroup S.b := commute_of_elementAlgebra_eq_bot hb (g : A)
      exact ⟨1 * g, Set.mul_mem_mul hYone hgB, 1, hYone, by simp⟩
    · obtain ⟨y₁, hy₁, y₂, hy₂, hy_eq⟩ := Submodule.mem_sup.mp hy
      have hgsplit : g = blockUnit e₁ e₂ h₂₁ y₁ * blockUnit e₁ e₂ h₂₁ y₂ := by
        apply Units.ext
        rw [hg, ← hy_eq, Units.val_mul, blockUnit_val, blockUnit_val, blockUnit_val]
        calc 1 + e₁ * (y₁ + y₂) * e₂ = 1 + e₁ * y₁ * e₂ + e₁ * y₂ * e₂ +
            e₁ * y₁ * (e₂ * e₁) * y₂ * e₂ := by rw [h₂₁]; noncomm_ring
          _ = _ := by noncomm_ring
      have hY : blockUnit e₁ e₂ h₂₁ y₁ ∈ simpleCharacterIntertwiningFactor S q (i + 1) := by
        unfold simpleCharacterIntertwiningFactor
        rw [ite_eq_right hb]
        have hmem : ((blockUnit e₁ e₂ h₂₁ y₁ : G) : A) - 1 ∈ centralizerLattice S.chain S.b
            (finiteCriticalDepth S.chain S.n S.b - ((i + 1 : ℕ) : ℤ)) *
            adjointLattice S.chain S.b (-finiteCriticalDepth S.chain S.n S.b) := by
          rw [blockUnit_val, add_sub_cancel_left]
          exact mul_mul_mem_centralizer_mul_adjoint S.chain S.b he₁B he₂B hy₁
        exact Submodule.mem_sup_left hmem
      have hB : blockUnit e₁ e₂ h₂₁ y₂ ∈ centralizerUnitGroup S.b := by
        change Commute S.b ((blockUnit e₁ e₂ h₂₁ y₂ : G) : A)
        rw [blockUnit_val]
        have h1 := hcomm e₁ he₁B
        have h2 := hcomm e₂ he₂B
        have h3 := hcomm y₂ hy₂
        change S.b * (1 + e₁ * y₂ * e₂) = (1 + e₁ * y₂ * e₂) * S.b
        rw [mul_add, add_mul, mul_one, one_mul, ← mul_assoc, ← mul_assoc, h1, mul_assoc e₁ S.b y₂, h3,
          ← mul_assoc, mul_assoc (e₁ * y₂) S.b e₂, h2, ← mul_assoc]
      exact ⟨_, Set.mul_mem_mul hY hB, 1, hYone, (mul_one _).trans hgsplit.symm⟩
  have hcrit_i : ((i : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b :=
    lt_of_le_of_lt (WithTop.coe_le_coe.mpr (by push_cast; omega)) hcrit
  have hcov := simpleCharacterCovariance F V ψF hψ S h0 hs q i (i + 1) (by omega) hin hcrit_i hcrit
    (by omega) θ hθ g hgYB
  have hϑcov := characterConjugationRatio.of_twist ψF hcov hϑ
  have h := hϑcov k hk
  rw [h]
  set W := e₁ * y * e₂ with hW
  set b := S.b + c with hbdef
  have hbe₁ : b * e₁ = e₁ * b := by rw [hbdef, add_mul, mul_add, ← hcomm e₁ he₁B, hc₁]
  have hdiff : ((g⁻¹ : G) : A) * b * (g : A) - b = b * W - W * b := by
    rw [hg, blockUnit_inv_val, blockUnit_val, ← hW]
    have hWbW : W * b * W = 0 := by
      rw [hW]
      calc e₁ * y * e₂ * b * (e₁ * y * e₂) =
          e₁ * y * e₂ * (b * e₁) * y * e₂ := by noncomm_ring
        _ = 0 := by rw [hbe₁]; rw [show e₁ * y * e₂ * (e₁ * b) * y * e₂ =
            e₁ * y * (e₂ * e₁) * b * y * e₂ by noncomm_ring, h₂₁]; noncomm_ring
    calc (1 - W) * b * (1 + W) - b = b * W - W * b - W * b * W := by noncomm_ring
      _ = b * W - W * b := by rw [hWbW, sub_zero]
  rw [hdiff, elementCharacter_apply, mul_assoc]
  set x := (((k : G) : A) - 1) with hx
  have htr := trace_mul_commutator b x W
  rw [show traceCharacter ψF ((b * W - W * b) * x) * traceCharacter ψF (W * (b * x - x * b)) = 1 by
    rw [traceCharacter_apply, traceCharacter_apply, htr, map_neg, ← AddChar.map_add_eq_mul,
      add_neg_cancel, AddChar.map_zero_eq_one], mul_one]

/-- **The transfer across the shallow part of the `(2,1)`-block.** Let `[𝔄, n, 0, β]` be simple,
with `θ ∈ C(𝔄, m−1, β)` on `H = H^m` with `m = i + 1` below the critical depth,
`ϑ = θ ψ_c` with `c ∈ 𝔓^{−m}` split by complementary idempotents `e₁, e₂ ∈ 𝔅` for which the
corestricted stratum is split on the `(2,1)`-block (hypothesis `hinj`). Let `M` be a subgroup
of `1 + e₁ A e₂`. A vector outside `rel(M)` on which the elements of `H` with `(2,1)`-block in
`𝔓^{m+1}` act through `ϑ` gives a vector outside `rel(M)` on which `H` acts through `ϑ`. -/
abbrev LowerBlockIsotypicTransferStatement : Prop :=
  ∀ {E : Type*} [Field E] [Algebra F E] [Module E V]
    [IsScalarTower F E V] (S : Stratum 𝒪[F] F V) (_h0 : S.r = 0) (_hs : S.IsSimple)
    (q : S.DefiningSequenceChoice) {βE : E}
    (_hβES : subfieldEmbedding F E V βE = S.b) (_hβE : Algebra.adjoin F ({βE} : Set E) = ⊤)
    (s : TameCorestriction 𝒪[F] F E V) (_hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ S.chain.stabilizer)
    {ψF : AddChar F ℂ} (_hψ : IsBKAdditiveCharacter ψF) (i : ℕ) (_hin : (i : ℤ) + 1 < S.n)
    (_hcrit : (((i + 1 : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {θ : simpleHGroup S.chain S.n S.b q.tail (i + 1) →* ℂˣ}
    (_hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail i)
    (ϑ : simpleHGroup S.chain S.n S.b q.tail (i + 1) →* ℂˣ) {c : A}
    (_hc : c ∈ S.chain.endFiltration (-((i + 1 : ℕ) : ℤ)))
    (_hϑ : ∀ h, (ϑ h : ℂ) = (θ h : ℂ) * elementCharacter (traceCharacter ψF) c (h : G))
    {e₁ e₂ : A} (_hadd : e₁ + e₂ = 1) (h₂₁ : e₂ * e₁ = 0)
    (_he₁B : e₁ ∈ centralizerLattice S.chain S.b 0) (_he₂B : e₂ ∈ centralizerLattice S.chain S.b 0)
    (_he₁₁ : e₁ * e₁ = e₁) (_he₂₂ : e₂ * e₂ = e₂) (_hc₁ : e₁ * c = c * e₁) (_hc₂ : e₂ * c = c * e₂)
    (_hinj : ∀ x : A, x ∈ centralizerLattice S.chain S.b ((i + 1 : ℕ) : ℤ) → e₂ * x * e₁ = x →
      (s (c * x - x * c)).restrictScalars F ∈ S.chain.endFiltration 1 →
      x ∈ S.chain.endFiltration ((i + 1 + 1 : ℕ) : ℤ))
    {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (M : Subgroup G)
    (_hM : M ≤ blockUnipotent e₁ e₂ h₂₁ ⊤) {v : W}
    (_hv : ∀ κ : simpleHGroup S.chain S.n S.b q.tail (i + 1),
      e₂ * (((κ : G) : A) - 1) * e₁ ∈ S.chain.endFiltration ((i + 1 + 1 : ℕ) : ℤ) →
        ρ κ v = (ϑ κ : ℂ) • v)
    (_hvM : v ∉ Jacquet.relations ρ M),
    ∃ w : W, (∀ k : simpleHGroup S.chain S.n S.b q.tail (i + 1), ρ k w = (ϑ k : ℂ) • w) ∧
      w ∉ Jacquet.relations ρ M

theorem exists_isotypic_of_lowerBlock : LowerBlockIsotypicTransferStatement (F := F) (V := V) := by
  intro E _ _ _ _ S h0 hs q βE hβES hβE s hE ψF hψ i hin hcrit θ hθ ϑ c hc hϑ
    e₁ e₂ hadd h₂₁ he₁B he₂B he₁₁ he₂₂ hc₁ hc₂ hinj W _ _ ρ M hM v hv hvM
  classical
  have := S.chain.finiteDimensional
  let H := simpleHGroup S.chain S.n S.b q.tail (i + 1)
  set r := finiteCriticalDepth S.chain S.n S.b with hr
  have hmr : ((i + 1 : ℕ) : ℤ) < r := lt_finiteCriticalDepth_of_lt S.chain S.n S.b hcrit (by omega)
  have hHU : H ≤ S.chain.unitFiltration (i + 1) := simpleHGroup_le_unitFiltration _ _ _ _ _
  have he₁0 := he₁B.1
  have he₂0 := he₂B.1
  set 𝒦 := lowerBlockSubgroup S.chain hadd he₁0 he₂0 H (i + 1) (by omega) hHU with h𝒦
  -- finite index of `𝒦` in `H`
  obtain ⟨k₀, hk₀1, hdeep⟩ := simpleCharacter_trivial_on_deep_units S.chain S.n hψ S.b q.tail i hθ
  set N := max k₀ (i + 2) with hN
  have hNU : (S.chain.unitFiltration N).subgroupOf H ≤ 𝒦.subgroupOf H := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    refine ⟨g.2, ?_⟩
    have hgN : ((g : G) : A) - 1 ∈ S.chain.endFiltration (N : ℤ) := hg.2.2
    have := mul_mul_mem_endFiltration S.chain he₂0 hgN he₁0 (by ring : (0 : ℤ) + N + 0 = N)
    exact S.chain.endFiltration_antitone (by push_cast; omega) this
  have hfin : ((S.chain.unitFiltration N).subgroupOf H).FiniteIndex := by
    obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero (show N ≠ 0 by omega)
    let := S.chain.unitFiltration_finiteIndex_in_one k'
    have hH1 : H ≤ S.chain.unitFiltration 1 := hHU.trans
      (S.chain.unitFiltration_antitone (by omega))
    rw [hk', ← Subgroup.comap_inclusion_subgroupOf hH1]
    infer_instance
  have : (𝒦.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_le hNU
  let : Fintype (H ⧸ 𝒦.subgroupOf H) := Fintype.ofFinite _
  -- the lattice of conjugators and the finite index set
  set Λ := centralizerLattice S.chain S.b (r - ((i + 1 : ℕ) : ℤ)) * adjointLattice S.chain S.b (-r) ⊔
    centralizerLattice S.chain S.b 0 with hΛ
  have hΛN : Λ ≤ adjointLattice S.chain S.b (-((i + 1 : ℕ) : ℤ)) :=
    sup_le ((centralizerLattice_mul_adjointLattice_le_inf S.chain S.b hmr.le).trans inf_le_left)
      (StratumEquivalence.centralizerLattice_le_adjointLattice S.chain S.b _)
  have hΛ0 : Λ ≤ S.chain.endFiltration 0 := hΛN.trans inf_le_left
  set N₀ : ℤ := S.n + 1 with hN₀
  have : Finite (latticeQuotient S.chain Λ N₀) :=
    finite_latticeQuotient S.chain hΛ0 (by have := S.r_lt_n; omega)
  let : Fintype (latticeQuotient S.chain Λ N₀) := Fintype.ofFinite _
  -- the element `b x − x b`
  have hbP : S.b + c ∈ S.chain.endFiltration (-S.n) := by
    refine add_mem (PureApproximation.mem_endFiltration_of_le_valuation S.chain
      (by exact_mod_cast S.valuation_ge)) (S.chain.endFiltration_antitone (by omega) hc)
  have hw : ∀ k : H, (S.b + c) * (((k : G) : A) - 1) - (((k : G) : A) - 1) * (S.b + c) ∈
      S.chain.endFiltration (1 - N₀) := by
    intro k
    have hx : ((k : G) : A) - 1 ∈ S.chain.endFiltration 0 :=
      S.chain.endFiltration_antitone (by positivity) (hHU k.2).2.2
    rw [show 1 - N₀ = -S.n by rw [hN₀]; ring]
    exact sub_mem (by simpa using S.chain.mul_mem_endFiltration hbP hx)
      (by simpa using S.chain.mul_mem_endFiltration hx hbP)
  let Φ : H → AddChar (latticeQuotient S.chain Λ N₀) ℂ := fun k =>
    latticeBlockCharacter S.chain hψ Λ N₀ he₁0 he₂0 (hw k)
  let g : latticeQuotient S.chain Λ N₀ → G := fun p =>
    blockUnit e₁ e₂ h₂₁ ((Quotient.out p : Λ) : A)
  have hgN : ∀ p, g p ∈ Subgroup.normalizer (H : Set G) := fun p =>
    blockUnit_mem_normalizer_simpleHGroup S h0 hs q i hmr h₂₁ he₁B he₂B (hΛN (Quotient.out p).2)
  have hgK : ∀ p, ∀ k ∈ H, g p * k * (g p)⁻¹ ∈ H := fun p k hk =>
    (Subgroup.mem_normalizer_iff.mp (hgN p) k).mp hk
  have hgK' : ∀ p, ∀ k ∈ H, (g p)⁻¹ * k * g p ∈ H := fun p k hk => by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem (hgN p)) k).mp hk
    rwa [inv_inv] at h
  have hΦapp : ∀ (k : H) (p : latticeQuotient S.chain Λ N₀), Φ k p =
      traceCharacter ψF (e₁ * ((Quotient.out p : Λ) : A) * e₂ *
        ((S.b + c) * (((k : G) : A) - 1) - (((k : G) : A) - 1) * (S.b + c))) := by
    intro k p
    rw [← latticeBlockCharacter_mk S.chain hψ Λ N₀ he₁0 he₂0 (hw k)]
    exact congrArg _ (Quotient.out_eq p).symm
  have hratio : ∀ p (k : H), (ϑ ⟨_, hgK p k k.2⟩ : ℂ) * Φ k p = ϑ k := by
    intro p k
    rw [hΦapp]
    exact blockUnit_conj_ratio S h0 hs q i hin hcrit hψ hθ ϑ hϑ h₂₁ he₁B he₂B hc₁
      (Quotient.out p).2 k _
  -- the block identity `tr(e₁ y e₂ w) = tr(y e₂ w e₁)`
  have hcommB : ∀ e ∈ centralizerLattice S.chain S.b 0, S.b * e = e * S.b := fun e he => by
    have h : adjointMap 𝒪[F] S.b e = 0 := LinearMap.mem_ker.mp he.2
    change S.b * e - e * S.b = 0 at h
    exact sub_eq_zero.mp h
  have hblk : ∀ (y : A) (k : H), traceCharacter ψF (e₁ * y * e₂ *
      ((S.b + c) * (((k : G) : A) - 1) - (((k : G) : A) - 1) * (S.b + c))) =
      traceCharacter ψF (y * ((S.b + c) * (e₂ * (((k : G) : A) - 1) * e₁) -
        (e₂ * (((k : G) : A) - 1) * e₁) * (S.b + c))) := by
    intro y k
    set x := ((k : G) : A) - 1
    have hb₁ : (S.b + c) * e₁ = e₁ * (S.b + c) := by
      rw [add_mul, mul_add, ← hcommB e₁ he₁B, hc₁]
    have hb₂ : (S.b + c) * e₂ = e₂ * (S.b + c) := by
      rw [add_mul, mul_add, ← hcommB e₂ he₂B, hc₂]
    rw [traceCharacter_apply, traceCharacter_apply]
    congr 1
    rw [show e₁ * y * e₂ * ((S.b + c) * x - x * (S.b + c)) =
      e₁ * (y * e₂ * ((S.b + c) * x - x * (S.b + c))) by noncomm_ring,
      LinearMap.trace_mul_comm]
    congr 1
    calc y * e₂ * ((S.b + c) * x - x * (S.b + c)) * e₁ =
        y * ((e₂ * (S.b + c)) * x * e₁ - e₂ * x * ((S.b + c) * e₁)) := by noncomm_ring
      _ = _ := by rw [← hb₂, hb₁]; noncomm_ring
  have hrad : ∀ k : H, Φ k = 0 ↔ (k : G) ∈ 𝒦 := by
    intro k
    have hxH : ((k : G) : A) - 1 ∈ simpleHLayer S.chain S.n S.b q.tail (i + 1) :=
      (simpleHGroup_mem_iff_of_pos S h0 hs q (by omega)).mp k.2
    set x₂₁ := e₂ * (((k : G) : A) - 1) * e₁ with hx₂₁
    have hx21H : x₂₁ ∈ simpleHLayer S.chain S.n S.b q.tail (i + 1) :=
      (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q (i + 1) he₁B
        (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q (i + 1) he₂B hxH).1).2
    have hx2121 : e₂ * x₂₁ * e₁ = x₂₁ := by
      rw [hx₂₁]
      calc e₂ * (e₂ * (((k : G) : A) - 1) * e₁) * e₁ =
          (e₂ * e₂) * (((k : G) : A) - 1) * (e₁ * e₁) := by noncomm_ring
        _ = _ := by rw [he₂₂, he₁₁]
    have hiff : Φ k = 0 ↔ ∀ y ∈ Λ, traceCharacter ψF (y * ((S.b + c) * x₂₁ - x₂₁ * (S.b + c))) = 1 := by
      constructor
      · intro h y hy
        have := AddChar.ext_iff.mp h (Submodule.Quotient.mk ⟨y, hy⟩)
        rw [latticeBlockCharacter_mk, AddChar.zero_apply, hblk] at this
        exact this
      · intro h
        ext p
        obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ p
        rw [AddChar.zero_apply]
        change latticeBlockCharacter S.chain hψ Λ N₀ he₁0 he₂0 (hw k)
          (Submodule.Quotient.mk ⟨y, hy⟩) = 1
        rw [latticeBlockCharacter_mk, hblk]
        exact h y hy
    rw [hiff]
    constructor
    · intro h
      have hH2 := mem_simpleHLayer_succ_of_orthogonal S h0 hs q hβES hβE s hE hψ i hmr hc he₁B
        he₂B he₁₁ he₂₂ hinj hx21H hx2121 (fun y hy => h y (Submodule.mem_sup_left hy))
        (fun y hy => h y (Submodule.mem_sup_right hy))
      exact ⟨k.2, hH2.2⟩
    · rintro ⟨-, hk21⟩ y hy
      have hyN := hΛN hy
      have hby : (S.b + c) * y - y * (S.b + c) ∈ S.chain.endFiltration (-((i + 1 : ℕ) : ℤ)) := by
        have h1 : S.b * y - y * S.b ∈ S.chain.endFiltration (-((i + 1 : ℕ) : ℤ)) := hyN.2
        have h2 : c * y - y * c ∈ S.chain.endFiltration (-((i + 1 : ℕ) : ℤ)) :=
          sub_mem (by simpa using S.chain.mul_mem_endFiltration hc hyN.1)
            (by simpa using S.chain.mul_mem_endFiltration hyN.1 hc)
        rw [show (S.b + c) * y - y * (S.b + c) = (S.b * y - y * S.b) + (c * y - y * c) by
          noncomm_ring]
        exact add_mem h1 h2
      rw [traceCharacter_apply, trace_mul_commutator, ← traceCharacter_apply]
      refine traceCharacter_eq_one S.chain hψ (neg_mem ?_)
      exact S.chain.endFiltration_antitone (by push_cast; omega)
        (S.chain.mul_mem_endFiltration hby hk21)
  have hgM : ∀ p, ∀ m ∈ M, (g p)⁻¹ * m * (g p)⁻¹⁻¹ ∈ M := by
    intro p m hm
    have hc' : g p * m = m * g p := blockUnipotent_commute
      (blockUnit_mem h₂₁ he₁₁ he₂₂ _) (hM hm)
    rw [inv_inv, mul_assoc, ← hc', ← mul_assoc, inv_mul_cancel, one_mul]
    exact hm
  exact Jacquet.exists_isotypic_not_mem_relations_of_addChar ρ M ϑ g Φ hgK hgK' hratio hrad hgM
    (fun κ hκ => hv κ hκ.2) hvM

end Langlands.BushnellKutzko.SplitBlocks

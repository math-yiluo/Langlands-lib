import Langlands.BushnellKutzko.CentralizerGradedScalar
import Langlands.BushnellKutzko.TameCorestrictionKernel
import Langlands.BushnellKutzko.FundamentalStratum

/-! # Residue data of two fields with the same graded centralizers

Let `E₁`, `E₂` be fields finite over `F` acting on `V`, with `E_i^×` normalizing the
`𝔬_F`-lattice chain `𝓛`. Write `𝔓^t = 𝓛.endFiltration t` and `𝔔_i^t = 𝔓^t ∩ End_{E_i}(V)`,
and assume `𝔔₁^t + 𝔓^{t+1} = 𝔔₂^t + 𝔓^{t+1}` for every `t ∈ ℤ` (`GradedEq`). Then

* `𝔬_{E₁} + 𝔓 = 𝔬_{E₂} + 𝔓` (`exists_integer_sub_mem`);
* there are prime elements `ϖ_i` of `E_i` with `ϖ₂ ∈ ϖ₁ U¹(𝔄)` (`exists_primeElement_congr`);
* there are tame corestrictions `s_i` with `s₁(x) ≡ s₂(x)` modulo `𝔓^{t+1}` for `x ∈ 𝔓^t`
  (`exists_tameCorestriction_congr`).
-/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

namespace GradedCentralizer

open StratumEquivalence

universe uF uV uE uE'

section OneField

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]
  {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]

/-- Elements of `E` act `E`-linearly. -/
theorem embedding_mem_fieldCommutant (a : E) : subfieldEmbedding F E V a ∈ fieldCommutant E := by
  intro b v
  rw [subfieldEmbedding_apply, subfieldEmbedding_apply, smul_smul, smul_smul, mul_comm]

/-- Elements of `E` commute with `E`-linear endomorphisms. -/
theorem embedding_mul_comm {x : Module.End F V} (hx : x ∈ fieldCommutant E) (a : E) :
    subfieldEmbedding F E V a * x = x * subfieldEmbedding F E V a := by
  ext v
  rw [Module.End.mul_apply, Module.End.mul_apply, subfieldEmbedding_apply,
    subfieldEmbedding_apply]
  exact (hx a v).symm

/-- An `E`-linear endomorphism, as an element of `End_E(V)`. -/
def fieldCommutantEnd {y : Module.End F V} (hy : y ∈ fieldCommutant E) : Module.End E V where
  toFun := y
  map_add' := y.map_add
  map_smul' := fun a w => hy a w

omit [Algebra F E] [IsScalarTower F E V] in
theorem restrictScalars_fieldCommutantEnd [Algebra F E] [IsScalarTower F E V]
    {y : Module.End F V} (hy : y ∈ fieldCommutant E) :
    (fieldCommutantEnd hy).restrictScalars F = y :=
  rfl

/-- The restriction of scalars of an element of `End_E(V)` is `E`-linear. -/
theorem restrictScalars_mem_fieldCommutant (b : Module.End E V) :
    b.restrictScalars F ∈ fieldCommutant E :=
  fun a v => b.map_smul a v

omit [ValuativeRel F] in
theorem restrictScalars_smul (c : E) (f : Module.End E V) :
    (c • f).restrictScalars F = subfieldEmbedding F E V c * f.restrictScalars F :=
  LinearMap.ext fun _ => rfl

variable (𝓛 : LatticeChain 𝒪[F] F V)

local notation "P" => 𝓛.endFiltration

/-- The identity does not lower the lattice chain. -/
theorem one_notMem_endFiltration_one : (1 : Module.End F V) ∉ P 1 := by
  intro h
  apply (𝓛.lattice_succ_lt 0).not_ge
  intro v hv
  exact h 0 v hv

variable (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)

/-- A nonzero element of `E` lies in `𝔓^{d}` for its shift `d`. -/
theorem embedding_mem_endFiltration_shift {a : E} (ha : a ≠ 0) :
    subfieldEmbedding F E V a ∈ P (shift 𝓛 hE a) := by
  intro i v hv
  rw [subfieldEmbedding_apply]
  exact (smul_mem_shift_iff 𝓛 hE ha i v).mpr hv

/-- A nonzero element of `E` lies in `𝔓^{d}` for its shift `d`, but not in `𝔓^{d+1}`. -/
theorem embedding_notMem_endFiltration_shift_add_one [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [FiniteDimensional F V] {a : E} (ha : a ≠ 0) :
    subfieldEmbedding F E V a ∉ P (shift 𝓛 hE a + 1) := by
  obtain ⟨n, w, k, c, hw, hu⟩ := exists_basis_depth_zero 𝓛 hE
  intro h
  apply (hu.smul 𝓛 hE ha).2
  have h2 := h 0 (c • w k) hu.1
  rw [subfieldEmbedding_apply, ← add_assoc] at h2
  exact h2

include hE in
/-- Integers of `E` lie in `𝔄`. -/
theorem embedding_mem_order {a : E} (ha : a ∈ subfieldIntegers F E) :
    subfieldEmbedding F E V a ∈ P 0 := by
  by_cases h0 : a = 0
  · rw [h0, map_zero]
    exact zero_mem _
  exact 𝓛.endFiltration_antitone (shift_nonneg_of_mem 𝓛 hE ha)
    (embedding_mem_endFiltration_shift 𝓛 hE h0)

/-- A unit multiple of a tame corestriction is a tame corestriction. -/
def unitSmul (u : (subfieldIntegers F E)ˣ) (s : TameCorestriction 𝒪[F] F E V) :
    TameCorestriction 𝒪[F] F E V where
  toFun x := ((u : subfieldIntegers F E) : E) • s x
  map_zero' := by simp only [map_zero, smul_zero]
  map_add' x y := by simp only [map_add, smul_add]
  map_mul_left b x := by
    rw [show s (b.restrictScalars F * x) = b * s x from s.map_mul_left b x, mul_smul_comm]
  map_mul_right x b := by
    rw [show s (x * b.restrictScalars F) = s x * b from s.map_mul_right x b, smul_mul_assoc]
  image_order 𝓛' h𝓛' := by
    have hs := s.image_order 𝓛' h𝓛'
    have hemb (c : subfieldIntegers F E) :
        subfieldEmbedding F E V (c : E) ∈ 𝓛'.order :=
      embedding_mem_order 𝓛' h𝓛' c.2
    ext b
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : s x ∈ s.toFun '' (𝓛'.order : Set (Module.End F V)) := ⟨x, hx, rfl⟩
      rw [hs] at h1
      change (((u : subfieldIntegers F E) : E) • s x).restrictScalars F ∈ 𝓛'.order
      rw [restrictScalars_smul]
      exact 𝓛'.order.mul_mem (hemb _) h1
    · intro hb
      have h1 : (((u⁻¹ : (subfieldIntegers F E)ˣ) : subfieldIntegers F E) : E) • b ∈
          {b : Module.End E V | b.restrictScalars F ∈ 𝓛'.order} := by
        change ((_ : E) • b).restrictScalars F ∈ 𝓛'.order
        rw [restrictScalars_smul]
        exact 𝓛'.order.mul_mem (hemb _) hb
      rw [← hs] at h1
      obtain ⟨x, hx, hxb⟩ := h1
      refine ⟨x, hx, ?_⟩
      change ((u : subfieldIntegers F E) : E) • s x = b
      rw [show s x = _ from hxb, smul_smul, ← Subalgebra.coe_mul, Units.mul_inv,
        Subalgebra.coe_one, one_smul]

theorem restrictScalars_unitSmul (u : (subfieldIntegers F E)ˣ)
    (s : TameCorestriction 𝒪[F] F E V) (x : Module.End F V) :
    ((unitSmul u s) x).restrictScalars F =
      subfieldEmbedding F E V ((u : subfieldIntegers F E) : E) * (s x).restrictScalars F :=
  LinearMap.ext fun _ => rfl

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

include hE in
/-- Elements of `𝔭_E` lie in `𝔓`. -/
theorem embedding_mem_endFiltration_one [FiniteDimensional F E] {ϖ : subfieldIntegers F E}
    (hϖ : Irreducible ϖ) {x : subfieldIntegers F E} (hx : x ∈ subfieldMaximalIdeal F E) :
    subfieldEmbedding F E V (x : E) ∈ P 1 := by
  by_cases h0 : x = 0
  · rw [h0, ZeroMemClass.coe_zero, map_zero]
    exact zero_mem _
  have hx0 : (x : E) ≠ 0 := fun h => h0 (Subtype.ext h)
  exact 𝓛.endFiltration_antitone ((mem_maximalIdeal_iff 𝓛 hE hϖ h0).mp hx)
    (embedding_mem_endFiltration_shift 𝓛 hE hx0)

variable [FiniteDimensional F V]

include hE in
/-- Tame corestrictions preserve the filtration steps. -/
theorem restrictScalars_mem
    (s : TameCorestriction 𝒪[F] F E V) {n : ℤ} {x : Module.End F V} (hx : x ∈ P n) :
    (s x).restrictScalars F ∈ P n := by
  have h := (tameCorestriction F V E).2.2 s 𝓛 hE n
  exact (Set.ext_iff.mp h _).mp ⟨x, hx, rfl⟩

include hE in
/-- Tame corestrictions map each filtration step onto its `E`-linear part. -/
theorem exists_eq
    (s : TameCorestriction 𝒪[F] F E V) {n : ℤ} {b : Module.End E V}
    (hb : b.restrictScalars F ∈ P n) : ∃ x ∈ P n, s x = b := by
  have h := (tameCorestriction F V E).2.2 s 𝓛 hE n
  exact (Set.ext_iff.mp h b).mpr hb

end OneField

theorem maximalIdealInField_add {F : Type uF} [Field F] [ValuativeRel F] {x y : F}
    (hx : x ∈ maximalIdealInField 𝒪[F] F) (hy : y ∈ maximalIdealInField 𝒪[F] F) :
    x + y ∈ maximalIdealInField 𝒪[F] F := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨s, hs, rfl⟩ := hy
  exact ⟨r + s, add_mem hr hs, map_add _ r s⟩

section TwoFields

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (𝓛 : LatticeChain 𝒪[F] F V)
  {E₁ : Type uE} [Field E₁] [Algebra F E₁] [Module E₁ V] [IsScalarTower F E₁ V]
  {E₂ : Type uE'} [Field E₂] [Algebra F E₂] [Module E₂ V] [IsScalarTower F E₂ V]

local notation "P" => 𝓛.endFiltration
local notation "A" => Module.End F V

variable (E₁ E₂) in
/-- The graded centralizers `𝔔_i^t = 𝔓^t ∩ End_{E_i}(V)` agree modulo `𝔓^{t+1}` for every
`t` (BK94 (5.8)). -/
def GradedEq : Prop :=
  ∀ t : ℤ, P t ⊓ fieldCommutant E₁ ⊔ P (t + 1) = P t ⊓ fieldCommutant E₂ ⊔ P (t + 1)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V] in
theorem GradedEq.symm (h : GradedEq 𝓛 E₁ E₂) : GradedEq 𝓛 E₂ E₁ :=
  fun t => (h t).symm

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V] in
/-- An element of `𝔓^d` commuting with `End_{E₁}(V)` commutes with `𝔔₂^j` modulo
`𝔓^{d+j+1}`. -/
theorem commutator_mem (h : GradedEq 𝓛 E₁ E₂) {x : A} {d : ℤ} (hx : x ∈ P d)
    (hcx : ∀ z ∈ fieldCommutant E₁, x * z = z * x) {j : ℤ} {y : A} (hyP : y ∈ P j)
    (hyE : y ∈ fieldCommutant E₂) : x * y - y * x ∈ P (d + j + 1) := by
  have hy : y ∈ P j ⊓ fieldCommutant E₂ ⊔ P (j + 1) := Submodule.mem_sup_left ⟨hyP, hyE⟩
  rw [← h j] at hy
  obtain ⟨z, hz, p, hp, rfl⟩ := Submodule.mem_sup.mp hy
  have e : x * (z + p) - (z + p) * x = (x * z - z * x) + (x * p - p * x) := by noncomm_ring
  rw [e, hcx z hz.2, sub_self, zero_add]
  refine sub_mem ?_ ?_
  · have := 𝓛.mul_mem_endFiltration hx hp
    rwa [show d + (j + 1) = d + j + 1 by ring] at this
  · have := 𝓛.mul_mem_endFiltration hp hx
    rwa [show j + 1 + d = d + j + 1 by ring] at this

variable (hE₁ : ∀ a : E₁ˣ, subfieldUnits F E₁ V a ∈ 𝓛.stabilizer)
  (hE₂ : ∀ a : E₂ˣ, subfieldUnits F E₂ V a ∈ 𝓛.stabilizer)

include hE₁ hE₂ in
/-- **BK94 (5.2)(i).** Every integer of `E₁` is congruent modulo `𝔓` to an integer of `E₂`. -/
theorem exists_integer_sub_mem [FiniteDimensional F E₂] (h : GradedEq 𝓛 E₁ E₂) {a : E₁}
    (ha : a ∈ subfieldIntegers F E₁) :
    ∃ b ∈ subfieldIntegers F E₂,
      subfieldEmbedding F E₁ V a - subfieldEmbedding F E₂ V b ∈ P 1 := by
  have hea := embedding_mem_order 𝓛 hE₁ ha
  have hm : subfieldEmbedding F E₁ V a ∈ P 0 ⊓ fieldCommutant E₁ ⊔ P (0 + 1) :=
    Submodule.mem_sup_left ⟨hea, embedding_mem_fieldCommutant a⟩
  rw [h 0] at hm
  obtain ⟨c, hc, p, hp, hcp⟩ := Submodule.mem_sup.mp hm
  have hc' : c = subfieldEmbedding F E₁ V a - p := by rw [← hcp]; abel
  have hcomm : ∀ (j : ℤ) (y : A), y ∈ P j → y ∈ fieldCommutant E₂ →
      c * y - y * c ∈ P (j + 1) := by
    intro j y hyP hyE
    have h1 := commutator_mem 𝓛 h hea (fun z hz => embedding_mul_comm hz a) hyP hyE
    rw [zero_add] at h1
    have e : c * y - y * c = (subfieldEmbedding F E₁ V a * y - y * subfieldEmbedding F E₁ V a) -
        (p * y - y * p) := by
      rw [hc']; noncomm_ring
    rw [e]
    refine sub_mem h1 (sub_mem ?_ ?_)
    · have := 𝓛.mul_mem_endFiltration hp hyP
      rwa [show (0 : ℤ) + 1 + j = j + 1 by ring] at this
    · have := 𝓛.mul_mem_endFiltration hyP hp
      rwa [show j + (0 + 1) = j + 1 by ring] at this
  obtain ⟨b, hb, hcb⟩ := exists_integer_sub_mem_of_commutator 𝓛 hE₂ hc.1 hcomm
  refine ⟨b, hb, ?_⟩
  have e : subfieldEmbedding F E₁ V a - subfieldEmbedding F E₂ V b =
      (c - subfieldEmbedding F E₂ V b) + p := by rw [← hcp]; abel
  rw [e]
  exact add_mem hcb (by simpa using hp)

include hE₁ hE₂ in
/-- **BK94 (5.2)(ii).** There are prime elements `ϖ_i` of `E_i` with `ϖ₂ ∈ ϖ₁ U¹(𝔄)`. -/
theorem exists_primeElement_congr [FiniteDimensional F E₁] [FiniteDimensional F E₂]
    (h : GradedEq 𝓛 E₁ E₂) :
    ∃ (π₁ : RingPrimeElement (subfieldIntegers F E₁))
      (π₂ : RingPrimeElement (subfieldIntegers F E₂)),
      ∃ u ∈ 𝓛.unitFiltration 1,
        subfieldEmbedding F E₂ V (π₂.1 : E₂) = subfieldEmbedding F E₁ V (π₁.1 : E₁) * (u : A) := by
  have := subfieldIntegers_isDiscreteValuationRing F E₁
  have := subfieldIntegers_isDiscreteValuationRing F E₂
  obtain ⟨ϖ₁, hϖ₁⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E₁)
  obtain ⟨ϖ₂, hϖ₂⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E₂)
  have hϖ₁0 : (ϖ₁ : E₁) ≠ 0 := fun h0 => hϖ₁.ne_zero (Subtype.ext h0)
  have hϖ₂0 : (ϖ₂ : E₂) ≠ 0 := fun h0 => hϖ₂.ne_zero (Subtype.ext h0)
  set d := shift 𝓛 hE₁ (ϖ₁ : E₁) with hd
  have hd₂ : shift 𝓛 hE₂ (ϖ₂ : E₂) = d :=
    (shift_uniformizer_eq_of_sup_eq 𝓛 hE₁ hE₂ (by have h0 := h 0; rw [zero_add] at h0; exact h0) hϖ₁ hϖ₂).symm
  set ϖe₁ := subfieldEmbedding F E₁ V (ϖ₁ : E₁) with hϖe₁def
  set ϖi₁ := subfieldEmbedding F E₁ V (ϖ₁ : E₁)⁻¹ with hϖi₁def
  set ϖe₂ := subfieldEmbedding F E₂ V (ϖ₂ : E₂) with hϖe₂def
  have hϖe₁ : ϖe₁ ∈ P d := embedding_mem_endFiltration_shift 𝓛 hE₁ hϖ₁0
  have hϖi₁ : ϖi₁ ∈ P (-d) := by
    have := embedding_mem_endFiltration_shift 𝓛 hE₁ (inv_ne_zero hϖ₁0)
    rwa [shift_inv 𝓛 hE₁ hϖ₁0] at this
  have hϖe₂ : ϖe₂ ∈ P d := hd₂ ▸ embedding_mem_endFiltration_shift 𝓛 hE₂ hϖ₂0
  have hϖe₂n : ϖe₂ ∉ P (d + 1) := hd₂ ▸ embedding_notMem_endFiltration_shift_add_one 𝓛 hE₂ hϖ₂0
  have hϖϖ : ϖe₁ * ϖi₁ = 1 := by rw [← map_mul, mul_inv_cancel₀ hϖ₁0, map_one]
  -- Decompose `ϖe₂ = z + p` with `z ∈ 𝔔₁^d` and `p ∈ 𝔓^{d+1}`.
  have hm : ϖe₂ ∈ P d ⊓ fieldCommutant E₂ ⊔ P (d + 1) :=
    Submodule.mem_sup_left ⟨hϖe₂, embedding_mem_fieldCommutant _⟩
  rw [← h d] at hm
  obtain ⟨z, hz, p, hp, hzp⟩ := Submodule.mem_sup.mp hm
  set b₁ := ϖi₁ * z with hb₁def
  have hb₁ : b₁ ∈ P 0 := by
    have := 𝓛.mul_mem_endFiltration hϖi₁ hz.1
    rwa [neg_add_cancel] at this
  have hcomm : ∀ (j : ℤ) (y : A), y ∈ P j → y ∈ fieldCommutant E₁ →
      b₁ * y - y * b₁ ∈ P (j + 1) := by
    intro j y hyP hyE
    have hzc : z * y - y * z ∈ P (d + j + 1) := by
      have hz' : z = ϖe₂ - p := by rw [← hzp]; abel
      have h1 := commutator_mem 𝓛 h.symm hϖe₂ (fun w hw => embedding_mul_comm hw _) hyP hyE
      have e : z * y - y * z = (ϖe₂ * y - y * ϖe₂) - (p * y - y * p) := by
        rw [hz']; noncomm_ring
      rw [e]
      refine sub_mem h1 (sub_mem ?_ ?_)
      · have := 𝓛.mul_mem_endFiltration hp hyP
        rwa [show d + 1 + j = d + j + 1 by ring] at this
      · have := 𝓛.mul_mem_endFiltration hyP hp
        rwa [show j + (d + 1) = d + j + 1 by ring] at this
    have hc : ϖi₁ * y = y * ϖi₁ := embedding_mul_comm hyE _
    have e : b₁ * y - y * b₁ = ϖi₁ * (z * y - y * z) := by
      rw [hb₁def, mul_sub, ← mul_assoc y, ← hc, mul_assoc, mul_assoc]
    rw [e]
    have := 𝓛.mul_mem_endFiltration hϖi₁ hzc
    rwa [show -d + (d + j + 1) = j + 1 by ring] at this
  obtain ⟨a, ha, hba⟩ := exists_integer_sub_mem_of_commutator 𝓛 hE₁ hb₁ hcomm
  set ea := subfieldEmbedding F E₁ V a with headef
  have hdiff : ϖe₂ - ϖe₁ * ea ∈ P (d + 1) := by
    have e : ϖe₂ - ϖe₁ * ea = ϖe₁ * (b₁ - ea) + p := by
      rw [← hzp, hb₁def, mul_sub, ← mul_assoc, hϖϖ, one_mul]
      abel
    rw [e]
    refine add_mem ?_ hp
    have := 𝓛.mul_mem_endFiltration hϖe₁ hba
    rwa [show d + 1 = d + 1 by ring] at this
  -- `a` is a unit of `𝔬_{E₁}`.
  have hau : IsUnit (⟨a, ha⟩ : subfieldIntegers F E₁) := by
    by_contra hnu
    have hmax : (⟨a, ha⟩ : subfieldIntegers F E₁) ∈ subfieldMaximalIdeal F E₁ := by
      rw [subfieldMaximalIdeal_eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hnu
    have h1 : ea ∈ P 1 := embedding_mem_endFiltration_one 𝓛 hE₁ hϖ₁ hmax
    have h2 := 𝓛.mul_mem_endFiltration hϖe₁ h1
    apply hϖe₂n
    have := add_mem hdiff h2
    rwa [sub_add_cancel] at this
  have ha0 : a ≠ 0 := fun h0 => hau.ne_zero (Subtype.ext h0)
  have hsa : shift 𝓛 hE₁ a = 0 := by
    have := shift_unit 𝓛 hE₁ hau.unit
    rwa [IsUnit.unit_spec] at this
  let π₁ : RingPrimeElement (subfieldIntegers F E₁) :=
    ⟨ϖ₁ * ⟨a, ha⟩, mul_ne_zero hϖ₁.ne_zero hau.ne_zero, by
      rw [Ideal.span_singleton_mul_right_unit hau, ← hϖ₁.maximalIdeal_eq,
        IsLocalRing.ringJacobson_eq_maximalIdeal]⟩
  let π₂ : RingPrimeElement (subfieldIntegers F E₂) :=
    ⟨ϖ₂, hϖ₂.ne_zero, by
      rw [← hϖ₂.maximalIdeal_eq, IsLocalRing.ringJacobson_eq_maximalIdeal]⟩
  have hπE : ((π₁.1 : subfieldIntegers F E₁) : E₁) = (ϖ₁ : E₁) * a := rfl
  have hπ0 : (ϖ₁ : E₁) * a ≠ 0 := mul_ne_zero hϖ₁0 ha0
  have hsπ : shift 𝓛 hE₁ ((ϖ₁ : E₁) * a) = d := by
    rw [shift_mul 𝓛 hE₁ hϖ₁0 ha0, hsa, add_zero]
  have hw : subfieldEmbedding F E₁ V ((ϖ₁ : E₁) * a)⁻¹ ∈ P (-d) := by
    have := embedding_mem_endFiltration_shift 𝓛 hE₁ (inv_ne_zero hπ0)
    rwa [shift_inv 𝓛 hE₁ hπ0, hsπ] at this
  have hemb : subfieldEmbedding F E₁ V ((ϖ₁ : E₁) * a) = ϖe₁ * ea := map_mul _ _ _
  have hx : subfieldEmbedding F E₁ V ((ϖ₁ : E₁) * a)⁻¹ * (ϖe₂ - ϖe₁ * ea) ∈ P 1 := by
    have := 𝓛.mul_mem_endFiltration hw hdiff
    rwa [show -d + (d + 1) = 1 by ring] at this
  obtain ⟨u, hu, hux⟩ := 𝓛.exists_mem_unitFiltration (n := 1) le_rfl (by rw [Nat.cast_one]; exact hx)
  refine ⟨π₁, π₂, u, hu, ?_⟩
  change ϖe₂ = subfieldEmbedding F E₁ V ((ϖ₁ : E₁) * a) * (u : A)
  rw [hux, mul_add, mul_one, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hπ0, map_one, one_mul,
    hemb, add_sub_cancel]

include hE₁ hE₂ in
/-- The values of two tame corestrictions on `x ∈ 𝔓^t` lie in `𝔓^{t+1}` simultaneously. -/
theorem restrictScalars_mem_of_graded (h : GradedEq 𝓛 E₁ E₂)
    (s₁ : TameCorestriction 𝒪[F] F E₁ V) (s₂ : TameCorestriction 𝒪[F] F E₂ V) {t : ℤ}
    {x : A} (hx : x ∈ P t) (h1 : (s₁ x).restrictScalars F ∈ P (t + 1)) :
    (s₂ x).restrictScalars F ∈ P (t + 1) := by
  rw [show t + 1 = 1 - -t by ring] at h1 ⊢
  rw [TameCorestriction.restrictScalars_mem_endFiltration_iff_trace s₁ 𝓛 hE₁] at h1
  rw [TameCorestriction.restrictScalars_mem_endFiltration_iff_trace s₂ 𝓛 hE₂]
  intro y hyP hyE
  have hy : y ∈ P (-t) ⊓ fieldCommutant E₂ ⊔ P (-t + 1) := Submodule.mem_sup_left ⟨hyP, hyE⟩
  rw [← h (-t)] at hy
  obtain ⟨z, hz, p, hp, rfl⟩ := Submodule.mem_sup.mp hy
  rw [mul_add, map_add]
  refine maximalIdealInField_add (h1 z hz.1 hz.2) (𝓛.trace_mem_maximalIdealInField ?_)
  have := 𝓛.mul_mem_endFiltration hx hp
  rwa [show t + (-t + 1) = 1 by ring] at this

include hE₁ hE₂ in
/-- If `s₁(x₀) = 1`, then `s₂(x) ≡ s₂(x₀) s₁(x)` modulo `𝔓^{t+1}` for `x ∈ 𝔓^t`. -/
theorem sub_mul_mem_of_eq_one (h : GradedEq 𝓛 E₁ E₂)
    (s₁ : TameCorestriction 𝒪[F] F E₁ V) (s₂ : TameCorestriction 𝒪[F] F E₂ V) {x₀ : A}
    (hx₀ : x₀ ∈ P 0) (h1 : s₁ x₀ = 1) {t : ℤ} {x : A} (hx : x ∈ P t) :
    (s₂ x).restrictScalars F - (s₂ x₀).restrictScalars F * (s₁ x).restrictScalars F ∈
      P (t + 1) := by
  set w := (s₁ x).restrictScalars F with hwdef
  have hwt : w ∈ P t := restrictScalars_mem 𝓛 hE₁ s₁ hx
  have hw : w ∈ P t ⊓ fieldCommutant E₁ ⊔ P (t + 1) :=
    Submodule.mem_sup_left ⟨hwt, restrictScalars_mem_fieldCommutant _⟩
  rw [h t] at hw
  obtain ⟨z, hz, p, hp, hzp⟩ := Submodule.mem_sup.mp hw
  have hker : s₁ (x - x₀ * w) = 0 := by
    rw [map_sub, show s₁ (x₀ * w) = s₁ x₀ * s₁ x from s₁.map_mul_right x₀ (s₁ x), h1, one_mul,
      sub_self]
  have hxw : x - x₀ * w ∈ P t := by
    refine sub_mem hx ?_
    have := 𝓛.mul_mem_endFiltration hx₀ hwt
    rwa [zero_add] at this
  have h2 : (s₂ (x - x₀ * w)).restrictScalars F ∈ P (t + 1) :=
    restrictScalars_mem_of_graded 𝓛 hE₁ hE₂ h s₁ s₂ hxw (by rw [hker]; exact zero_mem _)
  have hx₀p : x₀ * p ∈ P (t + 1) := by
    have := 𝓛.mul_mem_endFiltration hx₀ hp
    rwa [zero_add] at this
  have h3 : (s₂ (x₀ * p)).restrictScalars F ∈ P (t + 1) := restrictScalars_mem 𝓛 hE₂ s₂ hx₀p
  have h4 : s₂ (x₀ * z) = s₂ x₀ * fieldCommutantEnd hz.2 :=
    s₂.map_mul_right x₀ (fieldCommutantEnd hz.2)
  have hsx : s₂ x = s₂ (x - x₀ * w) + s₂ (x₀ * z) + s₂ (x₀ * p) := by
    rw [← map_add, ← map_add, ← hzp, mul_add]
    congr 1
    abel
  have key : (s₂ x).restrictScalars F = (s₂ (x - x₀ * w)).restrictScalars F +
      (s₂ x₀).restrictScalars F * z + (s₂ (x₀ * p)).restrictScalars F := by
    rw [hsx, h4]
    exact LinearMap.ext fun _ => rfl
  have e : (s₂ x).restrictScalars F - (s₂ x₀).restrictScalars F * w =
      ((s₂ (x - x₀ * w)).restrictScalars F + (s₂ (x₀ * p)).restrictScalars F) -
        (s₂ x₀).restrictScalars F * p := by
    rw [key, ← hzp]
    noncomm_ring
  rw [e]
  refine sub_mem (add_mem h2 h3) ?_
  have := 𝓛.mul_mem_endFiltration (restrictScalars_mem 𝓛 hE₂ s₂ hx₀) hp
  rwa [zero_add] at this

include hE₁ hE₂ in
/-- If `s₁(x₀) = 1`, then `s₂(x₀)` commutes with `𝔔₂^j` modulo `𝔓^{j+1}`. -/
theorem commutator_mem_of_eq_one (h : GradedEq 𝓛 E₁ E₂)
    (s₁ : TameCorestriction 𝒪[F] F E₁ V) (s₂ : TameCorestriction 𝒪[F] F E₂ V) {x₀ : A}
    (hx₀ : x₀ ∈ P 0) (h1 : s₁ x₀ = 1) {j : ℤ} {y : A} (hyP : y ∈ P j)
    (hyE : y ∈ fieldCommutant E₂) :
    (s₂ x₀).restrictScalars F * y - y * (s₂ x₀).restrictScalars F ∈ P (j + 1) := by
  have e : (s₂ x₀).restrictScalars F * y - y * (s₂ x₀).restrictScalars F =
      (s₂ (x₀ * y - y * x₀)).restrictScalars F := by
    rw [map_sub, show s₂ (x₀ * y) = s₂ x₀ * fieldCommutantEnd hyE from
        s₂.map_mul_right x₀ (fieldCommutantEnd hyE),
      show s₂ (y * x₀) = fieldCommutantEnd hyE * s₂ x₀ from
        s₂.map_mul_left (fieldCommutantEnd hyE) x₀]
    exact LinearMap.ext fun _ => rfl
  rw [e]
  have hc : x₀ * y - y * x₀ ∈ P j := by
    refine sub_mem ?_ ?_
    · have := 𝓛.mul_mem_endFiltration hx₀ hyP
      rwa [zero_add] at this
    · have := 𝓛.mul_mem_endFiltration hyP hx₀
      rwa [add_zero] at this
  refine restrictScalars_mem_of_graded 𝓛 hE₁ hE₂ h s₁ s₂ hc ?_
  have hy : y ∈ P j ⊓ fieldCommutant E₂ ⊔ P (j + 1) := Submodule.mem_sup_left ⟨hyP, hyE⟩
  rw [← h j] at hy
  obtain ⟨z, hz, p, hp, hzp⟩ := Submodule.mem_sup.mp hy
  have e2 : x₀ * y - y * x₀ = (x₀ * z - z * x₀) + (x₀ * p - p * x₀) := by
    rw [← hzp]; noncomm_ring
  have hz0 : s₁ (x₀ * z - z * x₀) = 0 := by
    rw [map_sub, show s₁ (x₀ * z) = s₁ x₀ * fieldCommutantEnd hz.2 from
        s₁.map_mul_right x₀ (fieldCommutantEnd hz.2),
      show s₁ (z * x₀) = fieldCommutantEnd hz.2 * s₁ x₀ from
        s₁.map_mul_left (fieldCommutantEnd hz.2) x₀, h1, one_mul, mul_one, sub_self]
  rw [e2, map_add, hz0, zero_add]
  refine restrictScalars_mem 𝓛 hE₁ s₁ (sub_mem ?_ ?_)
  · have := 𝓛.mul_mem_endFiltration hx₀ hp
    rwa [zero_add] at this
  · have := 𝓛.mul_mem_endFiltration hp hx₀
    rwa [add_zero] at this

include hE₁ hE₂ in
/-- **BK94 (5.2)(iii).** There are tame corestrictions `s_i` relative to `E_i/F` with
`s₁(x) ≡ s₂(x)` modulo `𝔓^{t+1}` for every `x ∈ 𝔓^t`. -/
theorem exists_tameCorestriction_congr [FiniteDimensional F E₂] (h : GradedEq 𝓛 E₁ E₂) :
    ∃ (s₁ : TameCorestriction 𝒪[F] F E₁ V) (s₂ : TameCorestriction 𝒪[F] F E₂ V),
      ∀ (t : ℤ), ∀ x ∈ P t,
        (s₁ x).restrictScalars F - (s₂ x).restrictScalars F ∈ P (t + 1) := by
  have := subfieldIntegers_isDiscreteValuationRing F E₂
  obtain ⟨s₁⟩ := (tameCorestriction F V E₁).1
  obtain ⟨s₂⟩ := (tameCorestriction F V E₂).1
  obtain ⟨x₀, hx₀, hs₁⟩ := exists_eq 𝓛 hE₁ s₁ (n := 0) (b := 1) 𝓛.order.one_mem
  obtain ⟨x₀', hx₀', hs₂⟩ := exists_eq 𝓛 hE₂ s₂ (n := 0) (b := 1) 𝓛.order.one_mem
  set b := (s₂ x₀).restrictScalars F with hbdef
  have hb : b ∈ P 0 := restrictScalars_mem 𝓛 hE₂ s₂ hx₀
  obtain ⟨a, ha, hba⟩ := exists_integer_sub_mem_of_commutator 𝓛 hE₂ hb
    (fun j y hyP hyE => commutator_mem_of_eq_one 𝓛 hE₁ hE₂ h s₁ s₂ hx₀ hs₁ hyP hyE)
  -- `a` is a unit of `𝔬_{E₂}`.
  have hau : IsUnit (⟨a, ha⟩ : subfieldIntegers F E₂) := by
    by_contra hnu
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E₂)
    have hmax : (⟨a, ha⟩ : subfieldIntegers F E₂) ∈ subfieldMaximalIdeal F E₂ := by
      rw [subfieldMaximalIdeal_eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hnu
    have hb1 : b ∈ P 1 := by
      have := add_mem hba (embedding_mem_endFiltration_one 𝓛 hE₂ hϖ hmax)
      rwa [sub_add_cancel] at this
    have hA := sub_mul_mem_of_eq_one 𝓛 hE₂ hE₁ h.symm s₂ s₁ hx₀' hs₂ (t := 0) hx₀
    rw [hs₁] at hA
    have h2 : (s₁ x₀').restrictScalars F * b ∈ P (0 + 1) :=
      𝓛.mul_mem_endFiltration (restrictScalars_mem 𝓛 hE₁ s₁ hx₀') hb1
    have h3 := add_mem hA h2
    rw [sub_add_cancel] at h3
    change (1 : Module.End F V) ∈ P (0 + 1) at h3
    rw [zero_add] at h3
    exact one_notMem_endFiltration_one 𝓛 h3
  set u := hau.unit with hudef
  refine ⟨s₁, unitSmul u⁻¹ s₂, fun t x hx => ?_⟩
  have hA := sub_mul_mem_of_eq_one 𝓛 hE₁ hE₂ h s₁ s₂ hx₀ hs₁ hx
  have hux : ((u : subfieldIntegers F E₂) : E₂) = a := by
    rw [hudef, IsUnit.unit_spec]
  set ea := subfieldEmbedding F E₂ V a with headef
  set ei := subfieldEmbedding F E₂ V (((u⁻¹ : (subfieldIntegers F E₂)ˣ) :
    subfieldIntegers F E₂) : E₂) with heidef
  have hei : ei ∈ P 0 := embedding_mem_order 𝓛 hE₂ (u⁻¹ : (subfieldIntegers F E₂)ˣ).1.2
  have heiea : ei * ea = 1 := by
    rw [heidef, headef, ← hux, ← map_mul, ← Subalgebra.coe_mul, Units.inv_mul,
      Subalgebra.coe_one, map_one]
  rw [restrictScalars_unitSmul]
  set w := (s₁ x).restrictScalars F with hwdef
  set v := (s₂ x).restrictScalars F with hvdef
  have e : w - ei * v = ei * ((ea - b) * w - (v - b * w)) := by
    have : ei * ((ea - b) * w - (v - b * w)) = ei * ea * w - ei * v := by noncomm_ring
    rw [this, heiea, one_mul]
  rw [e]
  have hw := restrictScalars_mem 𝓛 hE₁ s₁ hx
  have h1 : (ea - b) * w ∈ P (t + 1) := by
    have hab : ea - b ∈ P 1 := by
      rw [← neg_sub]
      exact neg_mem hba
    have := 𝓛.mul_mem_endFiltration hab hw
    rwa [add_comm] at this
  have := 𝓛.mul_mem_endFiltration hei (sub_mem h1 hA)
  rwa [zero_add] at this

end TwoFields

end GradedCentralizer

end Langlands.BushnellKutzko

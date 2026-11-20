import Langlands.BushnellKutzko.RefinementCore
import Langlands.BushnellKutzko.SubfieldValuationShifts
import Langlands.BushnellKutzko.ElementFieldInvariants

/-! # Ramification index and residue degree from approximation

Let `K` and `K'` be fields acting on `V` whose units normalize the chain `𝓛`. If the images of
`K` and `K'` in `A = End_F(V)` approximate each other at every level of the filtration
`𝔓^t = 𝓛.endFiltration t`, then `e(K|F) = e(K'|F)` and `f(K|F) = f(K'|F)`.

The ramification index is read off from the shift of a uniformizer: the shifts of the units of
`K` are the multiples of the shift `d_K` of a uniformizer, and `d_K · e(K|F)` is the period of
the chain. The residue degree is the length of the image of `𝔬_K` in `𝔓^0/𝔓^1`.
-/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uK uK'

section Invariants

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)
  {K : Type uK} [Field K] [Algebra F K] [Module K V] [IsScalarTower F K V]
  (hK : ∀ a : Kˣ, subfieldUnits F K V a ∈ 𝓛.stabilizer)
  {K' : Type uK'} [Field K'] [Algebra F K'] [Module K' V] [IsScalarTower F K' V]
  (hK' : ∀ a : K'ˣ, subfieldUnits F K' V a ∈ 𝓛.stabilizer)

local notation "P" => 𝓛.endFiltration

/-- A unit of `K` acts in `𝔓^k` exactly when `k` is at most its shift. -/
theorem subfieldEmbedding_unit_mem_iff (a : Kˣ) (k : ℤ) :
    subfieldEmbedding F K V (a : K) ∈ P k ↔ k ≤ (𝓛.fieldShift K hK a).toAdd :=
  subfieldEmbedding_mem_iff_le 𝓛 (fun i _ => 𝓛.mem_lattice_fieldShift K hK a i) k

include hK hK' in
/-- If `K` is approximated by `K'`, every shift of a unit of `K` is a shift of a unit of `K'`. -/
theorem exists_fieldShift_eq_of_approx
    (h : Approx 𝓛 (Set.range (subfieldEmbedding F K V)) (Set.range (subfieldEmbedding F K' V)))
    (a : Kˣ) : ∃ b : K'ˣ, (𝓛.fieldShift K' hK' b).toAdd = (𝓛.fieldShift K hK a).toAdd := by
  set d := (𝓛.fieldShift K hK a).toAdd with hd
  have hA : subfieldEmbedding F K V (a : K) ∈ P d :=
    (subfieldEmbedding_unit_mem_iff 𝓛 hK a d).mpr le_rfl
  have hA1 : subfieldEmbedding F K V (a : K) ∉ P (d + 1) := fun h1 =>
    absurd ((subfieldEmbedding_unit_mem_iff 𝓛 hK a (d + 1)).mp h1) (by omega)
  obtain ⟨_, ⟨y, rfl⟩, hY⟩ := h _ ⟨a, rfl⟩ d hA
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero, sub_zero] at hY
    exact hA1 hY
  refine ⟨Units.mk0 y hy0, ?_⟩
  have hyd : subfieldEmbedding F K' V y ∈ P d := by
    have := sub_mem hA (𝓛.endFiltration_antitone (by omega) hY)
    rwa [sub_sub_cancel] at this
  have hyd1 : subfieldEmbedding F K' V y ∉ P (d + 1) := by
    intro h1
    apply hA1
    have := add_mem hY h1
    rwa [sub_add_cancel] at this
  have e1 := (subfieldEmbedding_unit_mem_iff 𝓛 hK' (Units.mk0 y hy0) d).mp hyd
  have e2 := mt (subfieldEmbedding_unit_mem_iff 𝓛 hK' (Units.mk0 y hy0) (d + 1)).mpr hyd1
  omega

section LocalField

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

include hK in
/-- An element of `K` acting in `𝔄 = 𝔓^0` is integral. -/
theorem mem_subfieldIntegers_of_mem (a : K) (ha : subfieldEmbedding F K V a ∈ P 0) :
    a ∈ subfieldIntegers F K := by
  by_cases h0 : a = 0
  · rw [h0]
    exact zero_mem _
  have := 𝓛.finiteDimensional_subfield K
  have := subfieldIntegers_isDiscreteValuationRing F K
  have := subfieldIntegers_isFractionRing F K
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F K)
  obtain ⟨n, u, hu⟩ := subfieldUnit_factorization K hϖ (Units.mk0 a h0)
  have hs := 𝓛.fieldShift_eq_mul_of_factorization K hK hϖ.ne_zero hu
  have hpos : 0 < (𝓛.fieldShift K hK (subfieldIntegerUnit K hϖ.ne_zero)).toAdd :=
    𝓛.fieldShift_uniformizer_pos K hK hϖ
  have hnn : 0 ≤ (𝓛.fieldShift K hK (Units.mk0 a h0)).toAdd :=
    (subfieldEmbedding_unit_mem_iff 𝓛 hK _ 0).mp (by rwa [Units.val_mk0])
  have hn : 0 ≤ n := by
    by_contra hn
    push Not at hn
    have : (𝓛.fieldShift K hK (subfieldIntegerUnit K hϖ.ne_zero)).toAdd * n < 0 :=
      mul_neg_of_pos_of_neg hpos hn
    omega
  lift n to ℕ using hn
  have hval := congrArg (fun z : Kˣ => (z : K)) hu
  simp only [Units.val_mk0, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val,
    subfieldIntegerUnit_val] at hval
  rw [hval]
  exact mul_mem (u : subfieldIntegers F K).2 (pow_mem ϖ.2 n)

include hK in
/-- An integer of `K` lies in `𝔭_K` exactly when it acts in `𝔓^1`. -/
theorem mem_subfieldMaximalIdeal_iff (a : subfieldIntegers F K) :
    a ∈ subfieldMaximalIdeal F K ↔ subfieldEmbedding F K V (a : K) ∈ P 1 := by
  have := 𝓛.finiteDimensional_subfield K
  have := subfieldIntegers_isDiscreteValuationRing F K
  have := subfieldIntegers_isFractionRing F K
  rw [subfieldMaximalIdeal_eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hna
    by_cases h0 : (a : K) = 0
    · rw [h0, map_zero]
      exact zero_mem _
    apply (subfieldEmbedding_unit_mem_iff 𝓛 hK (Units.mk0 (a : K) h0) 1).mpr
    have hnn := 𝓛.fieldShift_nonneg_of_integral K hK (Units.mk0 (a : K) h0) a.2
    by_contra hlt
    have hz : (𝓛.fieldShift K hK (Units.mk0 (a : K) h0)).toAdd = 0 := by omega
    obtain ⟨u, hu⟩ := 𝓛.exists_integerUnit_of_fieldShift_zero K hK hz
    apply hna
    have hval := congrArg (fun z : Kˣ => (z : K)) hu
    simp only [Units.val_mk0] at hval
    have : a = (u : subfieldIntegers F K) := Subtype.ext hval
    rw [this]
    exact u.isUnit
  · intro h1 hunit
    obtain ⟨u, rfl⟩ := hunit
    have hz := 𝓛.fieldShift_integerUnit K hK u
    have := (subfieldEmbedding_unit_mem_iff 𝓛 hK
      (Units.map (algebraMap (subfieldIntegers F K) K).toMonoidHom u) 1).mp h1
    change 1 ≤ (𝓛.fieldShift K hK
      (Units.map (algebraMap (subfieldIntegers F K) K).toMonoidHom u)).toAdd at this
    omega

include hK hK' in
/-- Fields approximating each other have the same ramification index. -/
theorem subfieldRamificationIndex_eq_of_approx
    (h : Approx 𝓛 (Set.range (subfieldEmbedding F K V)) (Set.range (subfieldEmbedding F K' V)))
    (h' : Approx 𝓛 (Set.range (subfieldEmbedding F K' V)) (Set.range (subfieldEmbedding F K V))) :
    subfieldRamificationIndex F K = subfieldRamificationIndex F K' := by
  have := 𝓛.finiteDimensional_subfield K
  have := subfieldIntegers_isDiscreteValuationRing F K
  have := subfieldIntegers_isFractionRing F K
  have := 𝓛.finiteDimensional_subfield K'
  have := subfieldIntegers_isDiscreteValuationRing F K'
  have := subfieldIntegers_isFractionRing F K'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F K)
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F K')
  set d := (𝓛.fieldShift K hK (subfieldIntegerUnit K hϖ.ne_zero)).toAdd with hd
  set d' := (𝓛.fieldShift K' hK' (subfieldIntegerUnit K' hϖ'.ne_zero)).toAdd with hd'
  have hpos : 0 < d := 𝓛.fieldShift_uniformizer_pos K hK hϖ
  have hpos' : 0 < d' := 𝓛.fieldShift_uniformizer_pos K' hK' hϖ'
  have hdvd : d' ∣ d := by
    obtain ⟨b, hb⟩ := exists_fieldShift_eq_of_approx 𝓛 hK hK' h (subfieldIntegerUnit K hϖ.ne_zero)
    obtain ⟨n, u, hu⟩ := subfieldUnit_factorization K' hϖ' b
    have := 𝓛.fieldShift_eq_mul_of_factorization K' hK' hϖ'.ne_zero hu
    exact ⟨n, hb.symm.trans this⟩
  have hdvd' : d ∣ d' := by
    obtain ⟨b, hb⟩ := exists_fieldShift_eq_of_approx 𝓛 hK' hK h'
      (subfieldIntegerUnit K' hϖ'.ne_zero)
    obtain ⟨n, u, hu⟩ := subfieldUnit_factorization K hϖ b
    have := 𝓛.fieldShift_eq_mul_of_factorization K hK hϖ.ne_zero hu
    exact ⟨n, hb.symm.trans this⟩
  have hdd : d = d' := le_antisymm (Int.le_of_dvd hpos' hdvd') (Int.le_of_dvd hpos hdvd)
  have he : d * (subfieldRamificationIndex F K : ℤ) = 𝓛.period :=
    𝓛.fieldShift_uniformizer_mul_ramification K hK hϖ
  have he' : d' * (subfieldRamificationIndex F K' : ℤ) = 𝓛.period :=
    𝓛.fieldShift_uniformizer_mul_ramification K' hK' hϖ'
  rw [← hdd] at he'
  exact_mod_cast mul_left_cancel₀ hpos.ne' (he.trans he'.symm)

/-- The quotient `𝔓^0/𝔓^1` as an `𝔬_F`-module. -/
abbrev residueQuotient : Type uV :=
  ↥(P 0) ⧸ (P 1).comap (P 0).subtype

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hK in
/-- Integers of `K` act in `𝔄 = 𝔓^0`. -/
theorem subfieldEmbedding_integer_mem (a : subfieldIntegers F K) :
    subfieldEmbedding F K V (a : K) ∈ P 0 := by
  by_cases h0 : (a : K) = 0
  · rw [h0, map_zero]
    exact zero_mem _
  exact (subfieldEmbedding_unit_mem_iff 𝓛 hK (Units.mk0 (a : K) h0) 0).mpr
    (𝓛.fieldShift_nonneg_of_integral K hK (Units.mk0 (a : K) h0) a.2)

/-- The action of `𝔬_K` in `𝔓^0`. -/
def integerAction : subfieldIntegers F K →ₗ[𝒪[F]] ↥(P 0) where
  toFun a := ⟨subfieldEmbedding F K V (a : K), subfieldEmbedding_integer_mem 𝓛 hK a⟩
  map_add' a b := by
    apply Subtype.ext
    simp
  map_smul' c a := by
    apply Subtype.ext
    ext v
    change subfieldEmbedding F K V ((c • a : subfieldIntegers F K) : K) v =
      (c : F) • subfieldEmbedding F K V (a : K) v
    rw [subfieldEmbedding_apply, subfieldEmbedding_apply, Subalgebra.coe_smul,
      ← algebraMap_smul F (c : F) ((a : K) • v), ← smul_assoc, Algebra.smul_def]
    congr 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, Algebra.smul_def]
    rfl

/-- The residue map `𝔬_K → 𝔓^0/𝔓^1`. -/
def residueAction : subfieldIntegers F K →ₗ[𝒪[F]] residueQuotient 𝓛 :=
  ((P 1).comap (P 0).subtype).mkQ ∘ₗ integerAction 𝓛 hK

theorem residueAction_apply (a : subfieldIntegers F K) :
    residueAction 𝓛 hK a =
      Submodule.Quotient.mk ⟨subfieldEmbedding F K V (a : K), subfieldEmbedding_integer_mem 𝓛 hK a⟩ :=
  rfl

theorem ker_residueAction :
    LinearMap.ker (residueAction 𝓛 hK) = (subfieldMaximalIdeal F K).restrictScalars 𝒪[F] := by
  ext a
  rw [LinearMap.mem_ker, residueAction_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap, Submodule.subtype_apply, Submodule.restrictScalars_mem,
    mem_subfieldMaximalIdeal_iff 𝓛 hK]

include hK' in
theorem range_residueAction_le
    (h : Approx 𝓛 (Set.range (subfieldEmbedding F K V)) (Set.range (subfieldEmbedding F K' V))) :
    LinearMap.range (residueAction 𝓛 hK) ≤ LinearMap.range (residueAction 𝓛 hK') := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨_, ⟨y, rfl⟩, hY⟩ := h _ ⟨(a : K), rfl⟩ 0 (subfieldEmbedding_integer_mem 𝓛 hK a)
  have hy0 : subfieldEmbedding F K' V y ∈ P 0 := by
    have := sub_mem (subfieldEmbedding_integer_mem 𝓛 hK a) (𝓛.endFiltration_antitone (by omega) hY)
    rwa [sub_sub_cancel] at this
  refine ⟨⟨y, mem_subfieldIntegers_of_mem 𝓛 hK' y hy0⟩, ?_⟩
  rw [residueAction_apply, residueAction_apply, Submodule.Quotient.eq, Submodule.mem_comap]
  have := neg_mem hY
  rwa [neg_sub] at this

/-- The residue ring of `K` is isomorphic to the image of `𝔬_K` in `𝔓^0/𝔓^1`. -/
def residueRingEquivRange :
    subfieldResidueRing F K ≃ₗ[𝒪[F]] LinearMap.range (residueAction 𝓛 hK) :=
  (Submodule.Quotient.restrictScalarsEquiv 𝒪[F] (subfieldMaximalIdeal F K)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_residueAction 𝓛 hK).symm).trans
      (residueAction 𝓛 hK).quotKerEquivRange)

include hK hK' in
/-- Fields approximating each other have the same residue degree. -/
theorem subfieldResidueDegree_eq_of_approx
    (h : Approx 𝓛 (Set.range (subfieldEmbedding F K V)) (Set.range (subfieldEmbedding F K' V)))
    (h' : Approx 𝓛 (Set.range (subfieldEmbedding F K' V)) (Set.range (subfieldEmbedding F K V))) :
    subfieldResidueDegree F K = subfieldResidueDegree F K' := by
  have hr : LinearMap.range (residueAction 𝓛 hK) = LinearMap.range (residueAction 𝓛 hK') :=
    le_antisymm (range_residueAction_le 𝓛 hK hK' h) (range_residueAction_le 𝓛 hK' hK h')
  unfold subfieldResidueDegree
  rw [(residueRingEquivRange 𝓛 hK).length_eq, (residueRingEquivRange 𝓛 hK').length_eq,
    (LinearEquiv.ofEq _ _ hr).length_eq]

end LocalField

end Invariants

end Langlands.BushnellKutzko

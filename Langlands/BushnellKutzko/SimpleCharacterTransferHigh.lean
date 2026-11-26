import Langlands.BushnellKutzko.SimpleCharacterTransferTrace
import Langlands.BushnellKutzko.SimpleCharacterTransferComparison
import Langlands.BushnellKutzko.CorestrictionLatticeDual
import Mathlib.RingTheory.Trace.Defs

/-! # Trace characters at the high-index cutoff -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

private theorem traceCharacter_eq_one_of_mem (L : LatticeChain 𝒪[F] F V)
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) {x : A} (hx : x ∈ L.endFiltration 1) :
    traceCharacter ψF x = 1 := by
  obtain ⟨a, ha, heq⟩ := L.trace_mem_maximalIdealInField hx
  rw [traceCharacter_apply, ← heq]
  exact hψ.1 a ha

/-- On a filtration step strictly beyond half the level of the element, the
trace formula defines a character. -/
def highElementCharacter (L : LatticeChain 𝒪[F] F V) (ψF : AddChar F ℂ)
    (hψ : IsBKAdditiveCharacter ψF) (n : ℤ) (k : ℕ) (hk : n < 2 * (k : ℤ))
    (β : A) (hβ : β ∈ L.endFiltration (-n)) : L.unitFiltration k →* ℂˣ where
  toFun g := ((traceCharacter ψF).val_isUnit (β * ((g.val : A) - 1))).unit
  map_one' := by
    apply Units.ext
    change traceCharacter ψF (β * ((1 : A) - 1)) = 1
    simp
  map_mul' g h := by
    apply Units.ext
    change traceCharacter ψF (β * ((g.val : A) * (h.val : A) - 1)) =
      traceCharacter ψF (β * ((g.val : A) - 1)) * traceCharacter ψF (β * ((h.val : A) - 1))
    let x := (g.val : A) - 1
    let y := (h.val : A) - 1
    have hprod : β * ((g.val : A) * (h.val : A) - 1) = β * x + β * y + β * (x * y) := by
      dsimp [x, y]
      noncomm_ring
    have hxy : β * (x * y) ∈ L.endFiltration 1 :=
      L.endFiltration_antitone (by omega) (L.mul_mem_endFiltration hβ
        (L.mul_mem_endFiltration g.2.2.2 h.2.2.2))
    rw [hprod, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      traceCharacter_eq_one_of_mem L ψF hψ hxy, mul_one]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The high trace character is unchanged by conjugation by a unit commuting with the element. -/
theorem elementCharacter_conj_eq (ψF : AddChar F ℂ) (β : A) (g h : G)
    (hg : Commute β (g : A)) :
    elementCharacter (traceCharacter ψF) β (g * h * g⁻¹) =
      elementCharacter (traceCharacter ψF) β h := by
  unfold elementCharacter
  have heq : β * (((g * h * g⁻¹ : G) : A) - 1) =
      (g : A) * (β * ((h : A) - 1)) * ((g⁻¹ : G) : A) := by
    simp only [Units.val_mul]
    have hsub : (g : A) * (h : A) * ((g⁻¹ : G) : A) - 1 =
        (g : A) * ((h : A) - 1) * ((g⁻¹ : G) : A) := by
      rw [mul_sub, sub_mul, mul_one, Units.mul_inv]
    rw [hsub]
    simp only [← mul_assoc, hg.eq]
  rw [heq, traceCharacter_apply, LinearMap.trace_conj, traceCharacter_apply]

section Relative

variable {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem trace_restrictScalars [FiniteDimensional F E] [FiniteDimensional E V]
    (x : Module.End E V) :
    LinearMap.trace F V (x.restrictScalars F) = Algebra.trace F E (LinearMap.trace E V x) := by
  classical
  let b := Module.finBasis F E
  let c := Module.finBasis E V
  rw [LinearMap.trace_eq_matrix_trace F (b.smulTower' c), LinearMap.restrictScalars_toMatrix b c,
    LinearMap.trace_eq_matrix_trace E c, Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, Fintype.sum_prod_type, Matrix.comp_apply, Matrix.map_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (Algebra.trace_eq_matrix_trace b _).symm

variable [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  (L : LatticeChain 𝒪[F] F V) (C : LatticeChain 𝒪[E] E V)
  (hC : ∀ i v, v ∈ C.lattice i ↔ v ∈ L.lattice i)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hC in
/-- The depth of a nonzero scalar on the original chain is its relative
uniformizer order multiplied by the relative chain period. -/
theorem valuation_subfieldEmbedding_of_relative (b : E) (hb : b ≠ 0)
    {π : 𝒪[E]} (hπ : Irreducible π) :
    L.valuation (subfieldEmbedding F E V b) =
      (((C.period : ℤ) * ordOf hπ b : ℤ) : WithTop ℤ) := by
  classical
  let := L.nontrivialSpace
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hne : subfieldEmbedding F E V b ≠ 0 := by
    intro h
    exact smul_ne_zero hb hv (LinearMap.congr_fun h v)
  have hfilter (j : ℤ) :
      subfieldEmbedding F E V b ∈ L.endFiltration j ↔ j ≤ (C.period : ℤ) * ordOf hπ b := by
    constructor
    · intro h
      have hm := (hC _ _).mpr (h (C.index hπ v) v ((hC _ _).mp (C.mem_lattice_index hπ hv)))
      change b • v ∈ C.lattice (C.index hπ v + j) at hm
      rw [C.smul_mem_iff hπ hb, C.mem_iff_le_index hπ hv] at hm
      omega
    · intro h i w hw
      apply (hC _ _).mp
      change b • w ∈ C.lattice (i + j)
      rw [C.smul_mem_iff hπ hb]
      exact C.antitone (by omega) ((hC _ _).mpr hw)
  have hset : {j : ℤ | subfieldEmbedding F E V b ∈ L.endFiltration j} =
      Set.Iic ((C.period : ℤ) * ordOf hπ b) := Set.ext hfilter
  rw [LatticeChain.valuation, ite_eq_right hne, hset, csSup_Iic]

include hC in
/-- On relative units beyond half the original depth, the trace character
is a function of the relative determinant. -/
theorem elementCharacter_eq_relativeDet_of_highDepth [FiniteDimensional F E]
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) (b : E) (hb : b ≠ 0)
    (n : ℤ) (hval : L.valuation (subfieldEmbedding F E V b) = (-n : WithTop ℤ))
    (k : ℕ) (hk : n < 2 * (k : ℤ))
    (g : (Module.End E V)ˣ) (hg : g ∈ C.unitFiltration k) :
    elementCharacter (traceCharacter ψF) (subfieldEmbedding F E V b) (relativeEndUnits E g) =
      ψF (Algebra.trace F E (b * (LinearMap.det (g : Module.End E V) - 1))) := by
  let := C.finiteDimensional
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  have hβ := valuation_subfieldEmbedding_of_relative L C hC b hb hπ
  have hscale := WithTop.coe_injective (hβ.symm.trans hval)
  let t := -ordOf hπ b
  have hn : (C.period : ℤ) * t = n := by dsimp [t]; rw [mul_neg, hscale, neg_neg]
  let x := (g : Module.End E V) - 1
  let Δ := LinearMap.det (1 + x) - 1 - LinearMap.trace E V x
  let a := (π : E) ^ (-(t + 1)) * Δ
  have ha : a ∈ 𝒪[E] := C.det_one_add_sub_trace_scaled_mem_integer hπ (by positivity)
    (by simpa only [add_sub_cancel_right, hn] using hk) hg.2.2
  let b' := (π : E) ^ t * b
  have hπ0 := coe_uniformizer_ne_zero hπ
  have hb' : b' ∈ 𝒪[E] := by
    apply mem_integer_of_ordOf_nonneg hπ (mul_ne_zero (zpow_ne_zero _ hπ0) hb)
    change 0 ≤ ordOf hπ ((π : E) ^ t * b)
    rw [ordOf_mul hπ (zpow_ne_zero _ hπ0) hb, ordOf_zpow hπ]
    dsimp [t]
    omega
  have hδ : b * Δ = (π : E) * (b' * a) := by
    dsimp only [b', a]
    calc b * Δ = (π : E) ^ ((1 : ℤ) + t + -(t + 1)) * (b * Δ) := by
           rw [show (1 : ℤ) + t + -(t + 1) = 0 by omega, zpow_zero, one_mul]
         _ = _ := by rw [zpow_add₀ hπ0, zpow_add₀ hπ0, zpow_one]; ring
  obtain ⟨r, w, ⟨j⟩, hw, _⟩ := C.exists_common_splitting_basis C hπ
  let p := elementaryEnd w j j 1
  have hp := C.elementaryEnd_diag_mem_order hπ hw j
  have htracep : LinearMap.trace E V p = 1 := by
    change LinearMap.trace E V (1 • (w.coord j).smulRight (w j)) = 1
    simp [LinearMap.trace_smulRight]
  have hmem : ((b * Δ) • p).restrictScalars F ∈ L.endFiltration 1 := by
    intro i w hw
    apply (hC _ _).mp
    change (b * Δ) • p w ∈ C.lattice (i + 1)
    rw [hδ, mul_smul, C.uniformizer_smul_mem_iff hπ]
    have hper : (1 : ℤ) ≤ (C.period : ℤ) := by exact_mod_cast C.period_pos
    have hsmul := (C.lattice i).smul_mem ⟨b' * a, Subring.mul_mem _ hb' ha⟩
      (show p w ∈ C.lattice i by simpa using hp i w ((hC _ _).mpr hw))
    exact C.antitone (by omega) hsmul
  have hψΔ : ψF (Algebra.trace F E (b * Δ)) = 1 := by
    have h := traceCharacter_eq_one_of_mem L ψF hψ hmem
    rw [traceCharacter_apply, trace_restrictScalars, map_smul, htracep, smul_eq_mul, mul_one] at h
    exact h
  have hdet : b * (LinearMap.det (g : Module.End E V) - 1) =
      b * LinearMap.trace E V x + b * Δ := by
    dsimp only [Δ]
    have hx : 1 + x = (g : Module.End E V) := by simp [x]
    rw [hx]
    ring
  rw [elementCharacter_apply, traceCharacter_apply]
  change ψF (LinearMap.trace F V ((b • x).restrictScalars F)) = _
  rw [trace_restrictScalars, map_smul, smul_eq_mul, hdet, map_add, AddChar.map_add_eq_mul,
    hψΔ, mul_one]

end Relative

end Langlands.BushnellKutzko

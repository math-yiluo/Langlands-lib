import Langlands.BushnellKutzko.MoyReductionSandwich
import Langlands.BushnellKutzko.PureStratumApproximationChainLift
import Langlands.BushnellKutzko.SubfieldLayerLifting
import Langlands.BushnellKutzko.RefinementChainTransport

/-! # Moy's reduction in the centralizer of a field

BK93 (2.3.1), printed p. 57, applied in `B = End_E(V)` to the hereditary `𝔬_E`-order of a chain
normalized by `E`, as in the proof of (2.4.5), printed p. 68. The result is stated for chains over
`𝔬_F` normalized by `E`: a coset of the `E`-linear filtration containing a nilpotent element lies
in a step of smaller normalized depth of a second chain normalized by `E`, whose lattices are
sandwiched between consecutive lattices of the first chain.
-/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko.PureApproximation

universe uO uO' uK uF uE uV

section Periods

variable {O : Type uO} {O' : Type uO'} {K : Type uK} {V : Type uV} [CommRing O] [CommRing O']
  [IsDomain O] [IsDomain O'] [IsDiscreteValuationRing O] [IsDiscreteValuationRing O']
  [Field K] [Algebra O K] [Algebra O' K] [AddCommGroup V] [Module K V]
  [Module O V] [IsScalarTower O K V] [Module O' V] [IsScalarTower O' K V]

/-- Two chains with the same lattices, over discrete valuation rings with uniformizers having the
same image in `K`, have the same period. -/
theorem period_eq_of_coe_lattice_eq (A : LatticeChain O K V) (B : LatticeChain O' K V)
    (h : ∀ i, (A.lattice i : Set V) = B.lattice i) {ϖ : O} {ϖ' : O'} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') (hc : algebraMap O K ϖ = algebraMap O' K ϖ') :
    A.period = B.period := by
  have h1 := A.lattice_add_period_uniformizer hϖ 0
  have h2 := B.lattice_add_period_uniformizer hϖ' 0
  have h3 : B.lattice (0 + A.period) = B.lattice (0 + B.period) := by
    apply SetLike.coe_injective
    rw [← h, h1, h2, Submodule.coe_pointwise_smul, Submodule.coe_pointwise_smul, hc, h]
  have h4 := B.injective h3
  exact_mod_cast (by simpa using h4 : (A.period : ℤ) = B.period)

end Periods

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E] [FiniteDimensional F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

/-- **BK93 (2.3.1) in `End_E(V)`**, with a compatible chain. Let `𝓛` be normalized by `E`, and
let `z, y ∈ End_E(V)` with `z ∈ 𝔓^j(𝓛)`, `y` nilpotent and `y − z ∈ 𝔓^{j+1}(𝓛)`. Then there are a
chain `𝓜` normalized by `E` whose lattices are sandwiched between consecutive lattices of `𝓛`
and an integer `j'` with `j/e(𝓛) < j'/e(𝓜)` such that every `E`-linear `w ∈ z + 𝔓^{j+1}(𝓛)`
lies in `𝔓^{j'}(𝓜)`. -/
theorem exists_compatible_chain_of_isNilpotent (𝓛 : LatticeChain 𝒪[F] F V)
    (hL : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer) {j : ℤ} {z y : Module.End E V}
    (hz : z.restrictScalars F ∈ 𝓛.endFiltration j) (hy : IsNilpotent y)
    (hyz : (y - z).restrictScalars F ∈ 𝓛.endFiltration (j + 1)) :
    ∃ (𝓜 : LatticeChain 𝒪[F] F V) (j' : ℤ),
      (∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓜.stabilizer) ∧
      (∀ w : Module.End E V, (w - z).restrictScalars F ∈ 𝓛.endFiltration (j + 1) →
        w.restrictScalars F ∈ 𝓜.endFiltration j') ∧
      j * 𝓜.period < j' * 𝓛.period ∧
      ∀ t, ∃ q, 𝓛.lattice (q + 1) ≤ 𝓜.lattice t ∧ 𝓜.lattice t ≤ 𝓛.lattice q := by
  classical
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  have := LocalField.FiniteExtension.isLocalField F E
  have := 𝓛.finiteDimensional
  have : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite F E V
  let φ := subfieldIntegerEquiv F E
  let L₁ := 𝓛.subfieldChain E hL
  let C := L₁.transfer φ (fun _ => rfl)
  let f := (Module.finBasis E V).equivFun
  let D := C.linearEquivMap f
  let κ := f.conjAlgEquiv E
  have hD : ∀ i (u : Fin (Module.finrank E V) → E), u ∈ D.lattice i ↔ f.symm u ∈ 𝓛.lattice i :=
    fun i u => LatticeChain.mem_linearEquivMap C f i u
  have hκ : ∀ (x : Module.End E V) (v : V), f.symm (κ x (f v)) = x v := by
    intro x v
    simp [κ, LinearEquiv.conjAlgEquiv_apply]
  have hmemD : ∀ (x : Module.End E V) (k : ℤ),
      κ x ∈ D.endFiltration k ↔ x.restrictScalars F ∈ 𝓛.endFiltration k := by
    intro x k
    constructor
    · intro hx i v hv
      have h := (hD _ _).mp (hx i (f v) ((hD i _).mpr (by simpa using hv)))
      rw [hκ] at h
      exact h
    · intro hx i u hu
      rw [hD] at hu ⊢
      have h := hx i (f.symm u) hu
      have h' := hκ x (f.symm u)
      simp only [LinearEquiv.apply_symm_apply] at h'
      rw [h']
      exact h
  have hz' : κ z ∈ D.endFiltration j := (hmemD z j).mpr hz
  have hy' : IsNilpotent (κ y) := by
    obtain ⟨n, hn⟩ := hy
    exact ⟨n, by rw [← map_pow, hn, map_zero]⟩
  have hyz' : κ y - κ z ∈ D.endFiltration (j + 1) := by
    rw [← map_sub]
    exact (hmemD _ _).mpr hyz
  obtain ⟨N, j', hcos, hlt, hsw⟩ := D.exists_latticeChain_of_isNilpotent_sandwiched hz' hy' hyz'
  let ME := N.linearEquivMap f.symm
  let MS := ME.transfer φ.symm (fun a => by
    change algebraMap 𝒪[E] E (φ (φ.symm a)) = _
    rw [RingEquiv.apply_symm_apply])
  have hMS : ∀ i (v : V), v ∈ MS.lattice i ↔ f v ∈ N.lattice i := by
    intro i v
    change v ∈ ME.lattice i ↔ _
    rw [LatticeChain.mem_linearEquivMap]
    simp
  refine ⟨liftChain MS, j', liftChain_normalized MS, ?_, ?_, ?_⟩
  · intro w hw
    have h1 : κ w - κ z ∈ D.endFiltration (j + 1) := by
      rw [← map_sub]
      exact (hmemD _ _).mpr hw
    have h2 := hcos (κ w) h1
    intro i v hv
    change v ∈ MS.lattice i at hv
    change w v ∈ MS.lattice (i + j')
    rw [hMS] at hv ⊢
    have h := h2 i (f v) hv
    have h' := congrArg f (hκ w v)
    simp only [LinearEquiv.apply_symm_apply] at h'
    rwa [h'] at h
  · -- periods
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
    have hϖ' : Irreducible (φ ϖ) := (MulEquiv.irreducible_iff φ.toMulEquiv).mpr hϖ
    have hpC : L₁.period = C.period :=
      period_eq_of_coe_lattice_eq L₁ C (fun i => rfl) hϖ hϖ' rfl
    have hpD : D.period = C.period := by
      symm
      apply D.period_unique
      intro i
      change ((C.lattice (i + C.period)).map _) = Ring.jacobson 𝒪[E] • ((C.lattice i).map
        (f.toLinearMap.restrictScalars 𝒪[E]))
      rw [C.lattice_add_period, Submodule.map_smul'']
    have hpME : ME.period = N.period := by
      symm
      apply ME.period_unique
      intro i
      change ((N.lattice (i + N.period)).map _) = Ring.jacobson 𝒪[E] • ((N.lattice i).map
        (f.symm.toLinearMap.restrictScalars 𝒪[E]))
      rw [N.lattice_add_period, Submodule.map_smul'']
    have hpMS : MS.period = ME.period :=
      (period_eq_of_coe_lattice_eq ME MS (fun i => rfl) hϖ' hϖ
        (by change _ = algebraMap 𝒪[E] E (φ ϖ); rfl)).symm
    have hpL : (𝓛.period : ℤ) = subfieldRamificationIndex F E * L₁.period := by
      rw [LatticeChain.subfieldChain_period_eq_shift 𝓛 E hL hϖ, mul_comm]
      exact (𝓛.fieldShift_uniformizer_mul_ramification E hL hϖ).symm
    rw [liftChain_period, hpL]
    push_cast
    rw [hpMS, hpME, hpC, ← hpD]
    have he : (0 : ℤ) < subfieldRamificationIndex F E := by
      exact_mod_cast subfieldRamificationIndex_pos' (F := F) (E := E)
    have := mul_lt_mul_of_pos_left hlt he
    linarith
  · intro t
    obtain ⟨q, h1, h2⟩ := hsw t
    refine ⟨q, ?_, ?_⟩
    · intro v hv
      change v ∈ MS.lattice t
      rw [hMS]
      apply h1.le
      rw [hD]
      simpa using hv
    · intro v hv
      change v ∈ MS.lattice t at hv
      rw [hMS] at hv
      have h := (hD _ _).mp (h2 hv)
      simpa using h

end Langlands.BushnellKutzko.PureApproximation

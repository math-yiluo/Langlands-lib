import Langlands.BushnellKutzko.FundamentalStratumDual
import Langlands.BushnellKutzko.IntertwiningAveraging
import Langlands.BushnellKutzko.NormalizedLevel
import Langlands.Representation.Conductor.PrincipalCongruenceBasisProof

/-! # Proof of L1: a fundamental stratum computes the normalized level (core)

Bushnell (1987), Remark (2.9), printed p. 195, and (3.3) and Theorem 2′, printed
pp. 196–197. See also Bushnell–Kutzko (1993), Introduction, printed p. 8, and §2.3,
printed p. 57.

This module proves the body of statement L1 as `fundamentalStratumLevel_of_containsStratum`.
It uses the normalized-level definitions and explicitly named canonical instances. The closing theorem
`fundamentalStratumLevel` is in `Langlands.BushnellKutzko.FundamentalStratumLevelProof`.

Let `a` contain the fundamental stratum `[𝔄(𝓛), m, m - 1, b]`, with eigenvector `v` for the
function `χ(g) = ψ(tr(b (g - 1)))` on `U^m(𝔄(𝓛))`.

* `m / e(𝓛)` is a normalized level value of `a`: `χ` is trivial on `U^{m+1}(𝔄(𝓛))`, because
  `b (g - 1) ∈ 𝔓^1(𝓛)` has trace in `𝔭_K` (`LatticeChain.addChar_trace_eq_one`), so `v` is
  fixed by `U^{m+1}(𝔄(𝓛))`.
* Let `w ≠ 0` be fixed by `U^{m''+1}(𝔄(𝓛''))` and suppose `m'' / e'' < m / e`. The averaging
  lemma `exists_forall_conj_mem_eq_one` (with `H = U^m(𝔄(𝓛))`, `N = U^{m+1}(𝔄(𝓛))` and
  `J = U^{m''+1}(𝔄(𝓛''))`, all indices finite because `H` is compact and `N`, `J` are open)
  gives `g ∈ GL_n(K)` with `χ = 1` on `H ∩ g J g⁻¹`. With the transported chain
  `𝓛''' = g 𝓛''` (`LatticeChain.mapUnit`) this says `ψ(tr(b x)) = 1` for
  `x ∈ 𝔓^m(𝓛) ∩ 𝔓^{m''+1}(𝓛''')`. Then `LatticeChain.exists_isNilpotent_add` gives a nilpotent
  element of `b + 𝔓^{1-m}(𝓛)`, which contradicts the hypothesis that the stratum is fundamental.
-/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe u uK uV

/-! ### Traces of elements of `𝔓^1`, and comparison of filtrations -/

section Generic

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- An additive character takes the value `1` on a sum of elements at which it is `1`. -/
theorem addChar_sum_eq_one {κ : Type*} (ψ : AddChar F ℂ) (s : Finset κ) (f : κ → F)
    (hf : ∀ k ∈ s, ψ (f k) = 1) : ψ (∑ k ∈ s, f k) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, AddChar.map_add_eq_mul, hf a (Finset.mem_insert_self a s),
      ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)), one_mul]

include hϖ in
/-- An element of positive valuation lies in `𝔭_F`. -/
theorem exists_mem_maximalIdeal_of_one_le_ordOf {c : F} (hc : c ≠ 0) (h : 1 ≤ ordOf hϖ c) :
    ∃ a ∈ 𝓂[F], (a : F) = c := by
  obtain ⟨w, hw⟩ := exists_eq_zpow_ordOf_mul hϖ hc
  obtain ⟨t, ht⟩ : ∃ t : ℕ, ordOf hϖ c = ((t + 1 : ℕ) : ℤ) :=
    ⟨(ordOf hϖ c - 1).toNat, by omega⟩
  refine ⟨ϖ ^ (t + 1) * (w : 𝒪[F]), ?_, ?_⟩
  · exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _
      ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit) _ (Nat.succ_pos t))
  · rw [hw, ht, zpow_natCast]
    simp

namespace LatticeChain

variable {ι : Type*} (𝓛 : LatticeChain 𝒪[F] F (ι → F))

include hϖ in
/-- If `ψ` is trivial on `𝔭_F`, then `ψ(tr x) = 1` for every `x ∈ 𝔓^1(𝓛)`. -/
theorem addChar_trace_eq_one (ψ : AddChar F ℂ) (hψ : ∀ a ∈ 𝓂[F], ψ (a : F) = 1)
    {x : Module.End F (ι → F)} (hx : x ∈ 𝓛.endFiltration 1) :
    ψ (LinearMap.trace F (ι → F) x) = 1 := by
  classical
  obtain ⟨r, β, hβ⟩ := 𝓛.exists_basis_splits hϖ
  rw [LinearMap.trace_eq_matrix_trace F β x, Matrix.trace]
  refine addChar_sum_eq_one ψ _ _ fun k _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change ψ (entry β x k k) = 1
  by_cases hk : entry β x k k = 0
  · rw [hk, AddChar.map_zero_eq_one]
  · have h := 𝓛.le_of_mem_endFiltration hϖ hβ hx k k hk
    have he : (0 : ℤ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
    have h1 : 1 ≤ ordOf hϖ (entry β x k k) := by
      by_contra hcon
      have h0 : ordOf hϖ (entry β x k k) ≤ 0 := by omega
      nlinarith
    obtain ⟨a, ha, hae⟩ := exists_mem_maximalIdeal_of_one_le_ordOf hϖ hk h1
    rw [← hae]
    exact hψ a ha

variable [Fintype ι]

include hϖ in
/-- **Comparison of filtrations.** For lattice chains `𝓛, 𝓛'` in `F^ι` and `j ∈ ℤ`,
`𝔓^N(𝓛') ⊆ 𝔓^j(𝓛)` for some `N`. -/
theorem exists_endFiltration_le (𝓛' : LatticeChain 𝒪[F] F (ι → F)) (j : ℤ) :
    ∃ N : ℤ, 𝓛'.endFiltration N ≤ 𝓛.endFiltration j := by
  classical
  obtain ⟨r, β, hβ, hβ'⟩ := exists_basis_splits_both hϖ 𝓛 𝓛'
  obtain ⟨C, hC⟩ : ∃ C : ℤ, ∀ k : Fin r,
      |𝓛.index hϖ (β k)| + |𝓛'.index hϖ (β k)| ≤ C :=
    ⟨∑ k, (|𝓛.index hϖ (β k)| + |𝓛'.index hϖ (β k)|), fun k =>
      Finset.single_le_sum (f := fun k => |𝓛.index hϖ (β k)| + |𝓛'.index hϖ (β k)|)
        (fun i _ => by positivity) (Finset.mem_univ k)⟩
  have he : (1 : ℤ) ≤ 𝓛.period := by exact_mod_cast 𝓛.period_pos
  have he' : (1 : ℤ) ≤ 𝓛'.period := by exact_mod_cast 𝓛'.period_pos
  refine ⟨𝓛'.period * (|j| + 2 * C) + 2 * C, fun x hx => ?_⟩
  rw [← sum_elementaryEnd_entry β x]
  refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ => ?_
  by_cases hkl : entry β x k l = 0
  · rw [hkl, elementaryEnd_zero]
    exact zero_mem _
  · rw [𝓛.elementaryEnd_mem_iff hϖ hβ k l hkl]
    have h := 𝓛'.le_of_mem_endFiltration hϖ hβ' hx k l hkl
    have hk := hC k
    have hl := hC l
    have a1 := abs_nonneg (𝓛.index hϖ (β k))
    have a2 := abs_nonneg (𝓛.index hϖ (β l))
    have a3 := abs_nonneg (𝓛'.index hϖ (β k))
    have a4 := abs_nonneg (𝓛'.index hϖ (β l))
    have a5 := le_abs_self (𝓛'.index hϖ (β k))
    have a6 := neg_abs_le (𝓛'.index hϖ (β l))
    have a7 := le_abs_self (𝓛.index hϖ (β l))
    have a8 := neg_abs_le (𝓛.index hϖ (β k))
    have a9 := le_abs_self j
    have a10 := abs_nonneg j
    have h1 : (𝓛'.period : ℤ) * (|j| + 2 * C) ≤ 𝓛'.period * ordOf hϖ (entry β x k l) := by
      linarith
    have h2 : |j| + 2 * C ≤ ordOf hϖ (entry β x k l) :=
      le_of_mul_le_mul_left h1 (by omega)
    have h3 : 0 ≤ ordOf hϖ (entry β x k l) := by linarith
    have h4 : ordOf hϖ (entry β x k l) ≤ 𝓛.period * ordOf hϖ (entry β x k l) := by nlinarith
    linarith

end LatticeChain

/-! ### The standard chain and principal congruence subgroups -/

namespace LatticeChain

/-- An element of the principal congruence subgroup of level `N` of `GL_{n+1}(F)` is `1 + x`
with `x ∈ 𝔓^N` of the standard chain. -/
theorem sub_one_mem_standard_endFiltration {n N : ℕ}
    {g : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hg : g ∈ Conductor.principalLevelSubgroup F n N) :
    ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup F (Fin (n + 1) → F)) :
        Module.End F (Fin (n + 1) → F)) - 1 ∈
      (standard hϖ (Fin (n + 1))).endFiltration N := by
  classical
  rw [Conductor.principalLevelSubgroup, Conductor.mem_principalCongruenceSubgroup_iff] at hg
  rw [mem_endFiltration]
  intro i v hv
  rw [mem_standard_lattice] at hv ⊢
  intro k
  have hϖ0 : (ϖ : F) ≠ 0 := coe_uniformizer_ne_zero hϖ
  have e1 : (((uniformizerAsUnit hϖ ^ (i + (N : ℤ)))⁻¹ : Fˣ) : F) =
      ((ϖ : F) ^ i)⁻¹ * ((ϖ : F) ^ N)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, coe_uniformizerAsUnit,
      zpow_add₀ hϖ0, zpow_natCast, mul_inv]
  have e2 : (((uniformizerAsUnit hϖ ^ i)⁻¹ : Fˣ) : F) = ((ϖ : F) ^ i)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, coe_uniformizerAsUnit]
  have hcomp : ((((Matrix.GeneralLinearGroup.toLin g :
      LinearMap.GeneralLinearGroup F (Fin (n + 1) → F)) : Module.End F (Fin (n + 1) → F)) - 1)
        v) k = ∑ l, (g k l - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) k l) * v l := by
    rw [LinearMap.sub_apply, Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply,
      Module.End.one_apply, Pi.sub_apply]
    simp only [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [hcomp, Finset.mul_sum, e1]
  refine Subring.sum_mem _ fun l _ => ?_
  obtain ⟨x, hx, hxe⟩ := hg.1 k l
  rw [← hxe]
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx
  obtain ⟨y, rfl⟩ := hx
  have hvl := hv l
  rw [e2] at hvl
  have h : ((ϖ : F) ^ i)⁻¹ * ((ϖ : F) ^ N)⁻¹ * (((y * ϖ ^ N : 𝒪[F]) : F) * v l) =
      (y : F) * (((ϖ : F) ^ i)⁻¹ * v l) := by
    have hN : ((ϖ : F) ^ N) ≠ 0 := pow_ne_zero N hϖ0
    push_cast
    field_simp
  rw [h]
  exact mul_mem y.2 hvl

end LatticeChain

/-! ### Transport of a lattice chain by an automorphism -/

namespace LatticeChain

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The image `P 𝓛` of a lattice chain under an automorphism `P` of `V`:
`(P 𝓛)_i = P L_i`. -/
def mapUnit (𝓛 : LatticeChain 𝒪[F] F V) (P : (Module.End F V)ˣ) : LatticeChain 𝒪[F] F V :=
  𝓛.linearEquivMap (LinearMap.GeneralLinearGroup.toLinearEquiv P)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_mapUnit_lattice (𝓛 : LatticeChain 𝒪[F] F V) (P : (Module.End F V)ˣ) {i : ℤ}
    {v : V} : v ∈ (𝓛.mapUnit P).lattice i ↔
      ((P⁻¹ : (Module.End F V)ˣ) : Module.End F V) v ∈ 𝓛.lattice i :=
  𝓛.mem_linearEquivMap (LinearMap.GeneralLinearGroup.toLinearEquiv P) i v

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem period_mapUnit (𝓛 : LatticeChain 𝒪[F] F V) (P : (Module.End F V)ˣ) :
    (𝓛.mapUnit P).period = 𝓛.period := by
  refine ((𝓛.mapUnit P).period_unique (e := 𝓛.period) fun i => ?_).symm
  change (𝓛.lattice (i + 𝓛.period)).map ((P : Module.End F V).restrictScalars 𝒪[F]) =
    Ring.jacobson 𝒪[F] • (𝓛.lattice i).map ((P : Module.End F V).restrictScalars 𝒪[F])
  rw [𝓛.lattice_add_period, Submodule.map_smul'']

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- If `x ∈ 𝔓^j(P 𝓛)`, then `P⁻¹ x P ∈ 𝔓^j(𝓛)`. -/
theorem conj_mem_endFiltration_of_mem_mapUnit (𝓛 : LatticeChain 𝒪[F] F V)
    (P : (Module.End F V)ˣ) {x : Module.End F V} {j : ℤ}
    (hx : x ∈ (𝓛.mapUnit P).endFiltration j) :
    ((P⁻¹ : (Module.End F V)ˣ) : Module.End F V) * x * (P : Module.End F V) ∈
      𝓛.endFiltration j := by
  rw [mem_endFiltration] at hx ⊢
  intro i v hv
  have h1 : (P : Module.End F V) v ∈ (𝓛.mapUnit P).lattice i := by
    rw [mem_mapUnit_lattice, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
    exact hv
  have h2 := hx i _ h1
  rw [mem_mapUnit_lattice] at h2
  simpa only [Module.End.mul_apply] using h2

end LatticeChain

end Generic

/-! ### Openness and compactness of the unit subgroups -/

section Padic

/-! The canonical instances, as in the Library's normalized-level statement modules. They have
explicit names, so that importing this module next to those statement modules creates no
clash of automatically generated instance names. -/

local instance fslCoreTopologicalSpace {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance fslCoreValuativeRel {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance fslCoreLocalField {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

local instance fslCoreTopologicalSpaceGL {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- The image in `GL_{n+1}(K)` of `U^j(𝔄(𝓛))` is open. -/
theorem isOpen_unitSubgroup {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) {n : ℕ}
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin (n + 1) → K.Carrier)) (j : ℕ) :
    IsOpen (unitSubgroup K 𝓛 j : Set (GeneralLinear (n + 1) K.Carrier)) := by
  have := K.canonicalGeneralLinearTopologicalGroup (n + 1)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K.Carrier]
  obtain ⟨N, hN⟩ := 𝓛.exists_endFiltration_le hϖ (LatticeChain.standard hϖ (Fin (n + 1))) j
  have key : ∀ h : GeneralLinear (n + 1) K.Carrier,
      h ∈ Conductor.principalLevelSubgroup K.Carrier n N.toNat →
      ((Matrix.GeneralLinearGroup.toLin h :
        LinearMap.GeneralLinearGroup K.Carrier (Fin (n + 1) → K.Carrier)) :
          Module.End K.Carrier (Fin (n + 1) → K.Carrier)) - 1 ∈ 𝓛.endFiltration j :=
    fun h hh => hN ((LatticeChain.standard hϖ (Fin (n + 1))).endFiltration_antitone
      (Int.self_le_toNat N) (LatticeChain.sub_one_mem_standard_endFiltration hϖ hh))
  have hord : ∀ h : GeneralLinear (n + 1) K.Carrier,
      h ∈ Conductor.principalLevelSubgroup K.Carrier n N.toNat →
      ((Matrix.GeneralLinearGroup.toLin h :
        LinearMap.GeneralLinearGroup K.Carrier (Fin (n + 1) → K.Carrier)) :
          Module.End K.Carrier (Fin (n + 1) → K.Carrier)) ∈ 𝓛.order := by
    intro h hh
    rw [LatticeChain.mem_order_iff_mem_endFiltration]
    have h1 := 𝓛.endFiltration_antitone (show (0 : ℤ) ≤ j by positivity) (key h hh)
    have h2 := (𝓛.mem_order_iff_mem_endFiltration).1 (one_mem 𝓛.order)
    simpa using add_mem h1 h2
  refine Subgroup.isOpen_mono (H₁ :=
    (Conductor.principalLevelOpenSubgroup K.Carrier n N.toNat).toSubgroup) ?_
    (Conductor.principalLevelOpenSubgroup K.Carrier n N.toNat).isOpen
  intro g hg
  rw [mem_unitSubgroup]
  refine ⟨hord g hg, ?_, key g hg⟩
  rw [← map_inv]
  exact hord g⁻¹ (inv_mem hg)

/-- The image in `GL_{n+1}(K)` of `U^j(𝔄(𝓛))` is compact. -/
theorem isCompact_unitSubgroup {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) {n : ℕ}
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin (n + 1) → K.Carrier)) (j : ℕ) :
    IsCompact (unitSubgroup K 𝓛 j : Set (GeneralLinear (n + 1) K.Carrier)) := by
  classical
  have := K.canonicalGeneralLinearTopologicalGroup (n + 1)
  -- an `F`-basis of `F^{n+1}` coming from an `𝔬_F`-basis of `L_0`
  have hrank : Module.finrank 𝒪[K.Carrier] (𝓛.lattice 0) = n + 1 := by
    rw [Submodule.IsLattice.finrank_of_pi K.Carrier, Fintype.card_fin]
  let b := Module.finBasisOfFinrankEq 𝒪[K.Carrier] (𝓛.lattice 0) hrank
  let bF : Module.Basis (Fin (n + 1)) K.Carrier (Fin (n + 1) → K.Carrier) :=
    b.extendOfIsLattice K.Carrier
  have hbF : ∀ j, bF j ∈ 𝓛.lattice 0 := fun j => by
    simp only [bF, Module.Basis.extendOfIsLattice_apply]
    exact (b j).2
  let P : GeneralLinear (n + 1) K.Carrier := Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv bF.equivFun.symm)
  have hentry : ∀ (h : GeneralLinear (n + 1) K.Carrier) (i j : Fin (n + 1)),
      (P⁻¹ * h * P) i j = bF.repr (((Matrix.GeneralLinearGroup.toLin h :
        LinearMap.GeneralLinearGroup K.Carrier (Fin (n + 1) → K.Carrier)) :
          Module.End K.Carrier (Fin (n + 1) → K.Carrier)) (bF j)) i := by
    intro h i j
    have h1 : ∀ M : GeneralLinear (n + 1) K.Carrier, M i j =
        (((Matrix.GeneralLinearGroup.toLin M :
          LinearMap.GeneralLinearGroup K.Carrier (Fin (n + 1) → K.Carrier)) :
            Module.End K.Carrier (Fin (n + 1) → K.Carrier)) (Pi.single j 1)) i := by
      intro M
      rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
        Matrix.col_apply]
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    simp only [Units.val_mul, Module.End.mul_apply]
    change bF.equivFun (((Matrix.GeneralLinearGroup.toLin h :
        LinearMap.GeneralLinearGroup K.Carrier (Fin (n + 1) → K.Carrier)) :
          Module.End K.Carrier (Fin (n + 1) → K.Carrier)) (bF.equivFun.symm (Pi.single j 1))) i = _
    rw [Basis.equivFun_symm_single, Module.Basis.equivFun_apply]
  have hint : ∀ h : GeneralLinear (n + 1) K.Carrier,
      ((Matrix.GeneralLinearGroup.toLin h :
        LinearMap.GeneralLinearGroup K.Carrier (Fin (n + 1) → K.Carrier)) :
          Module.End K.Carrier (Fin (n + 1) → K.Carrier)) ∈ 𝓛.order →
      ∀ i j : Fin (n + 1), ∃ x : 𝒪[K.Carrier],
        x ∈ IsLocalRing.maximalIdeal 𝒪[K.Carrier] ^ 0 ∧
          (x : K.Carrier) = (P⁻¹ * h * P) i j -
            (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier) i j := by
    intro h hh i j
    have hmem : (P⁻¹ * h * P) i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier) i j ∈
        𝒪[K.Carrier] := by
      refine sub_mem ?_ ?_
      · rw [hentry]
        exact 𝓛.repr_extendOfIsLattice_mem b ((𝓛.mem_order.1 hh) 0 _ (hbF j)) i
      · rw [Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    exact ⟨⟨_, hmem⟩, by simp, rfl⟩
  have hP : ∀ g ∈ unitSubgroup K 𝓛 0,
      P⁻¹ * g * P ∈ Conductor.principalLevelSubgroup K.Carrier n 0 := by
    intro g hg
    rw [Conductor.principalLevelSubgroup, Conductor.mem_principalCongruenceSubgroup_iff]
    refine ⟨hint g hg.1, ?_⟩
    have hinv : (P⁻¹ * g * P)⁻¹ = P⁻¹ * g⁻¹ * P := by group
    rw [hinv]
    refine hint g⁻¹ ?_
    rw [map_inv]
    exact hg.2.1
  have hsub : (unitSubgroup K 𝓛 j : Set (GeneralLinear (n + 1) K.Carrier)) ⊆
      (fun k => P * k * P⁻¹) ''
        (Conductor.principalLevelOpenSubgroup K.Carrier n 0 :
          Set (GeneralLinear (n + 1) K.Carrier)) := by
    intro g hg
    have hg0 : g ∈ unitSubgroup K 𝓛 0 := 𝓛.unitFiltration_antitone (Nat.zero_le j) hg
    exact ⟨P⁻¹ * g * P, hP g hg0, by group⟩
  have hcpt := (Conductor.isCompact_principalLevelOpenSubgroup K.Carrier n 0).image
    (show Continuous fun k : GeneralLinear (n + 1) K.Carrier => P * k * P⁻¹ by fun_prop)
  exact hcpt.of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_unitSubgroup K 𝓛 j)) hsub

/-! ### Proof of L1 -/

/-- **L1** (Bushnell 1987, Remark (2.9) and Theorem 2′, and Bushnell–Kutzko 1993,
Introduction, p. 8). This is the body of `FundamentalStratumLevelStatement`, with the
same hypotheses and canonical instances.
If `a` contains a fundamental stratum `[𝔄(𝓛), m, m - 1, b]`, the normalized level of `a`
is `m / e(𝓛)`. -/
theorem fundamentalStratumLevel_of_containsStratum {p : ℕ} [Fact p.Prime]
    (K : PadicField.{uK} p) (n : ℕ) (hn : 1 ≤ n) (ψ : AddChar K.Carrier ℂ)
    (hψ : IsLevelOne K ψ)
    (a : SmoothDualClass.{0, uK, uV} (k := ℂ) (G := GeneralLinear n K.Carrier))
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin n → K.Carrier)) (m : ℕ)
    (b : Module.End K.Carrier (Fin n → K.Carrier)) (hm : 1 ≤ m)
    (hb : b ∈ 𝓛.endFiltration (-(m : ℤ)))
    (hfund : ∀ y ∈ 𝓛.endFiltration (1 - (m : ℤ)), ¬ IsNilpotent (b + y))
    (hcont : ContainsStratum K n ψ a 𝓛 m b) :
    IsNormalizedLevel K n a ((m : ℚ) / (𝓛.period : ℚ)) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨-, -, A, hA, v, hv0, hvχ⟩ := hcont
  subst hA
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K.Carrier]
  have := K.canonicalGeneralLinearTopologicalGroup (n' + 1)
  have hirr : Representation.IsIrreducible A.obj.representation := A.property.1
  let χ : GeneralLinear (n' + 1) K.Carrier → ℂ := fun g =>
    elementCharacter (traceCharacter ψ) b (Matrix.GeneralLinearGroup.toLin g)
  -- `χ` is trivial on `U^{m+1}(𝔄(𝓛))`
  have hχN : ∀ g ∈ unitSubgroup K 𝓛 (m + 1), χ g = 1 := by
    intro g hg
    change traceCharacter ψ (b * (((Matrix.GeneralLinearGroup.toLin g :
      LinearMap.GeneralLinearGroup K.Carrier (Fin (n' + 1) → K.Carrier)) :
        Module.End K.Carrier (Fin (n' + 1) → K.Carrier)) - 1)) = 1
    rw [traceCharacter_apply]
    refine 𝓛.addChar_trace_eq_one hϖ ψ hψ.1 ?_
    have h := 𝓛.mul_mem_endFiltration hb hg.2.2
    convert h using 2 <;> first | rfl | (push_cast; ring)
  have hle : unitSubgroup K 𝓛 (m + 1) ≤ unitSubgroup K 𝓛 m := fun g hg =>
    𝓛.unitFiltration_antitone (Nat.le_succ m) hg
  refine ⟨⟨𝓛, m, rfl, ?_⟩, ?_⟩
  · -- `v` is fixed by `U^{m+1}(𝔄(𝓛))`
    show fixedVectors A.obj.representation _ ≠ ⊥
    rw [Submodule.ne_bot_iff]
    refine ⟨v, (Representation.mem_invariants _ v).mpr fun h => ?_, hv0⟩
    change A.obj.representation h v = v
    rw [hvχ _ (hle h.2)]
    rw [show elementCharacter (traceCharacter ψ) b (Matrix.GeneralLinearGroup.toLin
      (h : GeneralLinear (n' + 1) K.Carrier)) = 1 from hχN _ h.2, one_smul]
  · rintro x ⟨𝓛'', m'', rfl, hfix⟩
    by_contra hlt
    rw [not_le] at hlt
    have he : (0 : ℚ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
    have he'' : (0 : ℚ) < 𝓛''.period := by exact_mod_cast 𝓛''.period_pos
    rw [div_lt_div_iff₀ he'' he] at hlt
    have hlt' : (m'' : ℤ) * 𝓛.period < m * 𝓛''.period := by exact_mod_cast hlt
    -- a nonzero vector fixed by `U^{m''+1}(𝔄(𝓛''))`
    change fixedVectors A.obj.representation _ ≠ ⊥ at hfix
    rw [Submodule.ne_bot_iff] at hfix
    obtain ⟨w, hw, hw0⟩ := hfix
    have hwJ := (Representation.mem_invariants _ w).mp hw
    -- averaging
    have hcont : ∀ g : GeneralLinear (n' + 1) K.Carrier,
        Continuous fun x : GeneralLinear (n' + 1) K.Carrier => (MulAut.conj g) x := fun g => by
      simp only [MulAut.conj_apply]
      fun_prop
    obtain ⟨g, hg⟩ := exists_forall_conj_mem_eq_one A.obj.representation
      (H := unitSubgroup K 𝓛 m) (J := unitSubgroup K 𝓛'' (m'' + 1))
      (N := unitSubgroup K 𝓛 (m + 1)) (χ := χ)
      (relIndex_ne_zero_of_isCompact (isCompact_unitSubgroup K 𝓛 m)
        (isOpen_unitSubgroup K 𝓛 (m + 1)))
      (fun g => relIndex_ne_zero_of_isCompact (isCompact_unitSubgroup K 𝓛 m)
        ((isOpen_unitSubgroup K 𝓛'' (m'' + 1)).preimage (hcont g⁻¹)))
      hv0 (fun h hh => hvχ h hh) (fun h _ hN => hχN h hN) hw0 (fun j hj => hwJ ⟨j, hj⟩)
    -- transport `𝓛''` by `g`
    let P : (Module.End K.Carrier (Fin (n' + 1) → K.Carrier))ˣ :=
      Matrix.GeneralLinearGroup.toLin g
    have hper : (𝓛''.mapUnit P).period = 𝓛''.period := 𝓛''.period_mapUnit P
    obtain ⟨s, hs⟩ := hψ.2
    have htr : ∀ x ∈ 𝓛.endFiltration (m : ℤ),
        x ∈ (𝓛''.mapUnit P).endFiltration ((m'' : ℤ) + 1) →
        ψ (LinearMap.trace K.Carrier (Fin (n' + 1) → K.Carrier) (b * x)) = 1 := by
      intro x hx hx'
      obtain ⟨u, hu, hux⟩ := 𝓛.exists_mem_unitFiltration hm hx
      have hH : Matrix.GeneralLinearGroup.toLin.symm u ∈ unitSubgroup K 𝓛 m := by
        rw [mem_unitSubgroup, MulEquiv.apply_symm_apply]
        exact hu
      have hJ : g⁻¹ * Matrix.GeneralLinearGroup.toLin.symm u * g ∈
          unitSubgroup K 𝓛'' (m'' + 1) := by
        rw [mem_unitSubgroup]
        have hx'' := 𝓛''.conj_mem_endFiltration_of_mem_mapUnit P hx'
        obtain ⟨u'', hu'', hu''e⟩ := 𝓛''.exists_mem_unitFiltration (n := m'' + 1)
          (by omega) (by exact_mod_cast hx'')
        convert hu'' using 1
        apply Units.ext
        rw [hu''e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
        simp only [Units.val_mul, hux, mul_add, add_mul, mul_one]
        rw [Units.inv_mul]
      have h := hg _ hH hJ
      change traceCharacter ψ (b * (((Matrix.GeneralLinearGroup.toLin
        (Matrix.GeneralLinearGroup.toLin.symm u) :
          LinearMap.GeneralLinearGroup K.Carrier (Fin (n' + 1) → K.Carrier)) :
            Module.End K.Carrier (Fin (n' + 1) → K.Carrier)) - 1)) = 1 at h
      rw [MulEquiv.apply_symm_apply, hux, add_sub_cancel_left, traceCharacter_apply] at h
      exact h
    obtain ⟨y, hy, hnil⟩ := 𝓛.exists_isNilpotent_add hϖ (𝓛''.mapUnit P) (m := m) (m'' := m'')
      (by rw [hper]; exact hlt') hb ψ s.2 hs htr
    exact hfund y hy hnil

end Padic

end Langlands.BushnellKutzko

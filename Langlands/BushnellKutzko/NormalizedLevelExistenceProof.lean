import Langlands.BushnellKutzko.SplittingBasis
import Langlands.BushnellKutzko.NormalizedLevelExistenceStatement
import Langlands.Representation.Conductor.PrincipalCongruenceBasisProof

/-! # Existence of the normalized level (proof of statement L0)

Every class `a` of irreducible admissible representations of `GL_n(K)`, `n ≥ 1`, has a
normalized level: `normalizedLevelValues K n a` has a least element.

* The set is nonempty: a nonzero vector of a representative is fixed by an open subgroup, which
  contains a principal congruence subgroup `K(N)`, `N ≥ 1`; the unit group `U^N(𝔄)` of the
  standard lattice chain `L_i = ϖ^i 𝔬_K^n` (period one) lies in `K(N)`.
* The period of every `𝔬_K`-lattice chain in `K^n` is at most `n`
  (`LatticeChain.period_le_card`), so every value `m / e(𝓛)` is a multiple of `1 / n!`; a
  nonempty set of nonnegative multiples of `1 / n!` has a least element.
-/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe u uK uV

/-! ### The period of a lattice chain is at most the dimension -/

section Period

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

namespace LatticeChain

/-- The period of an `𝔬_F`-lattice chain in `F^ι` is at most `#ι`: the lattices
`L_0 ⊋ L_1 ⊋ ⋯ ⊋ L_e = 𝔭_F L_0` give a strict chain of length `e` of submodules of
`L_0 / 𝔭_F L_0`, a vector space of dimension `#ι` over the residue field. -/
theorem period_le_card {ι : Type*} [Fintype ι] (𝓛 : LatticeChain 𝒪[F] F (ι → F)) :
    𝓛.period ≤ Fintype.card ι := by
  classical
  set e := 𝓛.period with he
  set L0 := 𝓛.lattice 0 with hL0
  have : L0.IsLattice F := 𝓛.isLattice 0
  have hle0 : ∀ i : ℤ, 0 ≤ i → 𝓛.lattice i ≤ L0 := fun i hi => 𝓛.antitone hi
  -- `N j` is the lattice `L_j` as a submodule of `L_0`.
  let N : ℕ → Submodule 𝒪[F] L0 := fun j => (𝓛.lattice j).comap L0.subtype
  have hN_anti : ∀ i j : ℕ, i ≤ j → N j ≤ N i := fun i j hij =>
    Submodule.comap_mono (𝓛.antitone (by exact_mod_cast hij))
  have hN_lt : ∀ j : ℕ, N (j + 1) < N j := by
    intro j
    have hlt : 𝓛.lattice ((j : ℤ) + 1) < 𝓛.lattice j := 𝓛.lattice_succ_lt j
    refine lt_of_le_of_ne (hN_anti _ _ (Nat.le_succ j)) ?_
    intro hEq
    have h := congrArg (Submodule.map L0.subtype) hEq
    simp only [N, Submodule.map_comap_subtype] at h
    rw [inf_eq_right.2 (hle0 _ (by positivity)), inf_eq_right.2 (hle0 _ (by positivity))] at h
    push_cast at h
    exact hlt.ne h
  have hNe : N e = IsLocalRing.maximalIdeal 𝒪[F] • (⊤ : Submodule 𝒪[F] L0) := by
    apply Submodule.map_injective_of_injective L0.injective_subtype
    have h := 𝓛.lattice_add_period 0
    rw [zero_add, jacobson_integer_eq_maximalIdeal, ← he, ← hL0] at h
    simp only [N, Submodule.map_comap_subtype, Submodule.map_smul'', Submodule.map_subtype_top]
    rw [h]
    exact inf_eq_right.2 Submodule.smul_le_right
  -- The images `P j` of the `N j` in `L_0 / L_e`.
  let P : ℕ → Submodule 𝒪[F] (L0 ⧸ N e) := fun j => (N j).map (N e).mkQ
  have hP_lt : ∀ j, j < e → P (j + 1) < P j := by
    intro j hj
    refine lt_of_le_of_ne (Submodule.map_mono (hN_lt j).le) ?_
    intro hEq
    have h := congrArg (Submodule.comap (N e).mkQ) hEq
    simp only [P, Submodule.comap_map_mkQ] at h
    rw [sup_eq_right.2 (hN_anti _ _ (by omega)), sup_eq_right.2 (hN_anti _ _ (by omega))] at h
    exact (hN_lt j).ne h
  have hcoh : ∀ j, j ≤ e → (j : ℕ∞) ≤ Order.coheight (P j) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := Order.coheight_add_one_le (hP_lt j (by omega))
      have h2 := ih (by omega)
      calc ((j + 1 : ℕ) : ℕ∞) = (j : ℕ∞) + 1 := by push_cast; rfl
        _ ≤ Order.coheight (P j) + 1 := by gcongr
        _ ≤ Order.coheight (P (j + 1)) := h1
  have hPe : P e = ⊥ := Submodule.mkQ_map_self _
  have hlen : (e : ℕ∞) ≤ Module.length 𝒪[F] (L0 ⧸ N e) := by
    rw [Module.length_eq_coheight, ← hPe]
    exact hcoh e le_rfl
  -- `L_0 / 𝔭_F L_0` has length `#ι`.
  have hlen' : Module.length 𝒪[F] (L0 ⧸ N e) = Fintype.card ι := by
    rw [(Submodule.quotEquivOfEq _ _ hNe).length_eq]
    let := Ideal.Quotient.field (IsLocalRing.maximalIdeal 𝒪[F])
    rw [Module.length_eq_of_surjective (R := 𝒪[F] ⧸ IsLocalRing.maximalIdeal 𝒪[F])
      Ideal.Quotient.mk_surjective]
    have : Module.Finite (𝒪[F] ⧸ IsLocalRing.maximalIdeal 𝒪[F])
        (L0 ⧸ IsLocalRing.maximalIdeal 𝒪[F] • (⊤ : Submodule 𝒪[F] L0)) :=
      Module.Finite.of_restrictScalars_finite 𝒪[F] _ _
    rw [Module.length_eq_finrank,
      ← IsLocalRing.spanFinrank_eq_finrank_quotient L0 (𝓛.fg_lattice 0),
      ← Submodule.spanFinrank_top, ← Module.finrank_eq_spanFinrank_of_free,
      Submodule.IsLattice.finrank_of_pi F]
  rw [hlen'] at hlen
  exact_mod_cast hlen

end LatticeChain

end Period

/-! ### The standard lattice chain -/

section Standard

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)

theorem stdChain_lattice (ι : Type*) [Fintype ι] [Nonempty ι] (i : ℤ) :
    (LatticeChain.standard hϖ ι).lattice i = (LatticeChain.uniformizerAsUnit hϖ ^ i) • LatticeChain.standardLattice F ι :=
  rfl

/-- Every element of `U^N(𝔄)` for the standard chain is congruent to `1` modulo `𝔭_F^N`
entrywise. -/
theorem exists_mem_pow_of_mem_unitFiltration {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (N : ℕ) (g : Matrix.GeneralLinearGroup ι F)
    (hg : Matrix.GeneralLinearGroup.toLin g ∈ (LatticeChain.standard hϖ ι).unitFiltration N) (i j : ι) :
    ∃ x : 𝒪[F], x ∈ IsLocalRing.maximalIdeal 𝒪[F] ^ N ∧
      (x : F) = g i j - (1 : Matrix ι ι F) i j := by
  have h1 := hg.2.2 0 (Pi.single j 1) (by
    rw [stdChain_lattice, zpow_zero, one_smul, LatticeChain.mem_standardLattice]
    intro k
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _)
  rw [zero_add, stdChain_lattice, LatticeChain.mem_smul_standardLattice] at h1
  have h2 := h1 i
  have hcol : ((((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup F (ι → F)) :
      Module.End F (ι → F)) - 1) (Pi.single j 1)) i = g i j - (1 : Matrix ι ι F) i j := by
    rw [LinearMap.sub_apply, Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply,
      Matrix.mulVec_single_one, Module.End.one_apply, Pi.sub_apply, Matrix.col_apply,
      Matrix.one_apply, Pi.single_apply]
  rw [hcol] at h2
  refine ⟨ϖ ^ N * ⟨_, h2⟩, Ideal.mul_mem_right _ _
    (Ideal.pow_mem_pow ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit) N), ?_⟩
  have hne : (ϖ : F) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow, zpow_natCast, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val, LatticeChain.coe_uniformizerAsUnit]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero N hne), one_mul]

/-- For the standard chain in `F^{n+1}`, the image of `U^N(𝔄)` in `GL_{n+1}(F)` lies in the
principal congruence subgroup of level `N`. -/
theorem unitSubgroup_stdChain_le (n N : ℕ) (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (hg : Matrix.GeneralLinearGroup.toLin g ∈ (LatticeChain.standard hϖ (Fin (n + 1))).unitFiltration N) :
    g ∈ Conductor.principalLevelSubgroup F n N := by
  rw [Conductor.principalLevelSubgroup, Conductor.mem_principalCongruenceSubgroup_iff]
  refine ⟨exists_mem_pow_of_mem_unitFiltration hϖ N g hg,
    exists_mem_pow_of_mem_unitFiltration hϖ N g⁻¹ ?_⟩
  rw [map_inv]
  exact inv_mem hg

end Standard

/-! ### Least elements of sets of multiples of `1 / D` -/

theorem exists_isLeast_of_mul_mem_nat {S : Set ℚ} {D : ℕ} (hD : 0 < D) (hS : S.Nonempty)
    (hint : ∀ x ∈ S, ∃ k : ℕ, x * D = k) : ∃ x, IsLeast S x := by
  classical
  have hT : ∃ k : ℕ, ∃ x ∈ S, x * D = k := by
    obtain ⟨x, hx⟩ := hS
    obtain ⟨k, hk⟩ := hint x hx
    exact ⟨k, x, hx, hk⟩
  obtain ⟨x0, hx0, hk0⟩ := Nat.find_spec hT
  refine ⟨x0, hx0, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hint x hx
  have hmin := Nat.find_min' hT ⟨x, hx, hk⟩
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have h : x0 * D ≤ x * D := by
    rw [hk0, hk]
    exact_mod_cast hmin
  exact le_of_mul_le_mul_right h hDq

/-! ### Proof of L0 -/

section Instances

local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- The normalized level values of a class of irreducible admissible representations of
`GL_{n+1}(K)` form a nonempty set. -/
theorem normalizedLevelValues_nonempty {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) (n : ℕ)
    (a : SmoothDualClass.{0, uK, uV} (k := ℂ) (G := GeneralLinear (n + 1) K.Carrier)) :
    (normalizedLevelValues K (n + 1) a).Nonempty := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep a
  have hirr : Representation.IsIrreducible A.obj.representation := A.property.1
  have : Nontrivial A.obj := by
    have : IsSimpleModule (MonoidAlgebra ℂ (GeneralLinear (n + 1) K.Carrier))
        A.obj.representation.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).mp hirr
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear (n + 1) K.Carrier))
      A.obj.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : A.obj)
  obtain ⟨K0, hK0⟩ := A.obj.isSmooth v
  obtain ⟨N, hN, hKN⟩ :=
    Conductor.exists_pos_principalLevelOpenSubgroup_subset K.Carrier n K0.mem_nhds_one
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K.Carrier]
  refine ⟨((N - 1 : ℕ) : ℚ) / (LatticeChain.standard hϖ (Fin (n + 1))).period, LatticeChain.standard hϖ (Fin (n + 1)),
    N - 1, rfl, ?_⟩
  rw [Nat.sub_add_cancel hN]
  show fixedVectors A.obj.representation _ ≠ ⊥
  rw [Submodule.ne_bot_iff]
  refine ⟨v, ?_, hv⟩
  refine (Representation.mem_invariants _ v).mpr fun h => ?_
  have hh : (h : GeneralLinear (n + 1) K.Carrier) ∈ K0 :=
    hKN (unitSubgroup_stdChain_le hϖ n N _ h.2)
  exact (Representation.mem_invariants _ v).mp hK0 ⟨h, hh⟩

/-- Every normalized level value of a class of `GL_n(K)` is an integer multiple of `1 / n!`. -/
theorem exists_mul_factorial_eq_of_mem_normalizedLevelValues {p : ℕ} [Fact p.Prime]
    (K : PadicField.{uK} p) (n : ℕ)
    (a : SmoothDualClass.{0, uK, uV} (k := ℂ) (G := GeneralLinear n K.Carrier)) :
    ∀ x ∈ normalizedLevelValues K n a, ∃ k : ℕ, x * (n.factorial : ℚ) = k := by
  rintro x ⟨𝓛, m, rfl, -⟩
  have hle : 𝓛.period ≤ n := by simpa using 𝓛.period_le_card
  obtain ⟨c, hc⟩ := Nat.dvd_factorial 𝓛.period_pos hle
  refine ⟨m * c, ?_⟩
  have hpos : (𝓛.period : ℚ) ≠ 0 := by exact_mod_cast 𝓛.period_pos.ne'
  rw [hc]
  push_cast
  field_simp

/-- **L0.** Every class of irreducible admissible representations of `GL_n(K)`, `n ≥ 1`, has a
normalized level. -/
theorem normalizedLevelExistence : NormalizedLevelExistenceStatement.{uK, uV} := by
  intro p _ K n hn a
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  exact exists_isLeast_of_mul_mem_nat (Nat.factorial_pos _)
    (normalizedLevelValues_nonempty K n a)
    (exists_mul_factorial_eq_of_mem_normalizedLevelValues K (n + 1) a)

end Instances

end Langlands.BushnellKutzko

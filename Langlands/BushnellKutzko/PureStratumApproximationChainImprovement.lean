import Langlands.BushnellKutzko.PureStratumApproximationImprovementSteps
import Langlands.BushnellKutzko.PureStratumApproximationMoyTransport
import Langlands.BushnellKutzko.PureStratumApproximationAssembly

/-! # BK93 (2.4.5): improving a simple approximation

Proof of the Library proposition `ChainImprovementPremise`, BK93 (2.4.5), printed pp. 67–69: if
the derived stratum of `β − γ` is non-fundamental or scalar fundamental, then `β` has a simple
approximation of strictly smaller normalized depth with the same field invariants.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uV uE

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem restrictScalars_algebraMap (x : E) :
    (algebraMap E (Module.End E V) x).restrictScalars F = subfieldEmbedding F E V x := by
  ext v
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem isNilpotent_restrictScalars {y : Module.End E V} (hy : IsNilpotent y) :
    IsNilpotent (y.restrictScalars F) := by
  obtain ⟨n, hn⟩ := hy
  refine ⟨n, ?_⟩
  ext v
  have h : (y.restrictScalars F ^ n) v = (y ^ n) v := by
    rw [Module.End.pow_apply, Module.End.pow_apply]
    rfl
  rw [h, hn]
  rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- If `y ∈ 𝔓^k` and `y − x` is nilpotent for a scalar `x` of a field normalizing the chain,
then `x ∈ 𝔓^k`: otherwise `y − x` would be a unit. -/
theorem subfieldEmbedding_mem_of_isNilpotent_sub (𝓛 : LatticeChain 𝒪[F] F V)
    (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer) {k : ℤ} {y : Module.End E V}
    (hy : y.restrictScalars F ∈ 𝓛.endFiltration k) {x : E}
    (hnil : IsNilpotent (y - algebraMap E (Module.End E V) x)) :
    subfieldEmbedding F E V x ∈ 𝓛.endFiltration k := by
  by_contra hx
  have hx0 : x ≠ 0 := by
    intro h
    apply hx
    rw [h, map_zero]
    exact zero_mem _
  have := 𝓛.nontrivialSpace
  let a := Units.mk0 x hx0
  have hd := subfieldEmbedding_unit_mem_iff 𝓛 hE a k
  have hlt : (𝓛.fieldShift E hE a).toAdd < k := by
    by_contra h
    exact hx (hd.mpr (not_lt.mp h))
  have hinv : subfieldEmbedding F E V ((a⁻¹ : Eˣ) : E) ∈
      𝓛.endFiltration (-(𝓛.fieldShift E hE a).toAdd) := by
    rw [subfieldEmbedding_unit_mem_iff 𝓛 hE a⁻¹, map_inv, toAdd_inv]
  set Xf := subfieldEmbedding F E V x with hXf
  set Xi := subfieldEmbedding F E V ((a⁻¹ : Eˣ) : E) with hXi
  have hai : ((a⁻¹ : Eˣ) : E) = x⁻¹ := by simp [a]
  have hXX : Xf * Xi = 1 := by
    rw [hXf, hXi, ← map_mul, hai, mul_inv_cancel₀ hx0, map_one]
  have hXX' : Xi * Xf = 1 := by
    rw [hXf, hXi, ← map_mul, hai, inv_mul_cancel₀ hx0, map_one]
  have hY : Xi * y.restrictScalars F ∈ 𝓛.endFiltration 1 := by
    have h := 𝓛.mul_mem_endFiltration hinv hy
    exact 𝓛.endFiltration_antitone (by omega) h
  obtain ⟨g, -, hg⟩ := 𝓛.exists_mem_unitFiltration (n := 1) le_rfl (neg_mem hY)
  have hN : (y - algebraMap E (Module.End E V) x).restrictScalars F =
      -(Xf * (1 + -(Xi * y.restrictScalars F))) := by
    have hs : (y - algebraMap E (Module.End E V) x).restrictScalars F =
        y.restrictScalars F - Xf := by
      ext v
      rfl
    rw [hs, mul_add, mul_one, mul_neg, ← mul_assoc, hXX, one_mul]
    abel
  have hunit : IsUnit ((y - algebraMap E (Module.End E V) x).restrictScalars F) := by
    rw [hN, ← hg]
    have hXu : IsUnit Xf := ⟨⟨Xf, Xi, hXX, hXX'⟩, rfl⟩
    exact (hXu.mul g.isUnit).neg
  exact (isNilpotent_restrictScalars hnil).not_isUnit hunit

/-- A scalar `x ∈ E` of valuation `−ρ` on a chain normalized by `E` gives the simple stratum
`[𝔅,ρ,ρ−1,x]` over `E`, on the chain over `𝔬_E` with the same lattices. Its critical exponent is
`−∞`. -/
theorem exists_scalar_simple [FiniteDimensional F E] (𝓜 : LatticeChain 𝒪[F] F V)
    (hM : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓜.stabilizer) {x : E} {ρ : ℤ}
    (hv : 𝓜.valuation (subfieldEmbedding F E V x) = ((-ρ : ℤ) : WithTop ℤ)) :
    ∃ C : Stratum (subfieldIntegers F E) E V,
      (∀ i, (C.chain.lattice i : Set V) = 𝓜.lattice i) ∧ C.n = ρ ∧ C.r = ρ - 1 ∧
      C.b = algebraMap E (Module.End E V) x ∧ C.IsSimple := by
  have := 𝓜.nontrivialSpace
  let M := 𝓜.subfieldChain E hM
  let X := algebraMap E (Module.End E V) x
  have hval : M.valuation X = ((-ρ : ℤ) : WithTop ℤ) := by
    rw [valuation_subfieldChain 𝓜 hM X, restrictScalars_algebraMap, hv]
  have hbot : elementAlgebra X = ⊥ :=
    le_antisymm (Algebra.adjoin_le (Set.singleton_subset_iff.mpr
      (Subalgebra.algebraMap_mem ⊥ x))) bot_le
  have hinj : Function.Injective (algebraMap E (Module.End E V)) := by
    intro a b hab
    obtain ⟨v, hv0⟩ := exists_ne (0 : V)
    have h := LinearMap.congr_fun hab v
    simp only [Module.algebraMap_end_apply] at h
    exact smul_left_injective E hv0 h
  have hfield : IsField (elementAlgebra X) :=
    ((Subalgebra.equivOfEq _ _ hbot).trans (Algebra.botEquivOfInjective hinj)).toMulEquiv.isField
      (Field.toIsField E)
  refine ⟨⟨M, ρ, ρ - 1, X, by omega, by rw [hval]; exact_mod_cast le_rfl⟩, fun i => rfl, rfl, rfl,
    rfl, ⟨⟨hfield, ?_⟩, ?_⟩, ?_⟩
  · let := hfield.toField
    intro a
    have hmem : ((a : elementAlgebra X) : Module.End E V) ∈ (⊥ : Subalgebra E _) :=
      hbot ▸ (a : elementAlgebra X).2
    obtain ⟨e, he⟩ := Algebra.mem_bot.mp hmem
    have he0 : e ≠ 0 := by
      intro h0
      apply a.ne_zero
      apply Subtype.ext
      rw [← he, h0, map_zero]
      rfl
    intro i
    obtain ⟨j, hj⟩ := hM (Units.mk0 e he0) i
    refine ⟨j, ?_⟩
    ext v
    have hj' := congrArg (fun P : Submodule 𝒪[F] V => v ∈ P) hj
    simp only [Submodule.mem_map] at hj' ⊢
    change (∃ w, w ∈ 𝓜.lattice i ∧ _) ↔ v ∈ 𝓜.lattice j
    rw [← eq_iff_iff.mp hj']
    refine exists_congr fun w => and_congr Iff.rfl ?_
    change ((a : elementAlgebra X) : Module.End E V) w = v ↔ e • w = v
    rw [← he]
    rfl
  · change M.valuation X = -(ρ : WithTop ℤ)
    rw [hval]
    rfl
  · change criticalExponent M X < _
    simp only [criticalExponent, elementAlgebra] at hbot ⊢
    rw [ite_eq_left hbot]
    exact WithBot.bot_lt_coe _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The scalars of the generated field `E = F[β]` lie in the generated algebra. -/
theorem subfieldEmbedding_mem_elementAlgebra {b : Module.End F V} {βE : E}
    (hβES : subfieldEmbedding F E V βE = b) (hβE : Algebra.adjoin F ({βE} : Set E) = ⊤)
    (e : E) : subfieldEmbedding F E V e ∈ elementAlgebra b := by
  have h1 : subfieldEmbedding F E V e ∈
      (Algebra.adjoin F ({βE} : Set E)).map (subfieldEmbedding F E V) :=
    Subalgebra.mem_map.mpr ⟨e, by rw [hβE]; exact Algebra.mem_top, rfl⟩
  rw [AlgHom.map_adjoin_singleton, hβES] at h1
  exact h1

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem adjoin_pair_eq_elementAlgebra {b c : Module.End F V} (hc : c ∈ elementAlgebra b) :
    Algebra.adjoin F ({b, c} : Set (Module.End F V)) = elementAlgebra b := by
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro y (rfl | rfl)
    · exact Algebra.self_mem_adjoin_singleton F y
    · exact hc
  · exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

/-- **BK93 (2.4.5)**, printed pp. 67–69, as the Library proposition `ChainImprovementPremise`.
If some element of the derived coset of `β − γ` differs from a scalar of `E = F[γ]` by a
nilpotent element, then `β` lies in the coset of a simple stratum of strictly smaller normalized
depth whose generated field has the ramification index and residue degree of `F[γ]`. -/
theorem chainImprovement : ChainImprovementPremise.{uF, uV, uE} := by
  intro F _ _ _ _ V _ _ _ E _ _ _ _ β S s D hD hns
  classical
  obtain ⟨hS, ⟨βE, hβES, hβE⟩, hb, hDlat, -, hDr, hDb⟩ := hD
  have := S.chain.finiteDimensional
  have : FiniteDimensional F E := S.chain.finiteDimensional_subfield E
  have hE := normalized_of_generated S hS.1 hβES hβE
  obtain ⟨x, y, hyD, hnil⟩ := hns
  have hpos : (0 : ℤ) < S.chain.period := by exact_mod_cast S.chain.period_pos
  have hy1 : (y - s (β - S.b)).restrictScalars F ∈ S.chain.endFiltration (1 - S.r) := by
    have h : y - D.b ∈ D.chain.endFiltration (-D.r) := hyD
    rw [hDb, hDr, show -(S.r - 1) = 1 - S.r by ring] at h
    exact (mem_endFiltration_restrictScalars hDlat).mp h
  have hsb : (s (β - S.b)).restrictScalars F ∈ S.chain.endFiltration (-S.r) := by
    have h := (tameCorestriction F V E).2.2 s S.chain hE (-S.r)
    have hmem : s (β - S.b) ∈ s '' (S.chain.endFiltration (-S.r) : Set (Module.End F V)) :=
      ⟨_, hb, rfl⟩
    rw [h] at hmem
    exact hmem
  have hsubF : ∀ u w : Module.End E V,
      (u - w).restrictScalars F = u.restrictScalars F - w.restrictScalars F :=
    fun u w => rfl
  have haddF : ∀ u w : Module.End E V,
      (u + w).restrictScalars F = u.restrictScalars F + w.restrictScalars F :=
    fun u w => rfl
  have hyr : y.restrictScalars F ∈ S.chain.endFiltration (-S.r) := by
    have h := add_mem (S.chain.endFiltration_antitone (by omega : -S.r ≤ 1 - S.r) hy1) hsb
    rwa [hsubF, sub_add_cancel] at h
  set X := algebraMap E (Module.End E V) x with hX
  have hXF : X.restrictScalars F = subfieldEmbedding F E V x := restrictScalars_algebraMap x
  set z := s (β - S.b) - X with hz_def
  have hXr : subfieldEmbedding F E V x ∈ S.chain.endFiltration (-S.r) :=
    subfieldEmbedding_mem_of_isNilpotent_sub S.chain hE hyr hnil
  have hz : z.restrictScalars F ∈ S.chain.endFiltration (-S.r) := by
    rw [hz_def, hsubF, hXF]
    exact sub_mem hsb hXr
  have hyz : ((y - X) - z).restrictScalars F ∈ S.chain.endFiltration (-S.r + 1) := by
    have h : (y - X) - z = y - s (β - S.b) := by rw [hz_def]; abel
    rw [h, show -S.r + 1 = 1 - S.r by ring]
    exact hy1
  obtain ⟨𝓜, j', hM, hcos, hlt, hsw⟩ :=
    exists_compatible_chain_of_isNilpotent S.chain hE hz hnil hyz
  have hz𝓜 : z.restrictScalars F ∈ 𝓜.endFiltration j' :=
    hcos z (by rw [sub_self]; exact zero_mem _)
  have hQ' : ∀ w : Module.End E V, w.restrictScalars F ∈ S.chain.endFiltration (1 - S.r) →
      w.restrictScalars F ∈ 𝓜.endFiltration j' := by
    intro w hw
    have h1 := hcos (z + w) (by rwa [add_sub_cancel_left, show -S.r + 1 = 1 - S.r by ring])
    have h2 := sub_mem h1 hz𝓜
    rwa [← hsubF, add_sub_cancel_left] at h2
  by_cases hX1 : subfieldEmbedding F E V x ∈ S.chain.endFiltration (1 - S.r)
  · -- the non-fundamental case
    have hsb𝓜 : (s (β - S.b)).restrictScalars F ∈ 𝓜.endFiltration (-(-j')) := by
      have h := add_mem hz𝓜 (hQ' X (by rw [hXF]; exact hX1))
      rw [neg_neg]
      rwa [← haddF, hz_def, sub_add_cancel] at h
    have hρ : -j' * S.chain.period < S.r * 𝓜.period := by linarith
    obtain ⟨T, hTc, hTr, hT, hβT, he, hf⟩ :=
      exists_improvement_of_le S hS hβES hβE s hb 𝓜 hM hsw hρ hsb𝓜
        (fun w hw => by rw [neg_neg]; exact hQ' w hw)
    refine ⟨T, hT, hβT, ?_, he, hf⟩
    rw [hTr, hTc]
    exact hρ
  · -- the scalar fundamental case
    have hx0 : x ≠ 0 := by
      intro h
      apply hX1
      rw [h, map_zero]
      exact zero_mem _
    have hvL : S.chain.valuation (subfieldEmbedding F E V x) = ((-S.r : ℤ) : WithTop ℤ) :=
      S.chain.valuation_eq_of_mem_of_notMem hXr (by rwa [show -S.r + 1 = 1 - S.r by ring])
    obtain ⟨ρ, hvM, hρ⟩ := exists_valuation_of_normalized S.chain hE 𝓜 hM hx0 hvL
    obtain ⟨C, hClat, hCn, hCr, hCb, hC⟩ := exists_scalar_simple 𝓜 hM hvM
    have hj : 1 - ρ ≤ j' := by
      have h1 : -ρ * S.chain.period < j' * S.chain.period := by nlinarith
      have h2 : -ρ < j' := lt_of_mul_lt_mul_right h1 hpos.le
      omega
    have hsC : s (β - S.b) ∈ C.coset := by
      change s (β - S.b) - C.b ∈ C.chain.endFiltration (-C.r)
      rw [hCb, hCr, show -(ρ - 1) = 1 - ρ by ring, mem_endFiltration_restrictScalars hClat]
      exact 𝓜.endFiltration_antitone hj hz𝓜
    obtain ⟨T, U, -, hUc, -, -, hUr, -, -, hU, hβU, -, -, he, hf, -⟩ :=
      exists_refinement_of_coset S hS hβES hβE s hb 𝓜 hM hsw hρ C hClat hCn hCr hC hsC
        (fun w hw => 𝓜.endFiltration_antitone hj (hQ' w hw))
    have hpair : Algebra.adjoin F ({S.b, C.b.restrictScalars F} : Set (Module.End F V)) =
        elementAlgebra S.b := by
      rw [hCb, hXF]
      exact adjoin_pair_eq_elementAlgebra (subfieldEmbedding_mem_elementAlgebra hβES hβE x)
    rw [hpair] at he hf
    refine ⟨U, hU, hβU, ?_, he, hf⟩
    rw [hUr, hUc]
    linarith

end Langlands.BushnellKutzko.PureApproximation

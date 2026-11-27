import Langlands.BushnellKutzko.SupercuspidalConductorRankLowerBoundStatement
import Langlands.BushnellKutzko.NormalizedLevelExistenceProof
import Langlands.BushnellKutzko.FundamentalStratumLevelCore
import Langlands.BushnellKutzko.SwanLevelHigherRank

/-! # Reduction of the supercuspidal conductor lower bound to depth zero

At positive normalized level, the higher-rank Swan formula gives the lower bound by rank for
the conductor of a supercuspidal class (`supercuspidalConductorRankLowerBound_of_depthZero`).
At normalized level zero, the bound follows from the proposition
`StandardDepthZeroShellNonzero`: the integral over the extreme determinant shell of the
standard first-unit test function is nonzero for a suitable smooth functional
(`supercuspidalConductorRankLowerBoundAtDepthZero_of_nonzeroShell`). The module
`Langlands.BushnellKutzko.DepthZeroShell` proves that proposition from finite matrix Gauss
injectivity.
-/

noncomputable section

namespace Langlands.BushnellKutzko

universe uK uV

open Correspondence Henniart.Numerical HarmonicAnalysis MeasureTheory ValuativeRel
open scoped Pointwise

local instance {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

local instance {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel

local instance {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) :
    IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField

local instance {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) :
    TotallyDisconnectedSpace K.Carrier := by
  let : NonarchimedeanRing K.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing K.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local instance {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) : MeasurableSpace K.Carrier :=
  borel _

local instance {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) : BorelSpace K.Carrier :=
  ⟨rfl⟩

local instance {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) (n : ℕ) :
    MeasurableSpace (GeneralLinear n K.Carrier) :=
  borel _

local instance {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) (n : ℕ) :
    BorelSpace (GeneralLinear n K.Carrier) :=
  ⟨rfl⟩

private theorem mem_endFiltration_one_of_maps_initial_lattice
    {F : Type uK} [Field F] [TopologicalSpace F] [ValuativeRel F]
    [IsNonarchimedeanLocalField F] {ι : Type*}
    (𝓛 : LatticeChain 𝒪[F] F (ι → F)) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {x : Module.End F (ι → F)}
    (h : ∀ v ∈ 𝓛.lattice 0, x v ∈ 𝓛.lattice (𝓛.period : ℤ)) :
    x ∈ 𝓛.endFiltration 1 := by
  intro i v hv
  let e : ℤ := 𝓛.period
  let q : ℤ := i / e
  let r : ℤ := i % e
  have he : 0 < e := Int.natCast_pos.mpr 𝓛.period_pos
  have hr : 0 ≤ r := Int.emod_nonneg _ he.ne'
  have hre : r < e := Int.emod_lt_of_pos _ he
  have hi : r - e * (-q) = i := by
    simp only [r, q, mul_neg, sub_neg_eq_add, Int.emod_add_mul_ediv]
  have hv' : (ϖ : F) ^ (-q) • v ∈ 𝓛.lattice r :=
    (𝓛.zpow_smul_mem_iff hϖ (-q)).mpr (by rwa [hi])
  have hx : x ((ϖ : F) ^ (-q) • v) ∈ 𝓛.lattice (r + 1) :=
    𝓛.antitone (show r + 1 ≤ e by omega) (h _ (𝓛.antitone hr hv'))
  rw [map_smul] at hx
  have hx' := (𝓛.zpow_smul_mem_iff hϖ (-q)).mp hx
  rwa [show r + 1 - (𝓛.period : ℤ) * (-q) = i + 1 by
    change r + 1 - e * (-q) = i + 1
    linarith only [hi]] at hx'

/-- A nonzero vector fixed by the first unit group of a lattice chain gives a nonzero
vector fixed by the first unit group of the standard chain. -/
theorem exists_fixedVector_standard_of_unitSubgroup_one
    {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V)
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin (n + 1) → K.Carrier))
    {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ)
    {v : V} (hv : v ≠ 0) (hfix : ∀ g ∈ unitSubgroup K 𝓛 1, σ g v = v) :
    ∃ w : V, w ≠ 0 ∧ ∀ g ∈ unitSubgroup K (LatticeChain.standard hϖ (Fin (n + 1))) 1,
      σ g w = w := by
  classical
  let 𝓢 := LatticeChain.standard hϖ (Fin (n + 1))
  have h𝓢0 : 𝓢.lattice 0 = LatticeChain.standardLattice K.Carrier (Fin (n + 1)) := by
    simp only [𝓢, stdChain_lattice, zpow_zero, one_smul]
  have hrank : Module.finrank 𝒪[K.Carrier] (𝓛.lattice 0) = n + 1 := by
    rw [Submodule.IsLattice.finrank_of_pi K.Carrier, Fintype.card_fin]
  let b := Module.finBasisOfFinrankEq 𝒪[K.Carrier] (𝓛.lattice 0) hrank
  let bF := b.extendOfIsLattice K.Carrier
  let P : GeneralLinear (n + 1) K.Carrier := Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv bF.equivFun.symm)
  have hforward (x : Fin (n + 1) → K.Carrier) (hx : x ∈ 𝓢.lattice 0) :
      bF.equivFun.symm x ∈ 𝓛.lattice 0 := by
    have hx' : ∀ j, x j ∈ 𝒪[K.Carrier] := by
      rwa [h𝓢0, LatticeChain.mem_standardLattice] at hx
    rw [Module.Basis.equivFun_symm_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    change (⟨x j, hx' j⟩ : 𝒪[K.Carrier]) • bF j ∈ _
    exact Submodule.smul_mem _ _ (by simp [bF, Module.Basis.extendOfIsLattice_apply])
  have hback (x : Fin (n + 1) → K.Carrier) (hx : x ∈ 𝓛.lattice 0) :
      bF.equivFun x ∈ 𝓢.lattice 0 := by
    rw [h𝓢0, LatticeChain.mem_standardLattice]
    exact fun j => 𝓛.repr_extendOfIsLattice_mem b hx j
  have hconj (g : GeneralLinear (n + 1) K.Carrier) (hg : g ∈ unitSubgroup K 𝓢 1) :
      P * g * P⁻¹ ∈ unitSubgroup K 𝓛 1 := by
    let A : Module.End K.Carrier (Fin (n + 1) → K.Carrier) :=
      ((Matrix.GeneralLinearGroup.toLin g :
        LinearMap.GeneralLinearGroup K.Carrier (Fin (n + 1) → K.Carrier)) :
        Module.End K.Carrier (Fin (n + 1) → K.Carrier))
    have hA : A - 1 ∈ 𝓢.endFiltration 1 := by
      rw [mem_unitSubgroup_iff_sub_one_mem K 𝓢 le_rfl, LatticeChain.mem_matrixFiltration,
        toLin'_sub_one] at hg
      exact hg
    rw [mem_unitSubgroup_iff_sub_one_mem K 𝓛 le_rfl, LatticeChain.mem_matrixFiltration,
      toLin'_sub_one]
    apply mem_endFiltration_one_of_maps_initial_lattice 𝓛 hϖ
    intro x hx
    have hy : (A - 1) (bF.equivFun x) ∈ 𝓢.lattice 1 := by
      simpa only [zero_add] using hA 0 (bF.equivFun x) (hback x hx)
    rw [show 𝓢.lattice 1 = (LatticeChain.uniformizerAsUnit hϖ) •
      LatticeChain.standardLattice K.Carrier (Fin (n + 1)) by
      simp only [𝓢, stdChain_lattice, zpow_one]] at hy
    obtain ⟨y, hy, hxy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    have hy' : bF.equivFun.symm ((A - 1) (bF.equivFun x)) ∈ 𝓛.lattice (𝓛.period : ℤ) := by
      rw [← hxy]
      change bF.equivFun.symm ((ϖ : K.Carrier) • y) ∈ _
      rw [map_smul, 𝓛.uniformizer_smul_mem_iff hϖ, sub_self]
      apply hforward
      rwa [h𝓢0]
    rw [← coe_toLin_eq_toLin', map_mul, map_mul, map_inv]
    simp only [P, MulEquiv.apply_symm_apply, Units.val_mul, Module.End.mul_apply,
      LinearMap.sub_apply, Module.End.one_apply]
    change bF.equivFun.symm (A (bF.equivFun x)) - x ∈ 𝓛.lattice (𝓛.period : ℤ)
    simpa only [LinearMap.sub_apply, Module.End.one_apply, map_sub, LinearEquiv.symm_apply_apply]
      using hy'
  refine ⟨σ P⁻¹ v, ?_, fun g hg => ?_⟩
  · intro hz
    apply hv
    have heq := congrArg (σ P) hz
    rw [map_zero, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] at heq
    exact heq
  · rw [← Module.End.mul_apply, ← map_mul,
      show g * P⁻¹ = P⁻¹ * (P * g * P⁻¹) by group,
      map_mul, Module.End.mul_apply, hfix _ (hconj g hg)]

/-- The lower bound on classes of normalized level zero and rank at least two. -/
def SupercuspidalConductorRankLowerBoundAtDepthZero : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k : ℕ)
    (π : SupercuspidalAutomorphicClass.{uK,uV} K (k + 1).succPNat),
    IsNormalizedLevel K (k + 2) (GeneralLinear.SupercuspidalClass.toSmoothDualClass π) 0 →
    ((k + 2 : ℕ) : WithTop ℕ) ≤ conductor K π

/-- The extreme determinant shell of the standard depth-zero test is nonzero
for a suitable smooth dual functional on each nonzero fixed vector. -/
def StandardDepthZeroShellNonzero : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (n : ℕ)
    (ψ : UnitaryAdditiveCharacter K.Carrier) (_ : Conductor.HasIntegerConductor ψ)
    (ν : AdditiveHaarMeasure K.Carrier) [SigmaFinite ν.measure]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V) (_ : IsSmooth σ)
    {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ) (w : smoothVectors σ) (_ : w.val ≠ 0),
    let 𝓢 := LatticeChain.standard hϖ (Fin (n + 1))
    (∀ g ∈ unitSubgroup K 𝓢 1, σ g w.val = w.val) →
    ∃ ℓ : SmoothDual σ,
      (∫ g in {g : GeneralLinear (n + 1) K.Carrier |
          K.canonicalTopologicalData.ord (Matrix.det g.val) = -(n + 1 : ℤ)},
        rectangularFourierIntegral ψ ν (stratumTest K 𝓢 le_rfl ψ 0) g.val *
          GodementJacquet.coefficientIota (stratumCoefficient K σ ℓ w).val g
          ∂(RankinSelberg.generalLinearHaar K.Carrier n)) ≠ 0

private theorem exponent_eq_rank_of_standard_fixedVector
    (hShell : StandardDepthZeroShellNonzero.{uK,uV})
    {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) {n : ℕ}
    (ψ : UnitaryAdditiveCharacter K.Carrier) (hψ : Conductor.HasIntegerConductor ψ)
    (ν : AdditiveHaarMeasure K.Carrier) [SigmaFinite ν.measure]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V) (hσ : IsSmooth σ)
    (c : ℂˣ) (a : ℤ)
    (hFE : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData K ψ ν σ 1 1 c a)
    {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ) {v : V} (hv : v ≠ 0)
    (hfix : ∀ g ∈ unitSubgroup K (LatticeChain.standard hϖ (Fin (n + 1))) 1, σ g v = v) :
    a = (n + 1 : ℤ) := by
  let T := K.canonicalTopologicalData
  let 𝓢 := LatticeChain.standard hϖ (Fin (n + 1))
  let w : smoothVectors σ := ⟨v, hσ v⟩
  obtain ⟨ℓ, hℓ⟩ := hShell p K n ψ hψ ν σ hσ hϖ w hv hfix
  let Φ := stratumTest K 𝓢 (k := 1) le_rfl ψ 0
  have hw (g) (hg : g ∈ unitSubgroup K 𝓢 1) :
      σ g w.val = ψ.complex (((0 : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier) *
        (g.val - 1)).trace) • w.val := by
    simpa only [zero_mul, Matrix.trace_zero, AddChar.map_zero_eq_one, one_smul] using hfix g hg
  have hR := hasShiftedRationalValue_stratumTest K 𝓢 le_rfl ψ 0 σ ℓ w hw
  let t : K.Carrier := (ϖ : K.Carrier)⁻¹
  have ht : t ≠ 0 := inv_ne_zero (coe_uniformizer_ne_zero hϖ)
  have htord : T.ord t = -1 := by
    rw [show t = (ϖ : K.Carrier)⁻¹ by rfl, T.ord_inv, ord_coe_of_irreducible K hϖ]
  have hsupp (g : GeneralLinear (n + 1) K.Carrier)
      (hg : rectangularFourierIntegral ψ ν Φ g.val ≠ 0) :
      -(n + 1 : ℤ) ≤ T.ord (Matrix.det g.val) := by
    have hmem := toLin'_inv_smul_transpose_mem_of_fourier_ne_zero K ψ ν 𝓢
      (k := 1) le_rfl 0 ht (exists_scaledCharacter_ne_one K hψ hϖ)
      (j := 0) (by norm_num) (by simp) g.val hg
    have hdet : (t⁻¹ • g.val.transpose).det ≠ 0 := by
      rw [Matrix.det_smul, Matrix.det_transpose]
      exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) g.det_ne_zero
    have h := card_mul_le_period_mul_ord_det K 𝓢 hmem hdet
    rw [ord_det_inv_smul_transpose K ht g, htord, mul_neg_one, sub_neg_eq_add, mul_zero] at h
    have hpos : (0 : ℤ) < 𝓢.period := Int.natCast_pos.mpr 𝓢.period_pos
    have hge := nonneg_of_mul_nonneg_right h hpos
    change -(n + 1 : ℤ) ≤ K.canonicalTopologicalData.ord (Matrix.det g.val)
    push_cast at hge
    omega
  by_contra hne
  have hshell : -(n + 1 : ℤ) ≠ -a := by omega
  have h := setIntegral_ord_det_of_monomial_functionalEquation K ψ ν σ c a hFE
    Φ (-(n + 1 : ℤ)) hsupp (stratumCoefficient K σ ℓ w) _ hR (-(n + 1 : ℤ))
  rw [ite_eq_right hshell] at h
  exact hℓ h

/-- The depth-zero conductor lower bound follows from a nonzero extreme shell of
the standard test function. -/
theorem supercuspidalConductorRankLowerBoundAtDepthZero_of_nonzeroShell
    (hShell : StandardDepthZeroShellNonzero.{uK,uV}) :
    SupercuspidalConductorRankLowerBoundAtDepthZero.{uK,uV} := by
  intro p _ K k π hlev
  obtain ⟨A, rfl⟩ := Quotient.exists_rep π
  obtain ⟨𝓛, m, hm, hfix⟩ := hlev.1
  have he : (0 : ℚ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
  have hm₀ : m = 0 := by
    rw [eq_comm, div_eq_zero_iff] at hm
    exact_mod_cast hm.resolve_right he.ne'
  subst m
  obtain ⟨v, hv, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K.Carrier]
  obtain ⟨w, hw, hwfix⟩ := exists_fixedVector_standard_of_unitSubgroup_one K
    A.obj.representation 𝓛 hϖ hv₀
    (fun g hg => (mem_fixedVectors_iff_forall_mem _ _ v).1 hv g hg)
  obtain ⟨ψ₀⟩ := padicUnitaryAdditiveCharacterExists K K.canonicalTopologicalData
  obtain ⟨u, hψ⟩ := RankinSelberg.UnramifiedUnitary.exists_scale_hasIntegerConductor K ψ₀
  obtain ⟨ν⟩ := RankinSelberg.HighlyRamified.nonempty_selfDualHaar K (ψ₀.scale u)
  have : SigmaFinite ν.1.measure := selfDualSigmaFinite K.Carrier (ψ₀.scale u) ν.1 ν.2
  obtain ⟨c, a, hFE⟩ := GodementJacquet.Padic.exists_supercuspidalMatrixFunctionalEquationData
    K (Nat.succ_pos k) (ψ₀.scale u) ν.1 ν.2 A.obj.representation A.property.2 A.property.1
  have ha := exponent_eq_rank_of_standard_fixedVector hShell K (ψ₀.scale u) hψ ν.1
    A.obj.representation A.obj.isSmooth c a hFE hϖ hw hwfix
  obtain ⟨b, hb, hlevel⟩ := exists_exponent_eq_firstFixedLevel K (ψ₀.scale u) hψ ν.1 ν.2
    (Nat.succ_pos k) A c a hFE
  change conductor K A.isoClass = (b : WithTop ℕ) at hlevel
  change ((k + 2 : ℕ) : WithTop ℕ) ≤ conductor K A.isoClass
  have hge : k + 2 ≤ b := by omega
  rw [hlevel]
  exact WithTop.coe_le_coe.mpr hge

/-- Positive normalized level gives positive truncated Swan conductor. -/
theorem supercuspidalConductorRankLowerBound_of_depthZero
    (hZero : SupercuspidalConductorRankLowerBoundAtDepthZero.{uK,uV}) :
    SupercuspidalConductorRankLowerBoundStatement.{uK,uV} := by
  intro p _ K k π
  obtain ⟨x, hx⟩ := normalizedLevelExistence p K (k + 2) (by omega)
    (GeneralLinear.SupercuspidalClass.toSmoothDualClass π)
  have hx_nonneg : 0 ≤ x := by
    obtain ⟨chain, m, heq, _⟩ := hx.1
    rw [heq]
    positivity
  rcases hx_nonneg.eq_or_lt with heq | hx_pos
  · subst x
    exact hZero p K k π hx
  · obtain ⟨a, ha, hformula⟩ := exists_firstFixedLevel_eq_of_isNormalizedLevel K
      (Nat.succ_pos k) π hx
    change conductor K π = (a : WithTop ℕ) at ha
    rw [ha]
    have hge : k + 2 ≤ a := by
      by_contra! h
      change ((a - (k + 2) : ℕ) : ℚ) = ((k + 2 : ℕ) : ℚ) * x at hformula
      rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero] at hformula
      have hpos := mul_pos (by positivity : (0 : ℚ) < ((k + 2 : ℕ) : ℚ)) hx_pos
      exact (ne_of_gt hpos) hformula.symm
    exact WithTop.coe_le_coe.mpr hge

/-- The higher-rank conductor lower bound follows from the depth-zero shell
calculation. -/
theorem supercuspidalConductorRankLowerBound_of_nonzeroShell
    (hShell : StandardDepthZeroShellNonzero.{uK,uV}) :
    SupercuspidalConductorRankLowerBoundStatement.{uK,uV} :=
  supercuspidalConductorRankLowerBound_of_depthZero
    (supercuspidalConductorRankLowerBoundAtDepthZero_of_nonzeroShell hShell)

end Langlands.BushnellKutzko

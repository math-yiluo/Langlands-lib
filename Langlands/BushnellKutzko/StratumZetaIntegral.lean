import Langlands.BushnellKutzko.FourierSupport
import Langlands.BushnellKutzko.FundamentalStratumLevelCore
import Langlands.Representation.GodementJacquet.MatrixUnitValueProof
import Langlands.Representation.RankinSelberg.TwoBlockDeformationNonvanishing

/-! # The zeta integral of the test function attached to a stratum

Let `K` be a `p`-adic field, `𝓛` a lattice chain in `K^{n+1}`, `k ≥ 1`, `ψ` a unitary additive
character of `K` and `b'` an `(n+1) × (n+1)` matrix. The *stratum test function* is the twisted
indicator `Φ(y) = 1[y - 1 ∈ 𝔓^k(𝓛)] ψ(-tr(b' (y - 1)))` of the module `FourierSupport`. It is a
Schwartz–Bruhat function on the full matrix space (`stratumTest`), because the set
`1 + 𝔓^k(𝓛)` is the image of the compact open subgroup `U^k(𝔄(𝓛))` of `GL_{n+1}(K)`
(`image_val_unitSubgroup`) and `ψ` is locally constant.

If `w` is a smooth vector with `σ(g) w = ψ(tr(b' (g - 1))) w` for `g ∈ U^k(𝔄(𝓛))` and `ℓ` a
smooth functional, then the Godement–Jacquet integrand of `Φ` against the coefficient
`g ↦ ℓ(σ(g) w)` is the constant `ℓ(w)` on `U^k(𝔄(𝓛))` and zero elsewhere. Hence the matrix
integral converges for every `s` and equals `vol(U^k(𝔄(𝓛))) ℓ(w)`
(`matrixIntegral_stratumTest`), and the shifted integral has the constant rational value
`vol(U^k(𝔄(𝓛))) ℓ(w)` (`hasShiftedRationalValue_stratumTest`).

This belongs to the analytic part of the proof of T2 (see `ConductorFormula`).
-/

noncomputable section

open MeasureTheory Topology Langlands.HarmonicAnalysis ValuativeRel
open scoped ENNReal NNReal

namespace Langlands.BushnellKutzko

universe uK uV

/-! ### Matrices of the unit subgroups -/

section Matrices

variable {F : Type*} [Field F] {N : ℕ}

omit [Field F] in
theorem toLin'_sub_one {R : Type*} [CommRing R] (y : Matrix (Fin N) (Fin N) R) :
    Matrix.toLin' (y - 1) = Matrix.toLin' y - 1 := by
  rw [map_sub, Matrix.toLin'_one, Module.End.one_eq_id]

theorem coe_toLin_eq_toLin' (g : Matrix.GeneralLinearGroup (Fin N) F) :
    ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup F (Fin N → F)) :
      Module.End F (Fin N → F)) = Matrix.toLin' g.val := by
  rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.toLin'_apply']

end Matrices

section Padic

local instance szTopologicalSpace {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance szValuativeRel {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance szLocalField {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

local instance szT2 {p : ℕ} [Fact p.Prime] (F : PadicField p) : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2

local instance szGLMeasurable {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) :=
  borel _

local instance szGLBorel {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) :=
  ⟨rfl⟩

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- For `k ≥ 1`, an element `g` of `GL_N(K)` lies in `U^k(𝔄(𝓛))` exactly when
`g - 1 ∈ 𝔓^k(𝓛)`. -/
theorem mem_unitSubgroup_iff_sub_one_mem {N : ℕ}
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin N → K.Carrier)) {k : ℕ} (hk : 1 ≤ k)
    (g : GeneralLinear N K.Carrier) :
    g ∈ unitSubgroup K 𝓛 k ↔ g.val - 1 ∈ 𝓛.matrixFiltration k := by
  rw [mem_unitSubgroup, LatticeChain.mem_matrixFiltration, toLin'_sub_one]
  constructor
  · intro hg
    have h := hg.2.2
    rwa [coe_toLin_eq_toLin'] at h
  · intro hg
    obtain ⟨u, hu, hu'⟩ := 𝓛.exists_mem_unitFiltration hk hg
    have hgu : Matrix.GeneralLinearGroup.toLin g = u := by
      apply Units.ext
      rw [coe_toLin_eq_toLin', hu']
      abel
    rw [hgu]
    exact hu

/-- For `k ≥ 1`, the matrices of `U^k(𝔄(𝓛))` are exactly the `y` with `y - 1 ∈ 𝔓^k(𝓛)`. -/
theorem image_val_unitSubgroup {N : ℕ}
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin N → K.Carrier)) {k : ℕ} (hk : 1 ≤ k) :
    Units.val '' (unitSubgroup K 𝓛 k : Set (GeneralLinear N K.Carrier)) =
      {y | y - 1 ∈ 𝓛.matrixFiltration k} := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_unitSubgroup_iff_sub_one_mem K 𝓛 hk g).1 hg
  · intro hy
    have hy' : Matrix.toLin' (y - 1) ∈ 𝓛.endFiltration k := hy
    obtain ⟨u, -, hu'⟩ := 𝓛.exists_mem_unitFiltration hk hy'
    have hunit : IsUnit (Matrix.toLinAlgEquiv' y) := by
      have h : Matrix.toLinAlgEquiv' y = (u : Module.End K.Carrier (Fin N → K.Carrier)) := by
        rw [hu', toLin'_sub_one]
        ext v i
        simp [Matrix.toLin'_apply]
      rw [h]
      exact u.isUnit
    have hy : IsUnit y := (MulEquiv.isUnit_map (Matrix.toLinAlgEquiv' (R := K.Carrier)
      (n := Fin N))).1 hunit
    refine ⟨hy.unit, ?_, hy.unit_spec⟩
    rw [SetLike.mem_coe, mem_unitSubgroup_iff_sub_one_mem K 𝓛 hk, hy.unit_spec]
    exact hy'

/-- For `k ≥ 1`, the set `1 + 𝔓^k(𝓛)` of matrices is open. -/
theorem isOpen_one_add_matrixFiltration {n : ℕ}
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin (n + 1) → K.Carrier)) {k : ℕ}
    (hk : 1 ≤ k) :
    IsOpen {y : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier | y - 1 ∈ 𝓛.matrixFiltration k} := by
  rw [← image_val_unitSubgroup K 𝓛 hk]
  exact (RankinSelberg.isOpenEmbedding_generalLinear_val (n + 1)).isOpenMap _
    (isOpen_unitSubgroup K 𝓛 k)

/-- For `k ≥ 1`, the set `1 + 𝔓^k(𝓛)` of matrices is compact. -/
theorem isCompact_one_add_matrixFiltration {n : ℕ}
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin (n + 1) → K.Carrier)) {k : ℕ}
    (hk : 1 ≤ k) :
    IsCompact {y : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier |
      y - 1 ∈ 𝓛.matrixFiltration k} := by
  rw [← image_val_unitSubgroup K 𝓛 hk]
  exact (isCompact_unitSubgroup K 𝓛 k).image Units.continuous_val

/-- A function `y ↦ ψ(L y)` with `L` continuous and additive is locally constant. -/
theorem isLocallyConstant_character_comp {X : Type*} [TopologicalSpace X] [AddGroup X]
    (ψ : UnitaryAdditiveCharacter K.Carrier) (L : X →+ K.Carrier) (hL : Continuous L) :
    IsLocallyConstant fun y => ψ.complex (L y) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y => L y - L x := hL.sub continuous_const
  have h0 : (fun y => L y - L x) x = 0 := sub_self _
  have hmem := hc.continuousAt.preimage_mem_nhds
    (h0 ▸ RankinSelberg.TwoBlockDeformation.character_eq_one_mem_nhds K ψ)
  filter_upwards [hmem] with y hy
  have hy' : ψ.complex (L y - L x) = 1 := hy
  rw [show L y = (L y - L x) + L x by abel, AddChar.map_add_eq_mul, hy', one_mul]

/-- The stratum test function is locally constant. -/
theorem isLocallyConstant_twistedIndicator {n : ℕ}
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin (n + 1) → K.Carrier)) {k : ℕ}
    (hk : 1 ≤ k) (ψ : UnitaryAdditiveCharacter K.Carrier)
    (b' : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier) :
    IsLocallyConstant (twistedIndicator ψ (𝓛.matrixFiltration k) b') := by
  set S := {y : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier | y - 1 ∈ 𝓛.matrixFiltration k}
  have hSo : IsOpen S := isOpen_one_add_matrixFiltration K 𝓛 hk
  have hSc : IsClosed S := (isCompact_one_add_matrixFiltration K 𝓛 hk).isClosed
  let L : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier →+ K.Carrier :=
    { toFun := fun y => -(b' * y).trace
      map_zero' := by simp
      map_add' := fun y z => by rw [Matrix.mul_add, Matrix.trace_add, neg_add] }
  have hL : Continuous L := by
    change Continuous fun y : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier => -(b' * y).trace
    exact (continuous_const.matrix_mul continuous_id).matrix_trace.neg
  have hχ := isLocallyConstant_character_comp K ψ L hL
  rw [IsLocallyConstant.iff_eventually_eq] at hχ ⊢
  intro x
  by_cases hx : x ∈ S
  · have h1 := hχ (x - 1)
    have h2 : Filter.Tendsto (fun y : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier => y - 1) (𝓝 x)
        (𝓝 (x - 1)) := (continuous_id.sub continuous_const).tendsto x
    filter_upwards [hSo.mem_nhds hx, h2.eventually h1] with y hy hy1
    rw [twistedIndicator_apply_of_mem ψ _ b' hy, twistedIndicator_apply_of_mem ψ _ b' hx]
    exact hy1
  · filter_upwards [hSc.isOpen_compl.mem_nhds hx] with y hy
    rw [twistedIndicator_apply_of_not_mem ψ _ b' (show y - 1 ∉ 𝓛.matrixFiltration k from hy),
      twistedIndicator_apply_of_not_mem ψ _ b' (show x - 1 ∉ 𝓛.matrixFiltration k from hx)]

/-- The stratum test function has compact support. -/
theorem hasCompactSupport_twistedIndicator {n : ℕ}
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin (n + 1) → K.Carrier)) {k : ℕ}
    (hk : 1 ≤ k) (ψ : UnitaryAdditiveCharacter K.Carrier)
    (b' : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier) :
    HasCompactSupport (twistedIndicator ψ (𝓛.matrixFiltration k) b') :=
  HasCompactSupport.intro (isCompact_one_add_matrixFiltration K 𝓛 hk) fun _ hy =>
    twistedIndicator_apply_of_not_mem ψ _ b' hy

/-- The stratum test function `y ↦ 1[y - 1 ∈ 𝔓^k(𝓛)] ψ(-tr(b' (y - 1)))`, as a Schwartz–Bruhat
function on the `(n+1) × (n+1)` matrices. -/
def stratumTest {n : ℕ} (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin (n + 1) → K.Carrier))
    {k : ℕ} (hk : 1 ≤ k) (ψ : UnitaryAdditiveCharacter K.Carrier)
    (b' : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier) :
    GodementJacquet.MatrixTestFunction n K.Carrier :=
  ⟨twistedIndicator ψ (𝓛.matrixFiltration k) b',
    isLocallyConstant_twistedIndicator K 𝓛 hk ψ b',
    hasCompactSupport_twistedIndicator K 𝓛 hk ψ b'⟩

theorem stratumTest_apply {n : ℕ}
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin (n + 1) → K.Carrier)) {k : ℕ}
    (hk : 1 ≤ k) (ψ : UnitaryAdditiveCharacter K.Carrier)
    (b' : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier)
    (y : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier) :
    stratumTest K 𝓛 hk ψ b' y = twistedIndicator ψ (𝓛.matrixFiltration k) b' y :=
  rfl

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The bi-smooth coefficient `g ↦ ℓ(σ(g) w)` as an element of the span of bi-smooth
coefficients. -/
def stratumCoefficient (σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V)
    (ℓ : SmoothDual σ) (w : smoothVectors σ) : GodementJacquet.biSmoothMatrixCoefficients σ :=
  ⟨GodementJacquet.biSmoothCoefficient σ ℓ w, Submodule.subset_span ⟨ℓ, w, rfl⟩⟩

/-- **The zeta integral of the stratum test function**. Let `k ≥ 1` and let `w` be a
smooth vector with `σ(g) w = ψ(tr(b' (g - 1))) w` for `g ∈ U^k(𝔄(𝓛))`. For every `s`, the
Godement–Jacquet matrix integral of the stratum test function against `g ↦ ℓ(σ(g) w)` converges
and equals `vol(U^k(𝔄(𝓛))) ℓ(w)`. -/
theorem matrixIntegral_stratumTest
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin (n + 1) → K.Carrier)) {k : ℕ}
    (hk : 1 ≤ k) (ψ : UnitaryAdditiveCharacter K.Carrier)
    (b' : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier)
    (σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V) (ℓ : SmoothDual σ)
    (w : smoothVectors σ)
    (hw : ∀ g ∈ unitSubgroup K 𝓛 k,
      σ g w.val = ψ.complex ((b' * (g.val - 1)).trace) • w.val) (s : ℂ) :
    GodementJacquet.Padic.MatrixConverges K (stratumTest K 𝓛 hk ψ b') s
        (stratumCoefficient K σ ℓ w).val ∧
      GodementJacquet.Padic.matrixIntegral K (stratumTest K 𝓛 hk ψ b') s
          (stratumCoefficient K σ ℓ w).val =
        ((RankinSelberg.generalLinearHaar K.Carrier n).real
          (unitSubgroup K 𝓛 k : Set (GeneralLinear (n + 1) K.Carrier)) : ℂ) * ℓ.val w.val := by
  classical
  let T := K.canonicalTopologicalData
  let G := GeneralLinear (n + 1) K.Carrier
  let μ := RankinSelberg.generalLinearHaar K.Carrier n
  let U : Subgroup G := unitSubgroup K 𝓛 k
  have hUo : IsOpen (U : Set G) := isOpen_unitSubgroup K 𝓛 k
  have hUc : IsCompact (U : Set G) := isCompact_unitSubgroup K 𝓛 k
  have hUm : MeasurableSet (U : Set G) := hUo.measurableSet
  have hUfin : μ (U : Set G) ≠ ∞ := hUc.measure_lt_top.ne
  have hdet (g : G) (hg : g ∈ U) : RankinSelberg.normalizedAbsoluteValue T g.val.det = 1 := by
    have h := T.determinantNorm_eq_one_of_mem_compact (n + 1) U hUc g hg
    have h' : ((T.determinantNorm (n + 1) g : ℝ≥0) : ℝ) = 1 := by
      rw [h]
      rfl
    exact h'
  have hpt : GodementJacquet.matrixIntegrand (RankinSelberg.normalizedAbsoluteValue T)
      (stratumTest K 𝓛 hk ψ b') s (stratumCoefficient K σ ℓ w).val =
        (U : Set G).indicator (fun _ => ℓ.val w.val) := by
    funext g
    by_cases hg : g ∈ U
    · have hg1 : g.val - 1 ∈ 𝓛.matrixFiltration k :=
        (mem_unitSubgroup_iff_sub_one_mem K 𝓛 hk g).1 hg
      have hΦ : stratumTest K 𝓛 hk ψ b' g.val = ψ.complex (-(b' * (g.val - 1)).trace) :=
        twistedIndicator_apply_of_mem ψ _ b' hg1
      have hf : (stratumCoefficient K σ ℓ w).val g =
          ψ.complex ((b' * (g.val - 1)).trace) * ℓ.val w.val := by
        change ℓ.val (σ g w.val) = _
        rw [hw g hg, map_smul, smul_eq_mul]
      have hχ : ψ.complex (-(b' * (g.val - 1)).trace) * ψ.complex ((b' * (g.val - 1)).trace) =
          1 := by
        rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
      simp only [GodementJacquet.matrixIntegrand, hΦ, hf, RankinSelberg.determinantWeight,
        hdet g hg, Complex.ofReal_one, Complex.one_cpow, mul_one, Set.indicator_of_mem hg]
      rw [← mul_assoc, hχ, one_mul]
    · have hg1 : g.val - 1 ∉ 𝓛.matrixFiltration k :=
        fun h => hg ((mem_unitSubgroup_iff_sub_one_mem K 𝓛 hk g).2 h)
      have hΦ : stratumTest K 𝓛 hk ψ b' g.val = 0 :=
        twistedIndicator_apply_of_not_mem ψ _ b' hg1
      simp only [GodementJacquet.matrixIntegrand, hΦ, zero_mul, Set.indicator_of_notMem hg]
  refine ⟨?_, ?_⟩
  · change Integrable (GodementJacquet.matrixIntegrand (RankinSelberg.normalizedAbsoluteValue T)
      (stratumTest K 𝓛 hk ψ b') s (stratumCoefficient K σ ℓ w).val) μ
    rw [hpt]
    exact (integrable_indicator_iff hUm).mpr (integrableOn_const (C := ℓ.val w.val) hUfin)
  · change (∫ g, GodementJacquet.matrixIntegrand (RankinSelberg.normalizedAbsoluteValue T)
      (stratumTest K 𝓛 hk ψ b') s (stratumCoefficient K σ ℓ w).val g ∂μ) = _
    rw [hpt, integral_indicator_const _ hUm]
    rfl

/-- The volume of `U^k(𝔄(𝓛))` for the normalized Haar measure is a positive real number. -/
theorem generalLinearHaar_real_unitSubgroup_pos
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin (n + 1) → K.Carrier)) (k : ℕ) :
    0 < (RankinSelberg.generalLinearHaar K.Carrier n).real
      (unitSubgroup K 𝓛 k : Set (GeneralLinear (n + 1) K.Carrier)) := by
  let μ := RankinSelberg.generalLinearHaar K.Carrier n
  have hUo := isOpen_unitSubgroup K 𝓛 k
  have hUc := isCompact_unitSubgroup K 𝓛 k
  have hpos : μ (unitSubgroup K 𝓛 k : Set (GeneralLinear (n + 1) K.Carrier)) ≠ 0 :=
    (hUo.measure_pos μ ⟨1, (unitSubgroup K 𝓛 k).one_mem⟩).ne'
  exact ENNReal.toReal_pos hpos hUc.measure_lt_top.ne

/-- **The rational value of the stratum test function**. Under the hypotheses of
`matrixIntegral_stratumTest`, the shifted matrix integral has the constant rational value
`vol(U^k(𝔄(𝓛))) ℓ(w)`. -/
theorem hasShiftedRationalValue_stratumTest
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin (n + 1) → K.Carrier)) {k : ℕ}
    (hk : 1 ≤ k) (ψ : UnitaryAdditiveCharacter K.Carrier)
    (b' : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier)
    (σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V) (ℓ : SmoothDual σ)
    (w : smoothVectors σ)
    (hw : ∀ g ∈ unitSubgroup K 𝓛 k,
      σ g w.val = ψ.complex ((b' * (g.val - 1)).trace) • w.val) :
    GodementJacquet.HasShiftedRationalValue K.canonicalTopologicalData.residueCardinality
      (RankinSelberg.normalizedAbsoluteValue K.canonicalTopologicalData)
      (RankinSelberg.generalLinearHaar K.Carrier n) (stratumTest K 𝓛 hk ψ b')
      (stratumCoefficient K σ ℓ w).val
      (RatFunc.C (((RankinSelberg.generalLinearHaar K.Carrier n).real
        (unitSubgroup K 𝓛 k : Set (GeneralLinear (n + 1) K.Carrier)) : ℂ) * ℓ.val w.val)) := by
  have h := matrixIntegral_stratumTest K 𝓛 hk ψ b' σ ℓ w hw
  refine ⟨⟨0, fun s _ => (h (s + GodementJacquet.jpssShift n)).1⟩, 0, fun s _ => ⟨?_, ?_⟩⟩
  · rw [RatFunc.denom_C, Polynomial.eval_one]
    exact one_ne_zero
  · rw [RatFunc.eval_C]
    exact (h (s + GodementJacquet.jpssShift n)).2

end Padic

end Langlands.BushnellKutzko

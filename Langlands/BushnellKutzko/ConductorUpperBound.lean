import Langlands.BushnellKutzko.ShellIdentity
import Langlands.BushnellKutzko.CompactLevelBound
import Langlands.Representation.RankinSelberg.UnramifiedUnitaryPoleFreeProof

/-! # The upper bound for the functional-equation exponent

Let `K` be a `p`-adic field and `σ` a representation of `GL_N(K)`, `N = n + 1`, with
Godement–Jacquet functional-equation data with both Euler polynomials `1`, unit `c` and exponent
`a` (module `ShellIdentity`). Suppose `σ` contains a character of a stratum: a lattice chain `𝓛`
of period `e`, `k ≥ 1`, a matrix `b'` and a smooth vector `w` with
`σ(g) w = ψ(tr(b' (g - 1))) w` for `g ∈ U^k(𝔄(𝓛))`, and a smooth functional `ℓ` with
`ℓ(w) ≠ 0`. Feed the stratum test function of `StratumZetaIntegral` into the shell identity:
some `g` with `ord(det g) = -a` has a nonzero Fourier transform of the test function, and
`ℓ(σ(g^{-T}) w) ≠ 0` (`exists_ord_det_eq_of_stratum`). The Fourier support bound of
`FourierSupport` puts `t⁻¹ gᵀ` in a lattice filtration step `𝔓^j(𝓛)` (for a scalar `t` with
`ψ(t ·)` nontrivial on `𝔬_K` and `t⁻¹ b' ∈ 𝔓^j(𝓛)`, `j ≤ 1 - k`), and the determinant bound
`N j ≤ e ord(det X)` on `𝔓^j(𝓛)` gives

`e a ≤ -N j - e N ord(t)` (`period_mul_le_of_stratum`).

With `ψ` of conductor `𝔬_K`, `t = ϖ⁻¹` and `j = -m` this reads `e a ≤ N (e + m)`: the exponent of
the functional equation is at most `N (1 + m/e)`.

This is piece UB of the analytic part of the proof of T2 (Task 7683).
-/

noncomputable section

open MeasureTheory Topology Langlands.HarmonicAnalysis ValuativeRel

namespace Langlands.BushnellKutzko

universe uK uV

section Padic

local instance cbTopologicalSpace {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance cbValuativeRel {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance cbLocalField {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

local instance cbT2 {p : ℕ} [Fact p.Prime] (F : PadicField p) : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2

local instance cbMeasurable {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    MeasurableSpace F.Carrier :=
  borel _

local instance cbBorel {p : ℕ} [Fact p.Prime] (F : PadicField p) : BorelSpace F.Carrier :=
  ⟨rfl⟩

local instance cbGLMeasurable {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) :=
  borel _

local instance cbGLBorel {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) :=
  ⟨rfl⟩

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-! ### The canonical order and `ordOf` -/

/-- Units of `𝔬_K` have canonical order `0`. -/
theorem ord_coe_unit (w : 𝒪[K.Carrier]ˣ) :
    K.canonicalTopologicalData.ord ((w : 𝒪[K.Carrier]) : K.Carrier) = 0 := by
  set T := K.canonicalTopologicalData
  have h1 : 0 ≤ T.ord ((w : 𝒪[K.Carrier]) : K.Carrier) :=
    (RankinSelberg.UnramifiedUnitary.mem_integers_iff_ord K T (coe_unit_ne_zero w)).1
      (w : 𝒪[K.Carrier]).2
  have h2 : 0 ≤ T.ord (((w⁻¹ : 𝒪[K.Carrier]ˣ) : 𝒪[K.Carrier]) : K.Carrier) :=
    (RankinSelberg.UnramifiedUnitary.mem_integers_iff_ord K T (coe_unit_ne_zero _)).1
      ((w⁻¹ : 𝒪[K.Carrier]ˣ) : 𝒪[K.Carrier]).2
  rw [coe_unit_inv, T.ord_inv] at h2
  omega

/-- A uniformizer of `𝔬_K` has canonical order `1`. -/
theorem ord_coe_of_irreducible {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ) :
    K.canonicalTopologicalData.ord (ϖ : K.Carrier) = 1 := by
  set T := K.canonicalTopologicalData
  have hϖ0 := coe_uniformizer_ne_zero hϖ
  have h0 : 0 ≤ T.ord (ϖ : K.Carrier) :=
    (RankinSelberg.UnramifiedUnitary.mem_integers_iff_ord K T hϖ0).1 ϖ.2
  have hu : T.ord T.uniformizer = 1 := T.ord_uniformizer
  have hu0 : T.uniformizer ≠ 0 := by
    intro h
    rw [h, T.ord_zero] at hu
    exact zero_ne_one hu
  obtain ⟨w, hw⟩ := exists_eq_zpow_ordOf_mul hϖ hu0
  have h := congrArg T.ord hw
  rw [T.ord_mul (zpow_ne_zero _ hϖ0) (coe_unit_ne_zero w), T.ord_zpow, ord_coe_unit K w,
    add_zero, hu] at h
  exact Int.eq_one_of_mul_eq_one_left h0 h.symm

/-- `ordOf` for a uniformizer of `𝔬_K` is the canonical order. -/
theorem ordOf_eq_ord {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ) {x : K.Carrier} (hx : x ≠ 0) :
    ordOf hϖ x = K.canonicalTopologicalData.ord x := by
  set T := K.canonicalTopologicalData
  obtain ⟨w, hw⟩ := exists_eq_zpow_ordOf_mul hϖ hx
  have hϖ0 := coe_uniformizer_ne_zero hϖ
  conv_rhs => rw [hw]
  rw [T.ord_mul (zpow_ne_zero _ hϖ0) (coe_unit_ne_zero w), T.ord_zpow, ord_coe_unit K w,
    ord_coe_of_irreducible K hϖ, mul_one, add_zero]

/-- The determinant bound with the canonical order: if `toLin' X ∈ 𝔓^j(𝓛)` and `det X ≠ 0`, then
`N j ≤ e(𝓛) ord(det X)`. -/
theorem card_mul_le_period_mul_ord_det {N : ℕ}
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin N → K.Carrier)) {j : ℤ}
    {X : Matrix (Fin N) (Fin N) K.Carrier} (hX : Matrix.toLin' X ∈ 𝓛.endFiltration j)
    (hdet : X.det ≠ 0) :
    (N : ℤ) * j ≤ 𝓛.period * K.canonicalTopologicalData.ord X.det := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K.Carrier]
  have h := 𝓛.card_mul_le_period_mul_ordOf_det hϖ hX (by rwa [LinearMap.det_toLin'])
  rwa [LinearMap.det_toLin', Fintype.card_fin, ordOf_eq_ord K hϖ hdet] at h

/-- The canonical order of `det(t⁻¹ gᵀ)`. -/
theorem ord_det_inv_smul_transpose {N : ℕ} {t : K.Carrier} (ht : t ≠ 0)
    (g : GeneralLinear N K.Carrier) :
    K.canonicalTopologicalData.ord (t⁻¹ • g.val.transpose).det =
      K.canonicalTopologicalData.ord (Matrix.det g.val) -
        N * K.canonicalTopologicalData.ord t := by
  set T := K.canonicalTopologicalData
  have hg : Matrix.det g.val ≠ 0 := g.det_ne_zero
  rw [Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin,
    T.ord_mul (pow_ne_zero _ (inv_ne_zero ht)) hg, ← zpow_natCast, T.ord_zpow, T.ord_inv]
  ring

/-! ### Stratum characters and the shell -/

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The Fourier transform of the stratum test function is supported where `t⁻¹ xᵀ ∈ 𝔓^j(𝓛)`,
when `ψ(t ·)` is nontrivial on `𝔬_K`, `t⁻¹ b' ∈ 𝔓^j(𝓛)` and `j ≤ 1 - k`. -/
theorem toLin'_inv_smul_transpose_mem_of_fourier_ne_zero
    (ψ : UnitaryAdditiveCharacter K.Carrier) (ν : AdditiveHaarMeasure K.Carrier)
    [SigmaFinite ν.measure]
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin (n + 1) → K.Carrier)) {k : ℕ}
    (hk : 1 ≤ k) (b' : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier) {t : K.Carrier}
    (ht : t ≠ 0) (hψt : ∃ x : 𝒪[K.Carrier], ψ.complex (t * x) ≠ 1) {j : ℤ}
    (hj : j ≤ 1 - k) (hb : Matrix.toLin' (t⁻¹ • b') ∈ 𝓛.endFiltration j)
    (x : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier)
    (hx : rectangularFourierIntegral ψ ν (stratumTest K 𝓛 hk ψ b') x ≠ 0) :
    Matrix.toLin' (t⁻¹ • x.transpose) ∈ 𝓛.endFiltration j := by
  have h1 := 𝓛.toLin'_mem_endFiltration_of_rectangularFourierIntegral_ne_zero (k : ℤ) ψ ν ht hψt
    b' x hx
  have h2 : Matrix.toLin' (t⁻¹ • (x.transpose - b')) ∈ 𝓛.endFiltration j :=
    𝓛.endFiltration_antitone hj h1
  have h3 : t⁻¹ • x.transpose = t⁻¹ • (x.transpose - b') + t⁻¹ • b' := by
    rw [smul_sub, sub_add_cancel]
  rw [h3, map_add]
  exact add_mem h2 hb

/-- **The stratum on the shell.** Let `σ` have functional-equation data with both Euler
polynomials `1`, unit `c` and exponent `a`. Let `w` satisfy `σ(g) w = ψ(tr(b' (g - 1))) w` on
`U^k(𝔄(𝓛))`, `k ≥ 1`, and let `ℓ(w) ≠ 0`. Let `t ≠ 0` with `ψ(t ·)` nontrivial on `𝔬_K`, and
`t⁻¹ b' ∈ 𝔓^j(𝓛)` with `j ≤ 1 - k`. Then some `g ∈ GL_{n+1}(K)` has `ord(det g) = -a`,
`t⁻¹ gᵀ ∈ 𝔓^j(𝓛)`, `ℓ(σ(g^{-T}) w) ≠ 0` and `t⁻¹ (gᵀ - b') ∈ 𝔓^{1-k}(𝓛)`. -/
theorem exists_ord_det_eq_of_stratum
    (ψ : UnitaryAdditiveCharacter K.Carrier) (ν : AdditiveHaarMeasure K.Carrier)
    [SigmaFinite ν.measure]
    (σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V) (c : ℂˣ) (a : ℤ)
    (hFE : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData K ψ ν σ 1 1 c a)
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin (n + 1) → K.Carrier)) {k : ℕ}
    (hk : 1 ≤ k) (b' : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier) (ℓ : SmoothDual σ)
    (w : smoothVectors σ)
    (hw : ∀ g ∈ unitSubgroup K 𝓛 k,
      σ g w.val = ψ.complex ((b' * (g.val - 1)).trace) • w.val)
    (hℓ : ℓ.val w.val ≠ 0) {t : K.Carrier} (ht : t ≠ 0)
    (hψt : ∃ x : 𝒪[K.Carrier], ψ.complex (t * x) ≠ 1) {j : ℤ} (hj : j ≤ 1 - k)
    (hb : Matrix.toLin' (t⁻¹ • b') ∈ 𝓛.endFiltration j) :
    ∃ g : GeneralLinear (n + 1) K.Carrier,
      K.canonicalTopologicalData.ord (Matrix.det g.val) = -a ∧
        Matrix.toLin' (t⁻¹ • g.val.transpose) ∈ 𝓛.endFiltration j ∧
          ℓ.val (σ (GeneralLinear.inverseTranspose (n + 1) K.Carrier g) w.val) ≠ 0 ∧
            Matrix.toLin' (t⁻¹ • (g.val.transpose - b')) ∈ 𝓛.endFiltration (1 - k) := by
  set T := K.canonicalTopologicalData
  have he : (1 : ℤ) ≤ 𝓛.period := by exact_mod_cast 𝓛.period_pos
  -- the support bound for the shell identity
  have hsupp : ∀ g : GeneralLinear (n + 1) K.Carrier,
      rectangularFourierIntegral ψ ν (stratumTest K 𝓛 hk ψ b') g.val ≠ 0 →
        (n + 1 : ℤ) * T.ord t + min ((n + 1 : ℤ) * j) 0 ≤ T.ord (Matrix.det g.val) := by
    intro g hg
    have hmem := toLin'_inv_smul_transpose_mem_of_fourier_ne_zero K ψ ν 𝓛 hk b' ht hψt hj hb
      g.val hg
    have hdet : (t⁻¹ • g.val.transpose).det ≠ 0 := by
      rw [Matrix.det_smul, Matrix.det_transpose]
      exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) g.det_ne_zero
    have h := card_mul_le_period_mul_ord_det K 𝓛 hmem hdet
    rw [ord_det_inv_smul_transpose K ht g] at h
    push_cast at h
    by_contra hlt
    push Not at hlt
    set d := T.ord (Matrix.det g.val) - (n + 1 : ℤ) * T.ord t with hd
    have hd' : d < min ((n + 1 : ℤ) * j) 0 := by rw [hd]; linarith
    have hd0 : d < 0 := lt_of_lt_of_le hd' (min_le_right _ _)
    have hdj : d < (n + 1 : ℤ) * j := lt_of_lt_of_le hd' (min_le_left _ _)
    have hed : (𝓛.period : ℤ) * d ≤ d := by nlinarith
    have : ((n + 1 : ℕ) : ℤ) * j ≤ 𝓛.period * d := by rw [hd]; push_cast; linarith
    push_cast at this
    linarith
  -- the shell identity applied to the stratum coefficient
  have hvol := generalLinearHaar_real_unitSubgroup_pos K 𝓛 k
  have hr : ((RankinSelberg.generalLinearHaar K.Carrier n).real
      (unitSubgroup K 𝓛 k : Set (GeneralLinear (n + 1) K.Carrier)) : ℂ) * ℓ.val w.val ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hvol.ne') hℓ
  obtain ⟨g, hg, hΦ, hf⟩ := exists_ord_det_eq_of_functionalEquation K ψ ν σ c a hFE
    (stratumTest K 𝓛 hk ψ b') _ hsupp (stratumCoefficient K σ ℓ w) _
    (hasShiftedRationalValue_stratumTest K 𝓛 hk ψ b' σ ℓ w hw) hr
  exact ⟨g, hg, toLin'_inv_smul_transpose_mem_of_fourier_ne_zero K ψ ν 𝓛 hk b' ht hψt hj hb
    g.val hΦ, hf,
    𝓛.toLin'_mem_endFiltration_of_rectangularFourierIntegral_ne_zero (k : ℤ) ψ ν ht hψt b' g.val hΦ⟩

/-- **The upper bound for the exponent** (piece UB). Under the hypotheses of
`exists_ord_det_eq_of_stratum`, `e a ≤ -N j - e N ord(t)`, where `N = n + 1` and `e` is the
period of `𝓛`. -/
theorem period_mul_le_of_stratum
    (ψ : UnitaryAdditiveCharacter K.Carrier) (ν : AdditiveHaarMeasure K.Carrier)
    [SigmaFinite ν.measure]
    (σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V) (c : ℂˣ) (a : ℤ)
    (hFE : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData K ψ ν σ 1 1 c a)
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin (n + 1) → K.Carrier)) {k : ℕ}
    (hk : 1 ≤ k) (b' : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier) (ℓ : SmoothDual σ)
    (w : smoothVectors σ)
    (hw : ∀ g ∈ unitSubgroup K 𝓛 k,
      σ g w.val = ψ.complex ((b' * (g.val - 1)).trace) • w.val)
    (hℓ : ℓ.val w.val ≠ 0) {t : K.Carrier} (ht : t ≠ 0)
    (hψt : ∃ x : 𝒪[K.Carrier], ψ.complex (t * x) ≠ 1) {j : ℤ} (hj : j ≤ 1 - k)
    (hb : Matrix.toLin' (t⁻¹ • b') ∈ 𝓛.endFiltration j) :
    (𝓛.period : ℤ) * a ≤
      -((n + 1 : ℤ) * j) - 𝓛.period * (n + 1 : ℤ) * K.canonicalTopologicalData.ord t := by
  obtain ⟨g, hg, hmem, -, -⟩ := exists_ord_det_eq_of_stratum K ψ ν σ c a hFE 𝓛 hk b' ℓ w hw hℓ ht
    hψt hj hb
  have hdet : (t⁻¹ • g.val.transpose).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) g.det_ne_zero
  have h := card_mul_le_period_mul_ord_det K 𝓛 hmem hdet
  rw [ord_det_inv_smul_transpose K ht g, hg] at h
  push_cast at h
  linarith

end Padic

end Langlands.BushnellKutzko

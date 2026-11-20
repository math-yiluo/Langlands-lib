import Langlands.BushnellKutzko.ConductorUpperBound
import Langlands.Representation.GodementJacquet.CentralCompactSupport

/-! # The lower bound for the functional-equation exponent

Let `K` be a `p`-adic field and `σ` a representation of `GL_N(K)`, `N = n + 1`, with
Godement–Jacquet functional-equation data with both Euler polynomials `1`, unit `c` and exponent
`a`, containing a stratum character: a lattice chain `𝓛` of period `e`, `k ≥ 1`, a matrix `b'`
and a smooth vector `w` with `σ(g) w = ψ(tr(b' (g - 1))) w` on `U^k(𝔄(𝓛))`, and a smooth
functional `ℓ` with `ℓ(w) ≠ 0`. Let `t ≠ 0` with `ψ(t ·)` nontrivial on `𝔬_K`, and put
`β = t⁻¹ b'`.

Iterating `exists_ord_det_eq_of_stratum` with the translated functionals `v ↦ ℓ(σ(h) v)` gives,
for every `m`, elements `g₁, …, g_m` with `ord(det gᵢ) = -a`, `t⁻¹ gᵢᵀ ∈ β + 𝔓^{1-k}(𝓛)` and
`ℓ(σ(g₁^{-T} ⋯ g_m^{-T}) w) ≠ 0` (`exists_list_of_stratum`). If the coefficient
`h ↦ ℓ(σ(h) w)` is supported in the scalar saturation of a compact set `C` (as for supercuspidal
representations), `g₁^{-T} ⋯ g_m^{-T} = z c` with `z` scalar and `c ∈ C`, so the product
`(t⁻¹ g_mᵀ) ⋯ (t⁻¹ g₁ᵀ) = t^{-m} z⁻¹ c⁻¹` lies in the scalar saturation of the compact set
`C⁻¹`. If `β ∈ 𝔓^{-k}(𝓛)` and no power `β^i` lies in `𝔓^{1-ik}(𝓛)` (the stratum
`[𝔄(𝓛), k, k - 1, β]` attains the normalized level), this product is not in `𝔓^{1-mk}(𝓛)`,
while its determinant has order `m (-a - N ord(t))`. The growth bound
`LatticeChain.period_mul_le_of_forall_exists` then gives

`N k - e N ord(t) ≤ e a` (`le_period_mul_of_stratum`),

and together with the upper bound of `ConductorUpperBound`, `e a = N k - e N ord(t)`
(`period_mul_eq_of_stratum`). With `ψ` of conductor `𝔬_K` and `t = ϖ⁻¹`, this is
`a = N (1 + k/e)`.

This is piece LB of the analytic part of the proof of T2 (Task 7683).
-/

noncomputable section

open MeasureTheory Topology Langlands.HarmonicAnalysis ValuativeRel

namespace Langlands.BushnellKutzko

universe uK uV

/-! ### Products of transposes -/

section Products

variable {F : Type*} [Field F] {N : ℕ}

/-- `toLin'` of a product of matrices is the product of the `toLin'`. -/
theorem toLin'_list_prod (L : List (Matrix (Fin N) (Fin N) F)) :
    Matrix.toLin' L.prod = (L.map Matrix.toLin').prod := by
  induction L with
  | nil =>
    rw [List.prod_nil, List.map_nil, List.prod_nil, Matrix.toLin'_one]
    rfl
  | cons x L ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, Matrix.toLin'_mul, ih,
      Module.End.mul_eq_comp]

/-- The inverse of `g` under the inverse transpose is the transpose of `g`. -/
theorem val_inv_inverseTranspose (g : GeneralLinear N F) :
    ((GeneralLinear.inverseTranspose N F g)⁻¹ : GeneralLinear N F).val = g.val.transpose :=
  rfl

/-- For `g₁, …, g_m ∈ GL_N(F)`, `t^{-m} (g₁^{-T} ⋯ g_m^{-T})^{-1} = (t⁻¹ g_mᵀ) ⋯ (t⁻¹ g₁ᵀ)`. -/
theorem pow_smul_inv_prod_inverseTranspose (t : F) (l : List (GeneralLinear N F)) :
    t⁻¹ ^ l.length •
        (((l.map (GeneralLinear.inverseTranspose N F)).prod)⁻¹ : GeneralLinear N F).val =
      (l.reverse.map fun g => t⁻¹ • g.val.transpose).prod := by
  induction l with
  | nil => simp
  | cons g l ih =>
    rw [List.map_cons, List.prod_cons, mul_inv_rev, Units.val_mul, val_inv_inverseTranspose,
      List.reverse_cons, List.map_append, List.prod_append, ← ih, List.map_singleton,
      List.prod_singleton, smul_mul_smul_comm, List.length_cons, pow_succ]

/-- The scalar matrix of `z` times `c` is `z • c`. -/
theorem val_scalar_mul (z : Fˣ) (c : GeneralLinear N F) :
    (GeneralLinear.scalar z * c).val = (z : F) • c.val := by
  change Matrix.scalar (Fin N) (z : F) * c.val = _
  ext i j
  simp [Matrix.scalar, Matrix.diagonal_mul]

end Products

section Padic

local instance clbTopologicalSpace {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance clbValuativeRel {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance clbLocalField {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

local instance clbT2 {p : ℕ} [Fact p.Prime] (F : PadicField p) : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2

local instance clbMeasurable {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    MeasurableSpace F.Carrier :=
  borel _

local instance clbBorel {p : ℕ} [Fact p.Prime] (F : PadicField p) : BorelSpace F.Carrier :=
  ⟨rfl⟩

local instance clbGLMeasurable {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) :=
  borel _

local instance clbGLBorel {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) :=
  ⟨rfl⟩

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- The canonical order of the determinant of a product of matrices, all of whose determinants
are nonzero of order `μ`. -/
theorem ord_det_list_prod {N : ℕ} (L : List (Matrix (Fin N) (Fin N) K.Carrier)) {μ : ℤ}
    (hL : ∀ x ∈ L, x.det ≠ 0 ∧ K.canonicalTopologicalData.ord x.det = μ) :
    L.prod.det ≠ 0 ∧ K.canonicalTopologicalData.ord L.prod.det = L.length * μ := by
  induction L with
  | nil => simp [PadicField.TopologicalData.ord_one]
  | cons x L ih =>
    obtain ⟨hx0, hx⟩ := hL x List.mem_cons_self
    obtain ⟨h0, h⟩ := ih fun y hy => hL y (List.mem_cons_of_mem x hy)
    rw [List.prod_cons, Matrix.det_mul]
    refine ⟨mul_ne_zero hx0 h0, ?_⟩
    rw [K.canonicalTopologicalData.ord_mul hx0 h0, hx, h, List.length_cons]
    push_cast
    ring

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The translate of a smooth functional: `(h⁻¹ · ℓ)(v) = ℓ(σ(h) v)`. -/
theorem smoothContragredient_inv_apply
    (σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V) (ℓ : SmoothDual σ)
    (h : GeneralLinear (n + 1) K.Carrier) (v : V) :
    (smoothContragredient σ h⁻¹ ℓ).val v = ℓ.val (σ h v) := by
  change (Module.Dual.transpose (R := ℂ) (σ (h⁻¹)⁻¹) ℓ.val) v = _
  rw [inv_inv]
  rfl

/-- **Iterating the shell.** Under the hypotheses of `exists_ord_det_eq_of_stratum` (with
`t⁻¹ b' ∈ 𝔓^{-k}(𝓛)`), for every `m` there are `g₁, …, g_m ∈ GL_{n+1}(K)` with
`ord(det gᵢ) = -a` and `t⁻¹ (gᵢᵀ - b') ∈ 𝔓^{1-k}(𝓛)`, such that
`ℓ(σ(g₁^{-T} ⋯ g_m^{-T}) w) ≠ 0`. -/
theorem exists_list_of_stratum
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
    (hψt : ∃ x : 𝒪[K.Carrier], ψ.complex (t * x) ≠ 1)
    (hb : Matrix.toLin' (t⁻¹ • b') ∈ 𝓛.endFiltration (-(k : ℤ))) (m : ℕ) :
    ∃ l : List (GeneralLinear (n + 1) K.Carrier), l.length = m ∧
      (∀ g ∈ l, K.canonicalTopologicalData.ord (Matrix.det g.val) = -a ∧
        Matrix.toLin' (t⁻¹ • (g.val.transpose - b')) ∈ 𝓛.endFiltration (1 - k)) ∧
      ℓ.val (σ (l.map (GeneralLinear.inverseTranspose (n + 1) K.Carrier)).prod w.val) ≠ 0 := by
  induction m with
  | zero => exact ⟨[], rfl, by simp, by simpa using hℓ⟩
  | succ m ih =>
    obtain ⟨l, hlen, hl, hne⟩ := ih
    set P := (l.map (GeneralLinear.inverseTranspose (n + 1) K.Carrier)).prod with hP
    have hℓ' : (smoothContragredient σ P⁻¹ ℓ).val w.val ≠ 0 := by
      rw [smoothContragredient_inv_apply]
      exact hne
    obtain ⟨g, hg, -, hf, hfine⟩ := exists_ord_det_eq_of_stratum K ψ ν σ c a hFE 𝓛 hk b'
      (smoothContragredient σ P⁻¹ ℓ) w hw hℓ' ht hψt (by omega) hb
    refine ⟨l ++ [g], by simp [hlen], ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hl x hx
      · rw [List.mem_singleton] at hx
        subst hx
        exact ⟨hg, hfine⟩
    · rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, ← hP,
        map_mul, Module.End.mul_apply]
      rwa [smoothContragredient_inv_apply] at hf

/-- **The lower bound for the exponent** (piece LB). Under the hypotheses of
`exists_list_of_stratum`, assume moreover that no power `β^i` of `β = t⁻¹ b'` lies in
`𝔓^{1-ik}(𝓛)`, and that `h ↦ ℓ(σ(h) w)` vanishes outside the scalar saturation of a compact
set `C ⊆ GL_{n+1}(K)`. Then `N k - e N ord(t) ≤ e a`, where `N = n + 1` and `e` is the period
of `𝓛`. -/
theorem le_period_mul_of_stratum
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
    (hψt : ∃ x : 𝒪[K.Carrier], ψ.complex (t * x) ≠ 1)
    (hb : Matrix.toLin' (t⁻¹ • b') ∈ 𝓛.endFiltration (-(k : ℤ)))
    (hpow : ∀ i : ℕ, Matrix.toLin' (t⁻¹ • b') ^ i ∉ 𝓛.endFiltration (i * (-(k : ℤ)) + 1))
    {C : Set (GeneralLinear (n + 1) K.Carrier)} (hC : IsCompact C)
    (hsupp : ∀ h : GeneralLinear (n + 1) K.Carrier, ℓ.val (σ h w.val) ≠ 0 →
      h ∈ GodementJacquet.scalarSaturation C) :
    (n + 1 : ℤ) * k - 𝓛.period * (n + 1 : ℤ) * K.canonicalTopologicalData.ord t ≤
      𝓛.period * a := by
  set T := K.canonicalTopologicalData
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K.Carrier]
  have key := 𝓛.period_mul_le_of_forall_exists hϖ (C := C⁻¹) hC.inv
    (j := -(k : ℤ)) (μ := -a - (n + 1 : ℤ) * T.ord t) ?_
  · rw [Fintype.card_fin] at key
    push_cast at key
    linarith
  intro m
  obtain ⟨l, hlen, hl, hne⟩ := exists_list_of_stratum K ψ ν σ c a hFE 𝓛 hk b' ℓ w hw hℓ ht hψt
    hb m
  obtain ⟨z, c₀, hc₀, hh⟩ := hsupp _ hne
  set P := (l.map (GeneralLinear.inverseTranspose (n + 1) K.Carrier)).prod with hP
  -- the reversed product of the `t⁻¹ gᵢᵀ`
  set L := l.reverse.map fun g : GeneralLinear (n + 1) K.Carrier => t⁻¹ • g.val.transpose
    with hL
  have hLlen : L.length = m := by simp [hL, hlen]
  have hPinv : (P⁻¹ : GeneralLinear (n + 1) K.Carrier).val = ((z⁻¹ : K.Carrierˣ) : K.Carrier) •
      (c₀⁻¹ : GeneralLinear (n + 1) K.Carrier).val := by
    rw [hh, mul_inv_rev, ← map_inv, ← Matrix.GeneralLinearGroup.scalar_commute,
      val_scalar_mul]
  have hM : (t⁻¹ ^ m * ((z⁻¹ : K.Carrierˣ) : K.Carrier)) •
      (c₀⁻¹ : GeneralLinear (n + 1) K.Carrier).val = L.prod := by
    rw [mul_smul, ← hPinv, ← hlen, hL]
    exact pow_smul_inv_prod_inverseTranspose t l
  refine ⟨c₀⁻¹, Set.inv_mem_inv.2 hc₀, t⁻¹ ^ m * ((z⁻¹ : K.Carrierˣ) : K.Carrier),
    mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) (Units.ne_zero _), ?_, ?_⟩
  · -- the product avoids `𝔓^{1-mk}`
    rw [hM, toLin'_list_prod]
    have h := 𝓛.list_prod_not_mem hb hpow (L.map Matrix.toLin') ?_
    · rwa [List.length_map, hLlen] at h
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
    rw [List.mem_reverse] at hg
    have h1 := (hl g hg).2
    rw [smul_sub, map_sub] at h1
    convert h1 using 2
    ring
  · -- the order of the determinant
    have hdet := ord_det_list_prod K L (μ := -a - (n + 1 : ℤ) * T.ord t) ?_
    · rw [hM, ordOf_eq_ord K hϖ hdet.1, hdet.2, hLlen]
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_reverse] at hg
    refine ⟨?_, ?_⟩
    · rw [Matrix.det_smul, Matrix.det_transpose]
      exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) g.det_ne_zero
    · rw [ord_det_inv_smul_transpose K ht g, (hl g hg).1]
      push_cast
      ring

/-- **The exponent of the functional equation** (pieces UB and LB). Under the hypotheses of
`le_period_mul_of_stratum`, `e a = N k - e N ord(t)`, where `N = n + 1` and `e` is the period
of `𝓛`. -/
theorem period_mul_eq_of_stratum
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
    (hψt : ∃ x : 𝒪[K.Carrier], ψ.complex (t * x) ≠ 1)
    (hb : Matrix.toLin' (t⁻¹ • b') ∈ 𝓛.endFiltration (-(k : ℤ)))
    (hpow : ∀ i : ℕ, Matrix.toLin' (t⁻¹ • b') ^ i ∉ 𝓛.endFiltration (i * (-(k : ℤ)) + 1))
    {C : Set (GeneralLinear (n + 1) K.Carrier)} (hC : IsCompact C)
    (hsupp : ∀ h : GeneralLinear (n + 1) K.Carrier, ℓ.val (σ h w.val) ≠ 0 →
      h ∈ GodementJacquet.scalarSaturation C) :
    (𝓛.period : ℤ) * a =
      (n + 1 : ℤ) * k - 𝓛.period * (n + 1 : ℤ) * K.canonicalTopologicalData.ord t := by
  have hle := le_period_mul_of_stratum K ψ ν σ c a hFE 𝓛 hk b' ℓ w hw hℓ ht hψt hb hpow hC hsupp
  have hge := period_mul_le_of_stratum K ψ ν σ c a hFE 𝓛 hk b' ℓ w hw hℓ ht hψt
    (j := -(k : ℤ)) (by omega) hb
  linarith

end Padic

end Langlands.BushnellKutzko

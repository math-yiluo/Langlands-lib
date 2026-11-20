import Langlands.BushnellKutzko.ConductorLowerBound
import Langlands.BushnellKutzko.StratumExistence
import Langlands.Representation.GodementJacquet.SupercuspidalMatrixSupport
import Langlands.Representation.Conductor.Essential
import Langlands.Representation.Unitary.SquareIntegrableProof
import Langlands.Representation.Category.Contragredient
import Langlands.HarmonicAnalysis.SelfDualSigmaFiniteProof

/-! # The functional-equation exponent of a supercuspidal representation and its level

Let `K` be a `p`-adic field, `ψ` an additive character of `K` of conductor `𝔬_K`
(`Conductor.HasIntegerConductor ψ`), `ν` a self-dual Haar measure, and `A` an irreducible
supercuspidal representation of `GL_N(K)`, `N = n + 1`, whose Godement–Jacquet functional
equation has both Euler polynomials `1`, unit `c` and exponent `a`. If the class of `A` has
normalized level `x`, then

`max(a, N) = N (1 + x)` (`max_exponent_eq_of_isNormalizedLevel`),

that is, `a ≤ N` if `x = 0` and `a = N (1 + x)` if `x > 0`. This is piece E (rank-free part) of
the proof of T2: the analytic bounds of `ConductorUpperBound` and
`ConductorLowerBound` applied to the strata of `StratumExistence` and `LevelAttainingStratum`.
The Library provides the functional-equation data for rank at least two
(`GodementJacquet.Padic.exists_supercuspidalMatrixFunctionalEquationData`).
-/

noncomputable section

open MeasureTheory Topology Langlands.HarmonicAnalysis ValuativeRel

namespace Langlands.BushnellKutzko

universe uK uV

section Padic

local instance cfTopologicalSpace {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance cfValuativeRel {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance cfLocalField {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

local instance cfT2 {p : ℕ} [Fact p.Prime] (F : PadicField p) : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2

local instance cfDisconnected {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local instance cfMeasurable {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    MeasurableSpace F.Carrier :=
  borel _

local instance cfBorel {p : ℕ} [Fact p.Prime] (F : PadicField p) : BorelSpace F.Carrier :=
  ⟨rfl⟩

local instance cfGLMeasurable {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) :=
  borel _

local instance cfGLBorel {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) :=
  ⟨rfl⟩

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-! ### The level-one character -/

/-- The additive character `x ↦ ψ(t x)`. -/
def scaledCharacter (ψ : UnitaryAdditiveCharacter K.Carrier) (t : K.Carrier) :
    AddChar K.Carrier ℂ :=
  ψ.complex.compAddMonoidHom (AddMonoidHom.mulLeft t)

theorem scaledCharacter_apply (ψ : UnitaryAdditiveCharacter K.Carrier) (t x : K.Carrier) :
    scaledCharacter K ψ t x = ψ.complex (t * x) :=
  rfl

/-- If `ψ` has conductor `𝔬_K` and `ϖ` is a uniformizer, `x ↦ ψ(ϖ⁻¹ x)` is trivial on `𝔭_K`. -/
theorem scaledCharacter_eq_one_of_mem_maximalIdeal {ψ : UnitaryAdditiveCharacter K.Carrier}
    (hψ : Conductor.HasIntegerConductor ψ) {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ) :
    ∀ c ∈ 𝓂[K.Carrier], scaledCharacter K ψ (ϖ : K.Carrier)⁻¹ (c : K.Carrier) = 1 := by
  intro c hc
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hc
  obtain ⟨y, rfl⟩ := hc
  have hϖ0 : (ϖ : K.Carrier) ≠ 0 := coe_uniformizer_ne_zero hϖ
  have hy : (ϖ : K.Carrier)⁻¹ * ((y * ϖ : 𝒪[K.Carrier]) : K.Carrier) = (y : K.Carrier) := by
    push_cast
    field_simp
  rw [scaledCharacter_apply, hy, UnitaryAdditiveCharacter.complex_apply, hψ.1 _ y.2]
  rfl

/-- If `ψ` has conductor `𝔬_K` and `ϖ` is a uniformizer, `x ↦ ψ(ϖ⁻¹ x)` is nontrivial on
`𝔬_K`. -/
theorem exists_scaledCharacter_ne_one {ψ : UnitaryAdditiveCharacter K.Carrier}
    (hψ : Conductor.HasIntegerConductor ψ) {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ) :
    ∃ c : 𝒪[K.Carrier], scaledCharacter K ψ (ϖ : K.Carrier)⁻¹ (c : K.Carrier) ≠ 1 := by
  set T := K.canonicalTopologicalData
  by_contra h
  push Not at h
  have hϖ0 : (ϖ : K.Carrier) ≠ 0 := coe_uniformizer_ne_zero hϖ
  have hmem : (ϖ : K.Carrier)⁻¹ ∈ (ValuativeRel.valuation K.Carrier).integer := by
    refine hψ.2 _ fun y hy => ?_
    have h1 := h ⟨y, hy⟩
    rw [scaledCharacter_apply, UnitaryAdditiveCharacter.complex_apply] at h1
    exact Circle.coe_eq_one.1 h1
  have h0 := (RankinSelberg.UnramifiedUnitary.mem_integers_iff_ord K T (inv_ne_zero hϖ0)).1 hmem
  rw [T.ord_inv, ord_coe_of_irreducible K hϖ] at h0
  omega

/-! ### The trace character in matrix form -/

/-- `ψ(ϖ⁻¹ tr(b (g - 1))) = ψ(tr((ϖ⁻¹ B) (g - 1)))` with `B` the matrix of `b`. -/
theorem elementCharacter_scaledCharacter (ψ : UnitaryAdditiveCharacter K.Carrier) {N : ℕ}
    (t : K.Carrier) (b : Module.End K.Carrier (Fin N → K.Carrier))
    (g : GeneralLinear N K.Carrier) :
    elementCharacter (traceCharacter (scaledCharacter K ψ t)) b
        (Matrix.GeneralLinearGroup.toLin g) =
      ψ.complex (((t • LinearMap.toMatrix' b) * (g.val - 1)).trace) := by
  rw [elementCharacter_apply, traceCharacter_apply, scaledCharacter_apply]
  congr 1
  have h : ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup K.Carrier
      (Fin N → K.Carrier)) : Module.End K.Carrier (Fin N → K.Carrier)) =
      Matrix.toLin' g.val := by
    rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.toLin'_apply']
  rw [h, show b * (Matrix.toLin' g.val - 1) = Matrix.toLin' (LinearMap.toMatrix' b * (g.val - 1))
    by rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', map_sub, Matrix.toLin'_one]; rfl,
    Matrix.trace_toLin'_eq, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-! ### Level zero: the upper bound -/

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- **Level zero.** Let `ψ` have conductor `𝔬_K` and let `σ` be a smooth representation of
`GL_{n+1}(K)` with functional-equation data with both Euler polynomials `1` and exponent `a`.
If `σ` has a nonzero vector fixed by `U^1(𝔄(𝓛))` for some lattice chain `𝓛`, then
`a ≤ n + 1`. -/
theorem exponent_le_of_fixedVector
    (ψ : UnitaryAdditiveCharacter K.Carrier) (hψ : Conductor.HasIntegerConductor ψ)
    (ν : AdditiveHaarMeasure K.Carrier) [SigmaFinite ν.measure]
    (σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V) (hσ : IsSmooth σ) (c : ℂˣ)
    (a : ℤ) (hFE : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData K ψ ν σ 1 1 c a)
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin (n + 1) → K.Carrier)) {v : V} (hv : v ≠ 0)
    (hfix : ∀ g ∈ unitSubgroup K 𝓛 1, σ g v = v) :
    a ≤ n + 1 := by
  set T := K.canonicalTopologicalData
  have := T.generalLinearTopologicalGroup (n + 1)
  obtain ⟨ℓ, hℓ⟩ := exists_smoothDual_apply_ne_zero_of_compact_cofinal
    (GeneralLinear.compactOpen_cofinal K T (n + 1)) σ hσ hv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K.Carrier]
  have hϖ0 : (ϖ : K.Carrier) ≠ 0 := coe_uniformizer_ne_zero hϖ
  let w : smoothVectors σ := ⟨v, hσ v⟩
  have hw : ∀ g ∈ unitSubgroup K 𝓛 1,
      σ g w.val = ψ.complex (((0 : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier) *
        (g.val - 1)).trace) • w.val := by
    intro g hg
    rw [zero_mul, Matrix.trace_zero, AddChar.map_zero_eq_one, one_smul]
    exact hfix g hg
  have h := period_mul_le_of_stratum K ψ ν σ c a hFE 𝓛 le_rfl 0 ℓ w hw hℓ
    (t := (ϖ : K.Carrier)⁻¹) (inv_ne_zero hϖ0) (exists_scaledCharacter_ne_one K hψ hϖ)
    (j := 0) (by norm_num) (by rw [smul_zero, map_zero]; exact zero_mem _)
  rw [T.ord_inv, ord_coe_of_irreducible K hϖ] at h
  have he : (0 : ℤ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
  nlinarith

/-! ### Positive level: the exponent -/

/-- **Positive level.** Let `ψ` have conductor `𝔬_K`, `ϖ` a uniformizer, and `σ` an irreducible
supercuspidal representation of `GL_{n+1}(K)` with functional-equation data with both Euler
polynomials `1` and exponent `a`. Suppose `σ` contains the stratum `[𝔄(𝓛), m, m - 1, b]` with
respect to `ψ(ϖ⁻¹ ·)` (a nonzero `v` with `σ(g) v = ψ(ϖ⁻¹ tr(b (g - 1))) v` on `U^m(𝔄(𝓛))`,
`m ≥ 1`, `b ∈ 𝔓^{-m}(𝓛)`), and that no power `b^i` lies in `𝔓^{1-im}(𝓛)`. Then
`e a = N m + e N`, where `N = n + 1` and `e` is the period of `𝓛`. -/
theorem period_mul_exponent_eq_of_stratum
    (ψ : UnitaryAdditiveCharacter K.Carrier) (hψ : Conductor.HasIntegerConductor ψ)
    (ν : AdditiveHaarMeasure K.Carrier) [SigmaFinite ν.measure]
    (σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V)
    (hσ : GeneralLinear.IsSupercuspidal σ) (hσi : σ.IsIrreducible) (c : ℂˣ) (a : ℤ)
    (hFE : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData K ψ ν σ 1 1 c a)
    {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ)
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin (n + 1) → K.Carrier)) {m : ℕ} (hm : 1 ≤ m)
    (b : Module.End K.Carrier (Fin (n + 1) → K.Carrier)) (hb : b ∈ 𝓛.endFiltration (-(m : ℤ)))
    (hpow : ∀ i : ℕ, b ^ i ∉ 𝓛.endFiltration (i * (-(m : ℤ)) + 1)) {v : V} (hv : v ≠ 0)
    (hχ : ∀ g ∈ unitSubgroup K 𝓛 m, σ g v =
      elementCharacter (traceCharacter (scaledCharacter K ψ (ϖ : K.Carrier)⁻¹)) b
        (Matrix.GeneralLinearGroup.toLin g) • v) :
    (𝓛.period : ℤ) * a = (n + 1 : ℤ) * m + 𝓛.period * (n + 1 : ℤ) := by
  set T := K.canonicalTopologicalData
  have := T.generalLinearTopologicalGroup (n + 1)
  have hσs : IsSmooth σ := hσ.1.1
  obtain ⟨ℓ, hℓ⟩ := exists_smoothDual_apply_ne_zero_of_compact_cofinal
    (GeneralLinear.compactOpen_cofinal K T (n + 1)) σ hσs hv
  have hϖ0 : (ϖ : K.Carrier) ≠ 0 := coe_uniformizer_ne_zero hϖ
  let w : smoothVectors σ := ⟨v, hσs v⟩
  set b' := (ϖ : K.Carrier)⁻¹ • LinearMap.toMatrix' b with hb'
  have hbb : ((ϖ : K.Carrier)⁻¹)⁻¹ • b' = LinearMap.toMatrix' b := by
    rw [hb', smul_smul, inv_inv, mul_inv_cancel₀ hϖ0, one_smul]
  have hw : ∀ g ∈ unitSubgroup K 𝓛 m,
      σ g w.val = ψ.complex ((b' * (g.val - 1)).trace) • w.val := by
    intro g hg
    rw [hχ g hg, elementCharacter_scaledCharacter]
  -- compact support modulo the centre
  obtain ⟨χ, -, hf⟩ :=
    GodementJacquet.exists_centralCharacter_compactScalarSupport T σ hσ hσi
  obtain ⟨-, -, C, hC, hsupp⟩ := hf (stratumCoefficient K σ ℓ w)
  have hsupp' : ∀ h : GeneralLinear (n + 1) K.Carrier, ℓ.val (σ h w.val) ≠ 0 →
      h ∈ GodementJacquet.scalarSaturation C := fun h hh => hsupp hh
  have h := period_mul_eq_of_stratum K ψ ν σ c a hFE 𝓛 hm b' ℓ w hw hℓ
    (t := (ϖ : K.Carrier)⁻¹) (inv_ne_zero hϖ0) (exists_scaledCharacter_ne_one K hψ hϖ)
    (by rw [hbb, Matrix.toLin'_toMatrix']; exact hb)
    (by rw [hbb, Matrix.toLin'_toMatrix']; exact hpow) hC hsupp'
  rw [h, T.ord_inv, ord_coe_of_irreducible K hϖ]
  ring

/-! ### The exponent and the normalized level -/

/-- **The exponent and the normalized level** (piece E, without the rank restriction). Let `ψ`
have conductor `𝔬_K`, `ν` be self-dual for `ψ`, and `A` an irreducible supercuspidal
representation of `GL_{n+1}(K)` whose Godement–Jacquet functional equation has both Euler
polynomials `1`, unit `c` and exponent `a`. If the class of `A` has normalized level `x`, then
`max(a, n + 1) = (n + 1)(1 + x)`. -/
theorem max_exponent_eq_of_isNormalizedLevel
    (ψ : UnitaryAdditiveCharacter K.Carrier) (hψ : Conductor.HasIntegerConductor ψ)
    (ν : AdditiveHaarMeasure K.Carrier) (hsd : IsSelfDual ψ ν)
    (A : GeneralLinear.SupercuspidalRep.{uK, uV} (F := K.Carrier) (n := n + 1)) (c : ℂˣ)
    (a : ℤ)
    (hFE : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData K ψ ν
      A.obj.representation 1 1 c a)
    {x : ℚ}
    (hlev : IsNormalizedLevel K (n + 1) (SmoothDualClass.ofRep A.toIrreducibleAdmissible) x) :
    max (a : ℚ) (n + 1) = (n + 1) * (1 + x) := by
  have : SigmaFinite ν.measure := selfDualSigmaFinite K.Carrier ψ ν hsd
  have hσ : GeneralLinear.IsSupercuspidal A.obj.representation := A.property.2
  have hσi : A.obj.representation.IsIrreducible := A.property.1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K.Carrier]
  -- `x ≥ 0`
  obtain ⟨𝓛₀, m₀, hx₀, hfix₀⟩ := hlev.1
  have he₀ : (0 : ℚ) < 𝓛₀.period := by exact_mod_cast 𝓛₀.period_pos
  have hx0 : 0 ≤ x := by rw [hx₀]; positivity
  rcases hx0.eq_or_lt with hx | hx
  · -- level zero
    subst hx
    have hm₀ : m₀ = 0 := by
      have : (m₀ : ℚ) = 0 := by
        rw [eq_comm, div_eq_zero_iff] at hx₀
        rcases hx₀ with h | h
        · exact h
        · exact absurd h he₀.ne'
      exact_mod_cast this
    subst hm₀
    have hne : fixedVectors A.obj.representation (unitSubgroup K 𝓛₀ (0 + 1)) ≠ ⊥ := hfix₀
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hle := exponent_le_of_fixedVector K ψ hψ ν A.obj.representation hσ.1.1 c a hFE 𝓛₀
      hv0 fun g hg => (mem_fixedVectors_iff_forall_mem _ _ v).1 hv g hg
    have : (a : ℚ) ≤ n + 1 := by exact_mod_cast hle
    rw [max_eq_right this]
    ring
  · -- positive level
    obtain ⟨𝓛, m, b, hxm, hcont, -⟩ := exists_containsStratum_of_isNormalizedLevel K (n + 1)
      (scaledCharacter K ψ (ϖ : K.Carrier)⁻¹) (scaledCharacter_eq_one_of_mem_maximalIdeal K hψ hϖ)
      (exists_scaledCharacter_ne_one K hψ hϖ) _ hlev hx
    have hpow := pow_add_not_mem_of_isNormalizedLevel K (n + 1)
      (scaledCharacter K ψ (ϖ : K.Carrier)⁻¹) (scaledCharacter_eq_one_of_mem_maximalIdeal K hψ hϖ)
      _ 𝓛 m b hcont (hxm ▸ hlev) 0 (zero_mem _)
    simp only [add_zero] at hpow
    obtain ⟨hm, hb, A', hA', v, hv0, hvχ⟩ := hcont
    obtain ⟨e⟩ := Quotient.exact hA'
    let φ := SmoothRep.equivOfIso
      ((irreducibleAdmissibleProperty (k := ℂ)
        (G := GeneralLinear (n + 1) K.Carrier)).ι.mapIso e)
    have hφv : φ v ≠ 0 := by
      intro h
      apply hv0
      apply φ.injective
      rw [map_zero]
      exact h
    have hχ : ∀ g ∈ unitSubgroup K 𝓛 m, A.obj.representation g (φ v) =
        elementCharacter (traceCharacter (scaledCharacter K ψ (ϖ : K.Carrier)⁻¹)) b
          (Matrix.GeneralLinearGroup.toLin g) • φ v := by
      intro g hg
      have h1 : φ (A'.obj.representation g v) = A.obj.representation g (φ v) :=
        congrArg (fun f => f v) (φ.isIntertwining' g)
      rw [← h1, hvχ g hg, map_smul]
    have h := period_mul_exponent_eq_of_stratum K ψ hψ ν A.obj.representation hσ hσi c a hFE hϖ
      𝓛 hm _ hb hpow hφv hχ
    have he : (0 : ℚ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
    have h' : (𝓛.period : ℚ) * a = (n + 1) * m + 𝓛.period * (n + 1) := by exact_mod_cast h
    have ha : (a : ℚ) = (n + 1) * (1 + x) := by
      rw [hxm]
      field_simp
      linarith
    have hle : ((n : ℚ) + 1) ≤ a := by
      rw [ha]
      nlinarith
    rw [max_eq_left hle, ha]

end Padic

end Langlands.BushnellKutzko

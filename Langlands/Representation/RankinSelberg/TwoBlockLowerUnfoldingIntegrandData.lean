import Langlands.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData
import Langlands.HarmonicAnalysis.TwoBlockRowPartialFourierShape
import Langlands.HarmonicAnalysis.RowSchwartzAction
import Langlands.HarmonicAnalysis.PadicRowFourierEquivarianceProof

/-!
# The integrand of the Section 4.7 lower unfolding

JPSS (1983), Section 4.7, equation (1), printed pages 412-413: the right side is the
integral over `H_(t_1,t_2) \ G_r` of `f[g; e, e] W(w' g) |det g|^s (gΦ)~[ζ, η]`, where
`w' = w_r diag(w_(t_1), w_(t_2))`, `ζ = (1, 0, …, 0)`, `η = (0, …, 0, 1)` and
`Φ~(ξ, v) = ∫ Φ[(w, v)] ψ(ξ ᵗw) dw` integrates the first block of a row.

For two blocks of sizes `m 0 + 1` and `m 1 + 1` of total rank `t + 1`, actual block
functionals `ℓ_i` in the inverse-character spaces, a lower normalized section `f`, a test
function `W` in the standard-character space, a Schwartz–Bruhat function `Φ` and a supplied
additive Haar measure `μ`, this module constructs the partial Fourier value
`g ↦ (gΦ)~[ζ, η]`, proves its explicit formula and the absolute integrability of its inner
integrand, and constructs the unweighted scalar function

`[g] ↦ W(C g) ⟨f(g), ⊗ ℓ_i⟩ (gΦ)~[ζ, η]`

on the published quotient `H⁻ \ GL_(t+1)`, `C = w'`, by actual quotient descent. The three
covariance laws under `H⁻` (scalar section, partial Fourier value and `W(C ·)`) and their
cancellation are proved. The weight `|det g|^s`, outer measurability, outer integrability and
the Section 4.7 identity are not part of this module.
-/

noncomputable section

open MeasureTheory

namespace Langlands.RankinSelberg.TwoBlockLowerUnfolding

open GeneralLinear TwoBlockJacquet TwoBlockDeformation TwoBlockLowerUnipotentQuotient
  QuotientIntegration Whittaker HarmonicAnalysis HarmonicAnalysis.TwoBlockRowPartialFourier

universe uF uW uK uR

/-! ### The source rows `ζ` and `η` -/

section Rows

variable {K : Type uK}

/-- The row `ζ = (1, 0, …, 0)` of length `n + 1`. -/
def zeta [Zero K] [One K] (n : ℕ) : Fin (n + 1) → K :=
  fun i => if i = 0 then 1 else 0

/-- The row `η = (0, …, 0, 1)` of length `n + 1`. -/
def eta [Zero K] [One K] (n : ℕ) : Fin (n + 1) → K :=
  fun j => if j = Fin.last n then 1 else 0

theorem zeta_apply [Zero K] [One K] (n : ℕ) (i : Fin (n + 1)) :
    zeta (K := K) n i = if i = 0 then 1 else 0 := rfl

theorem eta_apply [Zero K] [One K] (n : ℕ) (j : Fin (n + 1)) :
    eta (K := K) n j = if j = Fin.last n then 1 else 0 := rfl

/-- Pairing with `ζ` reads the first coordinate. -/
theorem rowPairing_zeta [Field K] {n : ℕ} (w : Fin (n + 1) → K) :
    rowPairing w (zeta n) = w 0 := by
  simp [rowPairing, zeta]

/-- `η M` is the last row of `M`. -/
theorem vecMul_eta [CommRing K] {n d : ℕ} (M : Matrix (Fin (n + 1)) (Fin d) K) :
    Matrix.vecMul (eta n) M = fun j => M (Fin.last n) j := by
  funext j
  simp [Matrix.vecMul, dotProduct, eta]

/-- Right multiplication by an upper unipotent matrix does not change the first
coordinate of a row. -/
theorem vecMul_upperUnipotent_zero [CommRing K] {n : ℕ} (w : Fin (n + 1) → K)
    (u : upperUnipotent (n + 1) K) :
    Matrix.vecMul w (u : GeneralLinear (n + 1) K).val 0 = w 0 := by
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_eq_single 0]
  · rw [show (u : GeneralLinear (n + 1) K).val 0 0 = 1 from UpperUnipotent.entry_diag u 0,
      mul_one]
  · intro i _ hi
    rw [show (u : GeneralLinear (n + 1) K).val i 0 = 0 from
      UpperUnipotent.entry_eq_zero u (Fin.pos_iff_ne_zero.mpr hi), mul_zero]
  · intro h0
    exact absurd (Finset.mem_univ 0) h0

/-- Pairing with `ζ` is unchanged by right multiplication by an upper unipotent matrix. -/
theorem rowPairing_vecMul_upperUnipotent_zeta [Field K] {n : ℕ} (w : Fin (n + 1) → K)
    (u : upperUnipotent (n + 1) K) :
    rowPairing (Matrix.vecMul w (u : GeneralLinear (n + 1) K).val) (zeta n) =
      rowPairing w (zeta n) := by
  rw [rowPairing_zeta, rowPairing_zeta, vecMul_upperUnipotent_zero]

end Rows

/-! ### The row action of `H⁻` on `join (w, η)` -/

section RowAction

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) {R : Type uR} [CommRing R]

/-- The corner entry of `u ∈ H⁻`: last row of the second block, first column of the first
block. -/
def corner (u : lowerBlockUnipotent h R) : R :=
  (u : GeneralLinear (t + 1) R) ((succBlockShape m h).index 1 (Fin.last (m 1)))
    ((succBlockShape m h).index 0 0)

theorem corner_def (u : lowerBlockUnipotent h R) :
    corner h u = (u : GeneralLinear (t + 1) R) ((succBlockShape m h).index 1 (Fin.last (m 1)))
      ((succBlockShape m h).index 0 0) := rfl

/-- The last row `η X` of the lower-left block `X` of `u ∈ H⁻`. -/
def cornerRow (u : lowerBlockUnipotent h R) : Fin (m 0 + 1) → R :=
  fun a => (u : GeneralLinear (t + 1) R) ((succBlockShape m h).index 1 (Fin.last (m 1)))
    ((succBlockShape m h).index 0 a)

theorem cornerRow_zero (u : lowerBlockUnipotent h R) : cornerRow h u 0 = corner h u := rfl

/-- At `join (w, η)`, right multiplication by `u = [[n_a, 0], [X, n_b]] ∈ H⁻` gives first block
`w n_a + η X` and unchanged second block `η`. -/
theorem vecMul_join_eta (u : lowerBlockUnipotent h R) (w : Fin (m 0 + 1) → R) :
    Matrix.vecMul (join (succBlockEquiv h) w (eta (m 1))) (u : GeneralLinear (t + 1) R).val =
      join (succBlockEquiv h)
        (Matrix.vecMul w (diagonalBlocks h R u 0 : GeneralLinear (m 0 + 1) R).val +
          cornerRow h u) (eta (m 1)) := by
  obtain ⟨-, hlow, hdiag⟩ := (mem_lowerBlockUnipotent_iff h R u.val).mp u.property
  have hsum : ∀ k : Fin (t + 1),
      Matrix.vecMul (join (succBlockEquiv h) w (eta (m 1))) (u : GeneralLinear (t + 1) R).val k =
        (∑ a, w a * (u : GeneralLinear (t + 1) R) ((succBlockShape m h).index 0 a) k) +
          (u : GeneralLinear (t + 1) R) ((succBlockShape m h).index 1 (Fin.last (m 1))) k := by
    intro k
    simp only [Matrix.vecMul, dotProduct]
    rw [← Equiv.sum_comp (succBlockEquiv h), Fintype.sum_sum_type]
    simp only [join_inl, join_inr]
    simp only [succBlockEquiv_inl, succBlockEquiv_inr, eta, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  funext k
  obtain ⟨s, rfl⟩ := (succBlockEquiv h).surjective k
  rcases s with a' | b'
  · rw [hsum, join_inl, succBlockEquiv_inl]
    simp only [Pi.add_apply, Matrix.vecMul, dotProduct, cornerRow]
    rfl
  · rw [hsum, join_inr, succBlockEquiv_inr]
    simp only [index_zero_one_eq_zero h R u.property, mul_zero, Finset.sum_const_zero, zero_add,
      eta]
    by_cases hb : b' = Fin.last (m 1)
    · simp only [hb, ↓reduceIte]
      exact hdiag 1 _
    · simp only [hb, ↓reduceIte]
      exact hlow 1 _ _ (lt_of_le_of_ne (Fin.le_last b') hb)

end RowAction

/-! ### Covariance of the scalar section and of `W(C ·)` -/

section Covariance

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : letI := F.canonicalTopologicalData.topology
  HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier}

variable (ell : letI := F.canonicalTopologicalData.topology
  ∀ i, Whittaker.glInverseFunctionals ψ (m i) (σ i))

/-- Left translation by `u ∈ H⁻` multiplies the scalar section at the Levi identity by the
product of the two block inverse standard characters of the diagonal blocks of `u`. The
lower-left block of `u` is arbitrary; the half modulus is one because the diagonal blocks are
unipotent. -/
theorem scalarSection_lowerBlockUnipotent_mul (f : Sections F h σ)
    (u : lowerBlockUnipotent h F.Carrier) (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    scalarSection (fun i => (ell i).val) f (u.val * g) 1 =
      (∏ i, (inverseStandardCharacter ψ (m i) (diagonalBlocks h F.Carrier u i) : ℂ)) *
        scalarSection (fun i => (ell i).val) f g 1 := by
  let := F.canonicalTopologicalData.topology
  let q : (succBlockShape m h).oppositeParabolic F.Carrier :=
    Subgroup.inclusion (lowerBlockUnipotent_le_oppositeParabolic h F.Carrier) u
  let b := (succBlockShape m h).oppositeLeviProjection F.Carrier q
  have hcov := scalarSection_covariant (fun i => (ell i).val) f q (b := b) rfl g 1
  have hmod : F.canonicalTopologicalData.leviHalfModulus (succBlockShape m h) b = 1 :=
    (F.canonicalTopologicalData.leviHalfModulus_eq_one (succBlockShape m h) b).mpr
      (leviModulus_eq_one F h _ b fun i =>
        determinantNorm_eq_one_of_mem_upperUnipotent F _ (diagonalBlocks h F.Carrier u i).property)
  refine hcov.trans ?_
  rw [hmod, Units.val_one, inv_one, one_mul, one_mul, scalarSection_def, scalarSection_one]
  exact tensorContraction_blockTensor F h σ ψ _ (fun i => (ell i).property) b
    (fun i => (diagonalBlocks h F.Carrier u i).property) _

variable (Wtest : letI := F.canonicalTopologicalData.topology
  RankinSelberg.WhittakerFunctions ψ t)

/-- `W(C u g) = ψ_(H⁻)(u) W(C g)` for `u ∈ H⁻`: `C u C⁻¹` is upper unipotent with standard
character value the lower character of `u`. -/
theorem whittaker_blockRotation_lowerBlockUnipotent_mul (u : lowerBlockUnipotent h F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    Wtest.val (blockRotation h F.Carrier * (u.val * g)) =
      letI := F.canonicalTopologicalData.topology
      (lowerCharacter h ψ u : ℂ) * Wtest.val (blockRotation h F.Carrier * g) := by
  let := F.canonicalTopologicalData.topology
  have e : blockRotation h F.Carrier * (u.val * g) =
      (conjugationEquiv h F.Carrier u).val * (blockRotation h F.Carrier * g) := by
    rw [conjugationEquiv_apply_val]
    group
  rw [e]
  exact Wtest.property (conjugationEquiv h F.Carrier u) (blockRotation h F.Carrier * g)

end Covariance

/-! ### The partial Fourier value -/

/-- The canonical topology makes `F` a topological ring. -/
theorem isTopologicalRing_carrier {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) :
    letI := F.canonicalTopologicalData.topology
    IsTopologicalRing F.Carrier := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  infer_instance

/-- Every additive Haar measure on `F` is σ-finite, since `F` is locally compact and second
countable. -/
theorem sigmaFinite_additiveHaarMeasure {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    [MeasurableSpace F.Carrier]
    (μ : letI := F.canonicalTopologicalData.topology; AdditiveHaarMeasure F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    SigmaFinite μ.measure := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  have : SecondCountableTopology F.Carrier :=
    PadicField.TopologicalData.secondCountableTopology F.canonicalTopologicalData
  infer_instance

section PartialSection

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable [MeasurableSpace F.Carrier]

/-- The partial Fourier value `(gΦ)~[ζ, η]` of JPSS (4.7.1): the plus-sign first-block
integral of the row translate `x ↦ Φ(x g)` at `ξ = ζ`, second block `η`. -/
def partialSection
    (ψ : letI := F.canonicalTopologicalData.topology
      HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
    (μ : letI := F.canonicalTopologicalData.topology; AdditiveHaarMeasure F.Carrier)
    (Φ : letI := F.canonicalTopologicalData.topology; SchwartzBruhat (Fin (t + 1) → F.Carrier))
    (g : GeneralLinear (t + 1) F.Carrier) : ℂ :=
  letI := F.canonicalTopologicalData.topology
  letI := isTopologicalRing_carrier F
  rowPartialFourierIntegral ψ μ (succBlockEquiv h) (rowTranslate g Φ) (zeta (m 0)) (eta (m 1))

variable (ψ : letI := F.canonicalTopologicalData.topology
  HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
variable (μ : letI := F.canonicalTopologicalData.topology; AdditiveHaarMeasure F.Carrier)
variable (Φ : letI := F.canonicalTopologicalData.topology
  SchwartzBruhat (Fin (t + 1) → F.Carrier))

theorem partialSection_def (g : GeneralLinear (t + 1) F.Carrier) :
    partialSection h ψ μ Φ g =
      letI := F.canonicalTopologicalData.topology
      letI := isTopologicalRing_carrier F
      rowPartialFourierIntegral ψ μ (succBlockEquiv h) (rowTranslate g Φ) (zeta (m 0))
        (eta (m 1)) :=
  rfl

/-- The explicit formula
`(gΦ)~[ζ, η] = ∫ ψ(w_0) Φ((w, η) g) dw` for the supplied product measure. -/
theorem partialSection_apply (g : GeneralLinear (t + 1) F.Carrier) :
    partialSection h ψ μ Φ g =
      letI := F.canonicalTopologicalData.topology
      ∫ w, ψ.complex (w 0) *
        Φ (Matrix.vecMul (join (succBlockEquiv h) w (eta (m 1))) g.val)
          ∂rowMeasure μ (m 0 + 1) := by
  let := F.canonicalTopologicalData.topology
  simp only [partialSection, rowPartialFourierIntegral, rowTranslate_apply, rowPairing_zeta]

end PartialSection

section Integrability

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable [MeasurableSpace F.Carrier] [@BorelSpace F.Carrier F.canonicalTopologicalData.topology _]
variable (ψ : letI := F.canonicalTopologicalData.topology
  HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
variable (μ : letI := F.canonicalTopologicalData.topology; AdditiveHaarMeasure F.Carrier)
variable (Φ : letI := F.canonicalTopologicalData.topology
  SchwartzBruhat (Fin (t + 1) → F.Carrier))

/-- The inner integrand `w ↦ ψ(w_0) Φ((w, η) g)` is absolutely integrable for the supplied
product measure, for every `g`. -/
theorem partialSection_integrable (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    Integrable (fun w => ψ.complex (w 0) *
        Φ (Matrix.vecMul (join (succBlockEquiv h) w (eta (m 1))) g.val))
      (rowMeasure μ (m 0 + 1)) := by
  let := F.canonicalTopologicalData.topology
  have := sigmaFinite_additiveHaarMeasure μ
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  have : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
  have : TotallyDisconnectedSpace F.Carrier := by
    let : NonarchimedeanRing F.Carrier := by
      convert! ValuativeRel.nonarchimedeanRing F.Carrier
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  have hint := rowPartialFourierIntegrand_integrable ψ μ (succBlockEquiv h) (rowTranslate g Φ)
    (zeta (m 0)) (eta (m 1))
  simpa only [rowTranslate_apply, rowPairing_zeta] using hint

/-- Right multiplication by an upper unipotent matrix preserves the supplied product row
measure. -/
theorem rowMeasure_map_vecMul_upperUnipotent {d : ℕ}
    (n : upperUnipotent d F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    (rowMeasure μ d).map (fun x => Matrix.vecMul x (n : GeneralLinear d F.Carrier).val) =
      rowMeasure μ d := by
  let := F.canonicalTopologicalData.topology
  have := sigmaFinite_additiveHaarMeasure μ
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  have : SecondCountableTopology F.Carrier :=
    PadicField.TopologicalData.secondCountableTopology F.canonicalTopologicalData
  have hχ (a : F.Carrier) (ha : a ≠ 0) :
      μ.measure.map (fun x => a * x) =
        (F.canonicalTopologicalData.normalizedAbsHom a)⁻¹ • μ.measure :=
    padicScalarHaarScaling F F.canonicalTopologicalData μ.measure (Units.mk0 a ha)
  rw [rowMeasure_map_vecMul F.canonicalTopologicalData.normalizedAbsHom μ hχ n.val,
    RankinSelberg.unipotent_det, map_one, inv_one, one_smul]

/-- `(u g Φ)~[ζ, η] = ψ(-corner(u)) (gΦ)~[ζ, η]` for `u ∈ H⁻`: the unipotent change
`w ↦ w n_a` preserves the measure and the first coordinate, and the translation by the last
row of the lower-left block contributes the inverse corner phase. -/
theorem partialSection_lowerBlockUnipotent_mul
    (u : lowerBlockUnipotent h F.Carrier) (g : GeneralLinear (t + 1) F.Carrier) :
    partialSection h ψ μ Φ (u.val * g) =
      (letI := F.canonicalTopologicalData.topology; ψ.complex (-corner h u)) *
        partialSection h ψ μ Φ g := by
  let := F.canonicalTopologicalData.topology
  have := sigmaFinite_additiveHaarMeasure μ
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  have : SecondCountableTopology F.Carrier :=
    PadicField.TopologicalData.secondCountableTopology F.canonicalTopologicalData
  let n := diagonalBlocks h F.Carrier u 0
  let φ : (Fin (t + 1) → F.Carrier) → ℂ := rowTranslate g Φ
  have hmp : MeasurePreserving
      (fun x : Fin (m 0 + 1) → F.Carrier => Matrix.vecMul x (n : GeneralLinear _ F.Carrier).val)
      (rowMeasure μ (m 0 + 1)) (rowMeasure μ (m 0 + 1)) :=
    ⟨(rowHomeomorph (n : GeneralLinear (m 0 + 1) F.Carrier)).continuous.measurable,
      rowMeasure_map_vecMul_upperUnipotent μ n⟩
  have hemb : MeasurableEmbedding
      (fun x : Fin (m 0 + 1) → F.Carrier => Matrix.vecMul x (n : GeneralLinear _ F.Carrier).val) :=
    (rowHomeomorph (n : GeneralLinear (m 0 + 1) F.Carrier)).measurableEmbedding
  calc partialSection h ψ μ Φ (u.val * g)
      = ∫ w, (fun x => ψ.complex (rowPairing x (zeta (m 0))) *
            φ (join (succBlockEquiv h) (x + cornerRow h u) (eta (m 1))))
          (Matrix.vecMul w (n : GeneralLinear _ F.Carrier).val) ∂rowMeasure μ (m 0 + 1) := by
        simp only [partialSection, rowPartialFourierIntegral]
        congr 1
        funext w
        rw [rowTranslate_mul, rowTranslate_apply, vecMul_join_eta,
          rowPairing_vecMul_upperUnipotent_zeta]
    _ = ∫ x, ψ.complex (rowPairing x (zeta (m 0))) *
            φ (join (succBlockEquiv h) (x + cornerRow h u) (eta (m 1)))
          ∂rowMeasure μ (m 0 + 1) :=
        hmp.integral_comp hemb (fun x => ψ.complex (rowPairing x (zeta (m 0))) *
          φ (join (succBlockEquiv h) (x + cornerRow h u) (eta (m 1))))
    _ = ψ.complex (-rowPairing (cornerRow h u) (zeta (m 0))) *
          rowPartialFourierIntegral ψ μ (succBlockEquiv h) φ (zeta (m 0)) (eta (m 1)) :=
        integral_join_add ψ μ (succBlockEquiv h) φ (cornerRow h u) (zeta (m 0)) (eta (m 1))
    _ = ψ.complex (-corner h u) * partialSection h ψ μ Φ g := by
        rw [rowPairing_zeta, cornerRow_zero]
        rfl

end Integrability

/-! ### The scalar function and its descent -/

section Integrand

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : letI := F.canonicalTopologicalData.topology
  HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier}
variable [MeasurableSpace F.Carrier]
variable (ell : letI := F.canonicalTopologicalData.topology
  ∀ i, Whittaker.glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable (Wtest : letI := F.canonicalTopologicalData.topology
  RankinSelberg.WhittakerFunctions ψ t)
variable (Φ : letI := F.canonicalTopologicalData.topology
  SchwartzBruhat (Fin (t + 1) → F.Carrier))
variable (μ : letI := F.canonicalTopologicalData.topology; AdditiveHaarMeasure F.Carrier)

/-- The unweighted scalar function `g ↦ W(C g) ⟨f(g), ⊗ ℓ_i⟩ (gΦ)~[ζ, η]` on `GL_(t+1)`,
before descent. -/
def groupIntegrand (g : GeneralLinear (t + 1) F.Carrier) : ℂ :=
  letI := F.canonicalTopologicalData.topology
  Wtest.val (blockRotation h F.Carrier * g) * scalarSection (fun i => (ell i).val) f g 1 *
    partialSection h ψ μ Φ g

theorem groupIntegrand_def (g : GeneralLinear (t + 1) F.Carrier) :
    groupIntegrand ell f Wtest Φ μ g =
      letI := F.canonicalTopologicalData.topology
      Wtest.val (blockRotation h F.Carrier * g) * scalarSection (fun i => (ell i).val) f g 1 *
        partialSection h ψ μ Φ g :=
  rfl

variable [@BorelSpace F.Carrier F.canonicalTopologicalData.topology _]

/-- Left `H⁻`-invariance: the two positive block characters and the positive corner phase of
the lower character from `W(C ·)` cancel the inverse block characters from the scalar
section and the inverse corner phase from the partial Fourier value. -/
theorem groupIntegrand_lowerBlockUnipotent_mul (u : lowerBlockUnipotent h F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    groupIntegrand ell f Wtest Φ μ (u.val * g) = groupIntegrand ell f Wtest Φ μ g := by
  let := F.canonicalTopologicalData.topology
  have h0 : (standardCharacter ψ (m 0) (diagonalBlocks h F.Carrier u 0) : ℂ) *
      (inverseStandardCharacter ψ (m 0) (diagonalBlocks h F.Carrier u 0) : ℂ) = 1 :=
    Units.mul_inv _
  have h1 : (standardCharacter ψ (m 1) (diagonalBlocks h F.Carrier u 1) : ℂ) *
      (inverseStandardCharacter ψ (m 1) (diagonalBlocks h F.Carrier u 1) : ℂ) = 1 :=
    Units.mul_inv _
  have hc : ψ.complex (corner h u) * ψ.complex (-corner h u) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [groupIntegrand_def, groupIntegrand_def,
    whittaker_blockRotation_lowerBlockUnipotent_mul Wtest u g,
    scalarSection_lowerBlockUnipotent_mul ell f u g,
    partialSection_lowerBlockUnipotent_mul h ψ μ Φ u g,
    lowerCharacter_eq_diagonalBlocks, Fin.prod_univ_two]
  change (standardCharacter ψ (m 0) (diagonalBlocks h F.Carrier u 0) : ℂ) *
      (standardCharacter ψ (m 1) (diagonalBlocks h F.Carrier u 1) : ℂ) *
      ψ.complex (corner h u) * _ * _ * _ = _
  calc _ = ((standardCharacter ψ (m 0) (diagonalBlocks h F.Carrier u 0) : ℂ) *
          (inverseStandardCharacter ψ (m 0) (diagonalBlocks h F.Carrier u 0) : ℂ)) *
        ((standardCharacter ψ (m 1) (diagonalBlocks h F.Carrier u 1) : ℂ) *
          (inverseStandardCharacter ψ (m 1) (diagonalBlocks h F.Carrier u 1) : ℂ)) *
        (ψ.complex (corner h u) * ψ.complex (-corner h u)) *
        (Wtest.val (blockRotation h F.Carrier * g) *
          scalarSection (fun i => (ell i).val) f g 1 * partialSection h ψ μ Φ g) := by ring
    _ = _ := by rw [h0, h1, hc, one_mul, one_mul, one_mul]

/-- The unweighted integrand of JPSS (4.7.1) on the actual quotient `H⁻ \ GL_(t+1)`: the
actual descent of `groupIntegrand`. No coset representative is chosen. -/
def integrand : LowerQuotient h F.Carrier → ℂ :=
  descend (lowerBlockUnipotent h F.Carrier) (groupIntegrand ell f Wtest Φ μ)
    (groupIntegrand_lowerBlockUnipotent_mul ell f Wtest Φ μ)

/-- Representative formula: `integrand [g] = W(C g) ⟨f(g), ⊗ ℓ_i⟩ (gΦ)~[ζ, η]`. -/
@[simp]
theorem integrand_mk (g : GeneralLinear (t + 1) F.Carrier) :
    integrand ell f Wtest Φ μ (Quotient.mk _ g) =
      letI := F.canonicalTopologicalData.topology
      Wtest.val (blockRotation h F.Carrier * g) * scalarSection (fun i => (ell i).val) f g 1 *
        partialSection h ψ μ Φ g :=
  rfl

theorem integrand_mk_eq_groupIntegrand (g : GeneralLinear (t + 1) F.Carrier) :
    integrand ell f Wtest Φ μ (Quotient.mk _ g) = groupIntegrand ell f Wtest Φ μ g :=
  rfl

end Integrand

end Langlands.RankinSelberg.TwoBlockLowerUnfolding

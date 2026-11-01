import Langlands.Representation.GodementJacquet.WhittakerModelRationality
import Langlands.Representation.GodementJacquet.UniformWhittakerSliceBound
import Langlands.Representation.RankinSelberg.UniformFiniteFunctionMellinConvergenceStatement
import Langlands.Representation.Whittaker.TypeAsymptoticProof
import Langlands.Representation.GodementJacquet.ZetaLinear

/-!
# Common matrix convergence on actual coefficient models

A uniform finite-function Mellin threshold and the fixed unipotent-slice
exponents give one matrix-convergence half-plane before all model functions
and full-matrix tests. Finite smooth-dual averaging transfers that bound to
the actual bi-smooth coefficient span. The uniform Mellin premise is explicit.
-/

noncomputable section

namespace Langlands.GodementJacquet.WhittakerTorus.Padic

open MeasureTheory HarmonicAnalysis RankinSelberg Whittaker GeneralLinear
open scoped BigOperators ENNReal

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance uniformMatrixTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance uniformMatrixValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance uniformMatrixLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance uniformMatrixUnitsMeasurableSpace : MeasurableSpace F.Carrierˣ := borel _
local instance uniformMatrixUnitsBorelSpace : BorelSpace F.Carrierˣ := ⟨rfl⟩
local instance uniformMatrixMeasurableSpace (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance uniformMatrixBorelSpace (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance uniformMatrixUnipotentMeasurableSpace (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance uniformMatrixUnipotentBorelSpace (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ}

local instance uniformMatrixModelAddCommGroup
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ n σ) :
    AddCommGroup (glCoefficientModel ψ n σ ℓ).toSubmodule :=
  (glCoefficientModel ψ n σ ℓ).toSubmodule.addCommGroup

/-- Tail-product change of variables preserves a single half-plane chosen
before every pair of additive test functions. -/
theorem uniform_torusMellin
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (X : Finset (((Fin (n + 1) → F.Carrierˣ) → ℂ)))
    (hX : ∀ η ∈ X, IsFiniteFunction η) :
    ∃ c : ℝ, ∀ η ∈ X, ∀ (φ : SchwartzBruhat (Fin n → F.Carrier))
      (J : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
      ∀ s : ℂ, c < s.re → Integrable (torusIntegrand F φ J η s)
        (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) := by
  classical
  have : SecondCountableTopology F.Carrier :=
    PadicField.TopologicalData.secondCountableTopology F.canonicalTopologicalData
  have : SecondCountableTopology F.Carrierˣ := Units.isEmbedding_val₀.secondCountableTopology
  let pull := fun η : (Fin (n + 1) → F.Carrierˣ) → ℂ =>
    η ∘ (tailProdEquiv (G := F.Carrierˣ) (n := n)).toMonoidHom
  obtain ⟨c, hc⟩ := hU p inferInstance F F.canonicalTopologicalData (n + 1)
    (fun i => (i : ℕ) + 1) (fun _ => Nat.succ_pos _) (X.image pull) (by
      intro η hη
      obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.mp hη
      exact (hX ξ hξ).comp _ continuous_tailProd)
  refine ⟨c, ?_⟩
  intro η hη φ J s hs
  have hmp := measurePreserving_tailProd (E := F.Carrier) (n := n)
  have hme : MeasurableEmbedding (tailProd : (Fin (n + 1) → F.Carrierˣ) → _) :=
    (tailProdHomeomorph (G := F.Carrierˣ) (n := n)).toHomeomorph.measurableEmbedding
  rw [← hmp.integrable_comp_emb hme]
  change Integrable (fun x => torusIntegrand F φ J η s (tailProd x)) _
  simpa [torusIntegrand_tailProd, pull, tailProdEquiv] using
    hc (pull η) (Finset.mem_image.mpr ⟨η, hη, rfl⟩) (initTail F φ J) s hs

/-- The unipotent/torus estimate at a fixed parameter, using the common
finite family and fixed slice exponents. -/
theorem lintegral_torus_lt_top_of_uniform_terms
    {ψ : UnitaryAdditiveCharacter F.Carrier}
    {W : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ} (hW : IsWhittakerLike F ψ W)
    (Φ : MatrixTestFunction n F.Carrier) {k : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hk : k ∈ integralK F n)
    (X : Finset (((Fin (n + 1) → F.Carrierˣ) → ℂ)))
    (φ : ((Fin (n + 1) → F.Carrierˣ) → ℂ) → SchwartzBruhat (Fin n → F.Carrier))
    (hφ : ∀ a, W (Iwasawa.diagonalUnits a * k) =
      ∑ χ ∈ X, φ χ (ratios F a) * χ a)
    (s : ℂ)
    (hterms : ∀ (J : SchwartzBruhat (Fin (n + 1) → F.Carrier)), ∀ χ ∈ X,
      Integrable (torusIntegrand F (φ χ) J (χ * torusWeight F (sliceExponents F n)) s)
        (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier)) :
    ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
        ∫⁻ u, ‖GodementJacquet.Padic.matrixIntegrand F Φ s W
          (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F.Carrier n
      ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) < ⊤ := by
  obtain ⟨B, ρ, hρ, hslice⟩ := exists_uniform_slice_bound F Φ k
  let e := sliceExponents F n
  let J := boxTest F n hρ
  have hint := hterms J
  have hpt : ∀ a : Fin (n + 1) → F.Carrierˣ,
      ENNReal.ofReal ((borelModulus F a)⁻¹) *
          ∫⁻ u, ‖GodementJacquet.Padic.matrixIntegrand F Φ s W
            (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F.Carrier n ≤
        ENNReal.ofReal B *
          ∑ χ ∈ X, ‖torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ := by
    intro a
    rw [lintegral_unipotent_matrixIntegrand F hW.equivariant Φ s a hk]
    have hsum : W (Iwasawa.diagonalUnits a * k) *
        (J (fun i => (a i : F.Carrier)) * torusWeight F e a *
          ((F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) : ℝ) : ℂ) ^ s) =
        ∑ χ ∈ X, torusIntegrand F (φ χ) J (χ * torusWeight F e) s a := by
      rw [show W (Iwasawa.diagonalUnits a * k) = ∑ χ ∈ X, φ χ (ratios F a) * χ a from hφ a,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun χ _ => ?_
      simp only [torusIntegrand, Pi.mul_apply]
      ring
    calc ENNReal.ofReal ((borelModulus F a)⁻¹) *
          (‖W (Iwasawa.diagonalUnits a * k) *
            ((F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) : ℝ) : ℂ) ^ s‖ₑ *
          ∫⁻ u, ‖Φ (u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) * k.val)‖ₑ
            ∂unipotentHaar F.Carrier n)
        ≤ ENNReal.ofReal ((borelModulus F a)⁻¹) *
          (‖W (Iwasawa.diagonalUnits a * k) *
            ((F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) : ℝ) : ℂ) ^ s‖ₑ *
          (ENNReal.ofReal B * ENNReal.ofReal (torusMonomial F e a) *
            ‖J (fun i => (a i : F.Carrier))‖ₑ)) := by
          gcongr
          exact hslice a
      _ = ENNReal.ofReal B * ‖W (Iwasawa.diagonalUnits a * k) *
          (J (fun i => (a i : F.Carrier)) * torusWeight F e a *
            ((F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) : ℝ) : ℂ) ^
              s)‖ₑ := by
          simp only [enorm_mul]
          rw [enorm_torusWeight]
          ring
      _ = ENNReal.ofReal B *
          ‖∑ χ ∈ X, torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ := by
          rw [hsum]
      _ ≤ ENNReal.ofReal B *
          ∑ χ ∈ X, ‖torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ := by
          gcongr
          exact enorm_sum_le _ _
  calc ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
          ∫⁻ u, ‖GodementJacquet.Padic.matrixIntegrand F Φ s W
            (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F.Carrier n
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier)
      ≤ ∫⁻ a, ENNReal.ofReal B *
          ∑ χ ∈ X, ‖torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal B * ∑ χ ∈ X, ∫⁻ a, ‖torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ fun χ hχ => (hint χ hχ).aestronglyMeasurable.enorm]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 fun χ hχ =>
        hasFiniteIntegral_iff_enorm.1 (hint χ hχ).hasFiniteIntegral)

/-- One fixed finite torus family gives one convergence threshold for all
Whittaker-like functions with expansions in that family and all matrix tests. -/
theorem exists_common_matrix_halfPlane
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (X : Finset (((Fin (n + 1) → F.Carrierˣ) → ℂ)))
    (hX : ∀ χ ∈ X, IsFiniteFunction χ) :
    ∃ c : ℝ, ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (W : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ),
      IsWhittakerLike F ψ W →
      (∀ k : Langlands.GeneralLinear (n + 1) F.Carrier,
        ∃ φ : ((Fin (n + 1) → F.Carrierˣ) → ℂ) → SchwartzBruhat (Fin n → F.Carrier),
          ∀ a, W (Iwasawa.diagonalUnits a * k) =
            ∑ χ ∈ X, φ χ (ratios F a) * χ a) →
      ∀ (Φ : MatrixTestFunction n F.Carrier) (s : ℂ), c < s.re →
        GodementJacquet.Padic.MatrixConverges F Φ s W := by
  classical
  let twist := fun χ : (Fin (n + 1) → F.Carrierˣ) → ℂ =>
    χ * torusWeight F (sliceExponents F n)
  obtain ⟨c, hc⟩ := uniform_torusMellin F hU (X.image twist) (by
    intro η hη
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hη
    exact (hX χ hχ).mul (isFiniteFunction_torusWeight F _))
  refine ⟨c, ?_⟩
  intro ψ W hW hexp Φ s hs
  have htorus : ∀ k ∈ integralK F n,
      ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
          ∫⁻ u, ‖GodementJacquet.Padic.matrixIntegrand F Φ s W
            (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F.Carrier n
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) < ⊤ := by
    intro k hk
    obtain ⟨φ, hφ⟩ := hexp k
    exact lintegral_torus_lt_top_of_uniform_terms F hW Φ hk X φ hφ s
      (fun J χ hχ => hc (twist χ) (Finset.mem_image.mpr ⟨χ, hχ, rfl⟩) (φ χ) J s hs)
  obtain ⟨K₀, S, hK₀K, hSK, hinv, hlin, -⟩ := IsWhittakerLike.exists_cosetSum F hW Φ
  have hmeas := measurable_matrixIntegrand F hW.continuous Φ s
  change Integrable (GodementJacquet.Padic.matrixIntegrand F Φ s W) (generalLinearHaar F.Carrier n)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_iwasawa F _ hmeas.enorm,
    hlin (fun k => ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
        ∫⁻ u, ‖GodementJacquet.Padic.matrixIntegrand F Φ s W
          (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F.Carrier n
      ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier))
      fun k _ k₀ hk₀ => ?_]
  · refine ENNReal.sum_lt_top.2 fun k hk => ENNReal.mul_lt_top ?_ (htorus k (hSK hk))
    exact (measure_mono fun x hx => hK₀K hx).trans_lt
      ((generalLinearHaar_integralSubgroup F.Carrier n).trans_lt ENNReal.one_lt_top)
  · refine lintegral_congr fun a => ?_
    congr 1
    refine lintegral_congr fun u => ?_
    rw [← mul_assoc, hinv s _ k₀ hk₀]

/-- A common shifted half-plane precedes every functional, model vector and
matrix test, using a fixed coefficient-torus expansion. -/
theorem exists_common_glModel_halfPlane
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsAdmissible σ) (hexp : CoefficientTorusExpansion (standardCharacter ψ n) σ) :
    ∃ c : ℝ, ∀ (ℓ : glFunctionals ψ n σ) (Φ : MatrixTestFunction n F.Carrier)
      (w : (glCoefficientModel ψ n σ ℓ).toSubmodule) (s : ℂ), c < s.re →
      GodementJacquet.Padic.MatrixConverges F Φ (s + jpssShift n)
        (glModelFunction ψ n σ ℓ w) := by
  obtain ⟨X, hX, hφ⟩ := hexp
  obtain ⟨c, hc⟩ := exists_common_matrix_halfPlane F hU X hX
  refine ⟨c - (jpssShift n).re, ?_⟩
  intro ℓ Φ w s hs
  refine hc ψ (glModelFunction ψ n σ ℓ w)
    (glModelFunction_isWhittakerLike F ψ σ hσ ⟨X, hX, hφ⟩ ℓ w) ?_ Φ _ ?_
  · intro k
    obtain ⟨φ, hφ'⟩ := hφ ℓ (glModelRepresentation ψ n σ ℓ k w)
    exact ⟨φ, hφ'⟩
  · rw [Complex.add_re]
    linarith

/-- Common convergence for model functions transfers to an individual actual
smooth coefficient at the same parameter. -/
theorem modelCoefficient_converges_of_modelFunctions
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsAdmissible σ) (ℓ : glFunctionals ψ n σ)
    (Φ : MatrixTestFunction n F.Carrier)
    (Λ : SmoothDual (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ))
    (w : smoothVectors (glModelRepresentation ψ n σ ℓ)) (s : ℂ)
    (hconv : ∀ (Ψ : MatrixTestFunction n F.Carrier)
      (v : (glCoefficientModel ψ n σ ℓ).toSubmodule),
      GodementJacquet.Padic.MatrixConverges F Ψ s (glModelFunction ψ n σ ℓ v)) :
    GodementJacquet.Padic.MatrixConverges F Φ s
      (GodementJacquet.biSmoothCoefficient (glModelRepresentation ψ n σ ℓ) Λ w) := by
  obtain ⟨K, -, hK⟩ := GodementJacquet.Padic.exists_compactOpen_matrixTest_invariant F Φ
  obtain ⟨L, hL, hLK, t, c, hc⟩ := GodementJacquet.Padic.exists_eq_sum_modelPointAverage
    F ψ σ hσ.1 ℓ (GodementJacquet.Padic.glModel_isAdmissible F ψ σ ℓ hσ) Λ K
  exact (GodementJacquet.Padic.matrixIntegral_sum_modelPointAverage F ψ σ hσ.1 ℓ
    Φ L hL (fun k hk => hK k (hLK hk)) t c w.val
    (GodementJacquet.biSmoothCoefficient (glModelRepresentation ψ n σ ℓ) Λ w)
    (fun g => hc _) s (fun h _ => hconv _ _)).1

/-- One common half-plane for every actual bi-smooth coefficient of every
coefficient model, including reducible originals and the zero functional. -/
theorem exists_common_modelMatrix_halfPlane
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsAdmissible σ) (hexp : CoefficientTorusExpansion (standardCharacter ψ n) σ) :
    ∃ c : ℝ, ∀ (ℓ : glFunctionals ψ n σ) (Φ : MatrixTestFunction n F.Carrier)
      (f : GodementJacquet.biSmoothMatrixCoefficients (glModelRepresentation ψ n σ ℓ))
      (s : ℂ), c < s.re →
      GodementJacquet.Padic.MatrixConverges F Φ (s + jpssShift n) f.val := by
  obtain ⟨c, hc⟩ := exists_common_glModel_halfPlane F hU ψ σ hσ hexp
  refine ⟨c, ?_⟩
  intro ℓ Φ f s hs
  apply GodementJacquet.matrixConverges_of_mem_span (f := f.val) _ f.property
  rintro g ⟨Λ, w, rfl⟩
  exact modelCoefficient_converges_of_modelFunctions F ψ σ hσ ℓ Φ Λ w _
    (fun Ψ v => hc ℓ Ψ v s hs)

/-- Full Whittaker type supplies the fixed expansion through the published
asymptotic proof. Only uniform Mellin convergence remains an explicit premise. -/
theorem exists_modelMatrixConvergenceBound
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) :
    ∃ c : ℝ, ∀ (ℓ : glFunctionals ψ n σ) (Φ : MatrixTestFunction n F.Carrier)
      (f : GodementJacquet.biSmoothMatrixCoefficients (glModelRepresentation ψ n σ ℓ))
      (s : ℂ), c < s.re →
      GodementJacquet.Padic.MatrixConverges F Φ (s + jpssShift n) f.val := by
  exact exists_common_modelMatrix_halfPlane F hU ψ σ hσ.1
    (modelAsymptoticTransfer whittakerTypeAsymptotic p inferInstance F F.canonicalTopologicalData
      n V σ ψ (standardCharacter ψ n) (Or.inl rfl) hσ)

/-- A common real convergence bound on all actual coefficient models of a
full Whittaker-type representation. The uniform Mellin premise is explicit. -/
def modelMatrixConvergenceBound
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) : ℝ :=
  Classical.choose (exists_modelMatrixConvergenceBound F hU ψ σ hσ)

/-- The chosen bound precedes the functional, full-matrix test, actual
bi-smooth coefficient and spectral parameter. -/
theorem modelMatrixConvergenceBound_spec
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (Φ : MatrixTestFunction n F.Carrier)
    (f : GodementJacquet.biSmoothMatrixCoefficients (glModelRepresentation ψ n σ ℓ))
    (s : ℂ) (hs : modelMatrixConvergenceBound F hU ψ σ hσ < s.re) :
    GodementJacquet.Padic.MatrixConverges F Φ (s + jpssShift n) f.val :=
  Classical.choose_spec (exists_modelMatrixConvergenceBound F hU ψ σ hσ) ℓ Φ f s hs

/-- Common shifted matrix convergence on each actual coefficient-model
representation, under uniform finite-function Mellin convergence. -/
theorem glModel_matrixConvergesOnRight
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) (ℓ : glFunctionals ψ n σ) :
    GodementJacquet.MatrixConvergesOnRight
      (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier n)
      (glModelRepresentation ψ n σ ℓ) :=
  ⟨modelMatrixConvergenceBound F hU ψ σ hσ,
    modelMatrixConvergenceBound_spec F hU ψ σ hσ ℓ⟩

end Langlands.GodementJacquet.WhittakerTorus.Padic

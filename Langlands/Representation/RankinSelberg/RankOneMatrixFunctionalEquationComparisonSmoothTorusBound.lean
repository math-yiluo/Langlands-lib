import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonDiscreteTorus
import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.Representation.GodementJacquet.MatrixTestTranslates
import Langlands.Representation.MatrixCoefficient.LawsProof
import Langlands.Representation.Conductor.PrincipalCongruenceBasisProof
import Langlands.Group.GL.NormalizedCharacter

/-! Discrete torus bounds for the actual smooth matrix coefficient family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear Topology Conductor GodementJacquet HarmonicAnalysis
open scoped ENNReal NNReal

universe uF uV uG

/-- Every member of the actual finite span of bi-smooth coefficients is
continuous and fixed on the right by some open subgroup. -/
theorem biSmoothMatrixCoefficient_continuous_rightFixed
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ G V) (f : biSmoothMatrixCoefficients σ) :
    Continuous f.val ∧ ∃ K : OpenSubgroup G,
      ∀ k ∈ K, ∀ g, f.val (g * k) = f.val g := by
  have aux : ∀ x ∈ biSmoothMatrixCoefficients σ,
      Continuous x ∧ ∃ K : OpenSubgroup G, ∀ k ∈ K, ∀ g, x (g * k) = x g := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨L, v, rfl⟩ := hx
      refine ⟨matrixCoefficient_isLocallyConstant σ (smoothDualPairing σ L) v.val
        v.property |>.continuous, ?_⟩
      obtain ⟨K, hK⟩ := v.property
      refine ⟨K, ?_⟩
      intro k hk g
      change matrixCoefficient σ (smoothDualPairing σ L) v.val (g * k) = _
      have hkv : σ k v.val = v.val := hK ⟨k, hk⟩
      rw [matrixCoefficient_mul, hkv]
      rfl
    | zero =>
      exact ⟨continuous_const, ⊤, fun k hk g => rfl⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨hc, K, hK⟩ := ihx
      obtain ⟨hd, J, hJ⟩ := ihy
      refine ⟨hc.add hd, K ⊓ J, ?_⟩
      intro k hk g
      exact congrArg₂ (· + ·) (hK k hk.1 g) (hJ k hk.2 g)
    | smul c x hx ih =>
      obtain ⟨hc, K, hK⟩ := ih
      refine ⟨hc.const_smul c, K, ?_⟩
      intro k hk g
      exact congrArg (c • ·) (hK k hk g)
  exact aux f.val f.property

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance smoothTorusTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance smoothTorusValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance smoothTorusLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance smoothTorusT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance smoothTorusSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance smoothTorusMeasurable : MeasurableSpace F.Carrier := borel _
local instance smoothTorusBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance smoothTorusGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance smoothTorusGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance smoothTorusGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance smoothTorusGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance smoothTorusExponentCountable (n : ℕ) :
    Countable (Multiplicative (Fin (n + 1) → ℤ)) :=
  Countable.of_equiv (Fin (n + 1) → ℤ) Multiplicative.ofAdd

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The entire matrix integrand has a principal right stabilizer independent
of the spectral exponent. -/
theorem matrixIntegrand_exists_principalFixed
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (Φ : MatrixTestFunction n F.Carrier) (f : biSmoothMatrixCoefficients σ) :
    ∃ a : ℕ, 0 < a ∧ ∀ s : ℂ,
      ∀ k ∈ principalLevelSubgroup F.Carrier n a, ∀ g,
        matrixIntegrand abv Φ s f.val (g * k) = matrixIntegrand abv Φ s f.val g := by
  obtain ⟨hc, K, hK⟩ := biSmoothMatrixCoefficient_continuous_rightFixed σ f
  have ht : Filter.Tendsto
      (fun k : Langlands.GeneralLinear (n + 1) F.Carrier =>
        ((1 : Langlands.GeneralLinear (n + 1) F.Carrier), k))
      (𝓝 1) (𝓝 (1, 1)) :=
    (continuous_const.prodMk continuous_id).tendsto _
  have hΦ : {k : Langlands.GeneralLinear (n + 1) F.Carrier |
      ∀ X, Φ (X * k.val) = Φ X} ∈ 𝓝 1 := by
    change ∀ᶠ k in 𝓝 (1 : Langlands.GeneralLinear (n + 1) F.Carrier),
      ∀ X, Φ (X * k.val) = Φ X
    simpa only [Units.val_one, Matrix.one_mul] using
      ht.eventually (eventually_matrixTranslate_eq Φ)
  obtain ⟨a, ha, haU⟩ := exists_pos_principalLevelOpenSubgroup_subset F.Carrier n
    (Filter.inter_mem (K.isOpen.mem_nhds K.one_mem) hΦ)
  refine ⟨a, ha, ?_⟩
  intro s k hk g
  have hkg := haU hk
  have hnorm := F.canonicalTopologicalData.determinantNorm_eq_one_of_mem_compact
    (n + 1) (principalLevelSubgroup F.Carrier n a)
    (isCompact_principalLevelOpenSubgroup F.Carrier n a) k hk
  have hdet : abv (Matrix.det k.val) = 1 := by
    simpa using congrArg (fun t : ℝ≥0ˣ => ((t : ℝ≥0) : ℝ)) hnorm
  simp only [matrixIntegrand, Units.val_mul, hkg.2 g.val, hK k hkg.1 g, determinantWeight,
    Matrix.det_mul, map_mul, hdet, mul_one]

/-- Measurability of the genuine integrand, including its complex spectral
weight, for every member of the actual bi-smooth coefficient span. -/
theorem measurable_biSmooth_matrixIntegrand
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (Φ : MatrixTestFunction n F.Carrier) (f : biSmoothMatrixCoefficients σ) (s : ℂ) :
    Measurable (matrixIntegrand abv Φ s f.val) := by
  have hf := (biSmoothMatrixCoefficient_continuous_rightFixed σ f).1
  have hc : Continuous fun g : Langlands.GeneralLinear (n + 1) F.Carrier =>
      ((abv (Matrix.det g.val) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (F.canonicalTopologicalData.determinantNormContinuous (n + 1)).continuous))
  exact ((Φ.continuous.comp Units.continuous_val).measurable.mul hf.measurable).mul
    (hc.measurable.pow_const s)

/-- The literal full-matrix integrand evaluated on the uniformizer exponent
lattice; the spectral exponent and the coefficient are unchanged. -/
def matrixUniformizerTorusIntegrand {n : ℕ} (ϖ : F.Carrierˣ)
    (Φ : MatrixTestFunction n F.Carrier) (s : ℂ)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (e : Multiplicative (Fin (n + 1) → ℤ)) : ℂ :=
  matrixIntegrand abv Φ s f (Iwasawa.torus ϖ e.toAdd)

/-- An actual convergent matrix integrand has a finite norm sum on the
uniformizer exponent lattice. -/
theorem tsum_enorm_biSmooth_matrixIntegrand_lt_top
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (Φ : MatrixTestFunction n F.Carrier) (f : biSmoothMatrixCoefficients σ)
    (s : ℂ) (ϖ : F.Carrierˣ)
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ)
    (hi : GodementJacquet.Padic.MatrixConverges F Φ s f.val) :
    (∑' e : Multiplicative (Fin (n + 1) → ℤ),
      ‖matrixUniformizerTorusIntegrand F ϖ Φ s f.val e‖ₑ) < ⊤ := by
  obtain ⟨a, ha, hfixed⟩ := matrixIntegrand_exists_principalFixed F σ Φ f
  exact tsum_enorm_uniformizerTorus_lt_top_of_principalFixed F n a ϖ hϖ _
    (measurable_biSmooth_matrixIntegrand F σ Φ f s) (hfixed s) hi

/-- The supplied common matrix half-plane also controls every genuine
discrete torus norm sum, with the same shift and the same common bound. -/
theorem biSmooth_matrixTorus_convergesOnRight
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F σ) :
    ∃ b : ℝ, ∀ Φ : MatrixTestFunction n F.Carrier, ∀ f : biSmoothMatrixCoefficients σ,
      ∀ s : ℂ, b < s.re → ∀ ϖ : F.Carrierˣ,
      Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ →
      (∑' e : Multiplicative (Fin (n + 1) → ℤ),
        ‖matrixUniformizerTorusIntegrand F ϖ Φ (s + jpssShift n) f.val e‖ₑ) < ⊤ := by
  obtain ⟨b, hb⟩ := hMatrix
  exact ⟨b, fun Φ f s hs ϖ hϖ =>
    tsum_enorm_biSmooth_matrixIntegrand_lt_top F σ Φ f (s + jpssShift n) ϖ hϖ
      (hb Φ f s hs)⟩

end Langlands.RankinSelberg

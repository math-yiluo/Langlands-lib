import Langlands.Representation.Classification.TemperedSupportProof
import Langlands.Representation.Unitary.SquareIntegrableProof
import Langlands.Representation.Unitary.Restriction
import Langlands.Representation.Induction.UnitaryProof
import Langlands.Representation.Induction.InverseTranspose
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Group.GL.LeviCentralQuotientMeasure
import Langlands.Group.GL.CompactOpen

/-!
# Unitarity of irreducible analytically tempered GL_n representations

An irreducible tempered representation embeds into the normalized opposite
induction of an irreducible square-integrable Levi representation. The Levi
representation is unitarizable by the generic square-integrable form, opposite
induction is reduced to upper induction by inverse transpose, and the induced
form is pulled back along the embedding.
-/

noncomputable section

namespace Langlands

open MeasureTheory
open scoped NNReal

universe uF uV uG uH

/-- On a locally compact group without nontrivial positive characters, every
regular Haar measure is right invariant. -/
theorem isMulRightInvariant_of_positiveCharacter_eq_one {Q : Type uG} [Group Q]
    [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q]
    (hχ : ∀ (χ : Q →* ℝ≥0) (q : Q), χ q = 1)
    (μ : Measure Q) [μ.IsHaarMeasure] [μ.Regular] : Measure.IsMulRightInvariant μ := by
  constructor
  intro q
  have : (Measure.map (fun x => x * q) μ).Regular :=
    Measure.Regular.map (μ := μ) (Homeomorph.mulRight q)
  rw [Measure.isMulLeftInvariant_eq_smul_of_regular
    (Measure.map (fun x => x * q) μ) μ,
    ← Measure.modularCharacterFun_eq_haarScalarFactor]
  change Measure.modularCharacter q • μ = μ
  rw [hχ, one_smul]

namespace GeneralLinear.BlockShape

variable {n : ℕ} (B : BlockShape n)

/-- A scalar matrix in one block is central in the product Levi. -/
theorem mulSingle_scalar_mem_center {R : Type uF} [CommRing R] (i : Fin B.length) (a : Rˣ) :
    (Pi.mulSingle i (Matrix.GeneralLinearGroup.scalar (Fin (B.size i)) a) : B.Levi R) ∈
      Subgroup.center (B.Levi R) := by
  rw [Subgroup.mem_center_iff]
  intro g
  funext j
  by_cases h : j = i
  · subst h
    simp only [Pi.mul_apply, Pi.mulSingle_eq_same]
    exact (Matrix.GeneralLinearGroup.scalar_commute a (g j)).symm
  · simp [Pi.mulSingle_eq_of_ne h]

/-- Blockwise inverse transpose of the actual product Levi. -/
def leviInverseTranspose (R : Type uF) [CommRing R] : B.Levi R ≃* B.Levi R :=
  MulEquiv.piCongrRight fun i => GeneralLinear.inverseTranspose (B.size i) R

@[simp] theorem leviInverseTranspose_apply (R : Type uF) [CommRing R] (m : B.Levi R)
    (i : Fin B.length) :
    B.leviInverseTranspose R m i = GeneralLinear.inverseTranspose (B.size i) R (m i) := rfl

/-- Blockwise inverse transpose of the Levi part of an inverse-transposed lower element
recovers the lower Levi part. -/
theorem leviInverseTranspose_leviProjection_oppositeToUpper (R : Type uF) [CommRing R]
    (q : B.oppositeParabolic R) :
    B.leviInverseTranspose R (B.leviProjection R (B.oppositeToUpperInverseTranspose R q)) =
      B.oppositeLeviProjection R q := by
  funext i
  rw [leviInverseTranspose_apply, B.leviProjection_oppositeToUpperInverseTranspose,
    GeneralLinear.inverseTranspose_involutive]

end GeneralLinear.BlockShape

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Every Borel Haar measure on the full central quotient of an actual product
Levi is right invariant. -/
theorem leviCentralQuotientHaar_rightInvariant (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.leviTopology B
    ∀ [MeasurableSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
      [BorelSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
      (μ : Measure (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)))
      [μ.IsHaarMeasure], Measure.IsMulRightInvariant μ := by
  let := T.leviTopology B
  intro _ _ μ _
  let := T.leviTopologicalGroup B
  let Q := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
  have h := (glBlockCentralQuotientTopology p F T n).2 B
  let : T2Space Q := h.2.1
  let : LocallyCompactSpace Q := h.2.2.1
  let : SecondCountableTopology Q := h.2.2.2.1
  exact isMulRightInvariant_of_positiveCharacter_eq_one
    (B.leviCentralQuotient_positiveCharacter_eq_one (F := F.Carrier)) μ

/-- Compact open subgroups are cofinal among open subgroups of the product Levi. -/
theorem leviCompactOpen_cofinal (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.leviTopology B
    ∀ K : OpenSubgroup (B.Levi F.Carrier), ∃ L : OpenSubgroup (B.Levi F.Carrier),
      IsCompact (L : Set (B.Levi F.Carrier)) ∧ L ≤ K := by
  let := T.leviTopology B
  intro K
  obtain ⟨L, hLc, hLK⟩ := T.leviCompactOpen B K K.mem_nhds_one
  exact ⟨L, hLc, fun x hx => hLK hx⟩

/-- An irreducible product-Levi representation that is square-integrable modulo
the center for every Borel Haar measure is smooth and unitarizable, by the
generic square-integrable unitarity theorem. -/
theorem leviSquareIntegrable_smooth_unitarizable
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    {W : Type uV} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (B.Levi F.Carrier) W) (hirr : Representation.IsIrreducible σ)
    (hL2 : letI := T.topology
      letI := T.leviTopologicalGroup B
      let Q := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
      ∀ [MeasurableSpace Q] [BorelSpace Q]
        (μ : Measure Q) [μ.IsHaarMeasure], IsSquareIntegrableModCenter σ μ) :
    (letI := T.leviTopology B; IsSmooth σ) ∧ IsUnitarizable σ := by
  let := T.topology
  let := T.leviTopologicalGroup B
  let := T.leviT2Space B
  let := T.leviLocallyCompactSpace B
  have : ∀ i : Fin B.length, SecondCountableTopology (GeneralLinear (B.size i) F.Carrier) :=
    fun i => T.generalLinearSecondCountableTopology (B.size i)
  let Q := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
  let : MeasurableSpace Q := borel Q
  have : BorelSpace Q := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_leviCentralQuotient B
  have hμσ := hL2 μ
  have : μ.IsMulRightInvariant := T.leviCentralQuotientHaar_rightInvariant B μ
  exact ⟨hμσ.1.1,
    squareIntegrableUnimodularUnitarity.{uF, uV} (B.Levi F.Carrier) (T.leviCompactOpen_cofinal B)
      W σ μ hirr hμσ⟩

/-- Normalized opposite induction preserves unitarizability of smooth Levi
representations. The Levi representation is pulled back by blockwise inverse
transpose, induced to the upper parabolic (where the published upper
normalized-induction theorem applies), and the ambient action is pulled back
by inverse transpose. -/
theorem isUnitarizable_normalizedOppositeParabolicInduced
    (T : F.TopologicalData) {n : ℕ} (hn : 0 < n) (B : GeneralLinear.BlockShape n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    (hs : letI := T.leviTopology B; IsSmooth σ) (hu : IsUnitarizable σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsUnitarizable (T.normalizedOppositeParabolicInduced B σ) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let θM := B.leviInverseTranspose F.Carrier
  let σ' := σ.comp θM.toMonoidHom
  have hθM : Continuous θM := continuous_pi fun i =>
    (GeneralLinear.continuous_inverseTranspose (B.size i) F.Carrier).comp (continuous_apply i)
  have hs' : IsSmooth σ' := isSmooth_comp θM.toMonoidHom hθM hs
  have hI := glNormalizedParabolicInductionUnitarity.{uF, uV} p F T n hn B V σ' hs'
    (hu.comp θM.toMonoidHom)
  have hI' := hI.comp (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom
  have hστ : ∀ q : B.oppositeParabolic F.Carrier,
      twist (T.parabolicHalfModulus B) (σ'.comp (B.leviProjection F.Carrier))
          (B.oppositeToUpperInverseTranspose F.Carrier q) =
        twist (T.oppositeParabolicHalfModulus B)
          (σ.comp (B.oppositeLeviProjection F.Carrier)) q := by
    intro q
    apply LinearMap.ext
    intro v
    change (T.parabolicHalfModulus B (B.oppositeToUpperInverseTranspose F.Carrier q) : ℂ) •
        σ (θM (B.leviProjection F.Carrier (B.oppositeToUpperInverseTranspose F.Carrier q))) v =
      (T.oppositeParabolicHalfModulus B q : ℂ) • σ (B.oppositeLeviProjection F.Carrier q) v
    rw [T.parabolicHalfModulus_oppositeToUpperInverseTranspose,
      B.leviInverseTranspose_leviProjection_oppositeToUpper]
  exact (isUnitarizable_iff_of_equiv (Induction.precomposeSmoothInducedEquiv
    (GeneralLinear.inverseTransposeContinuous n F.Carrier)
    (B.oppositeToUpperInverseTranspose F.Carrier) (fun _ => rfl) hστ)).mp hI'

end PadicField.TopologicalData

/-- Tempered unitarity from discrete-series support. -/
theorem glTemperedUnitarity_of
    (hsupp : GLTemperedDiscreteSeriesSupportStatement.{uF, uV}) :
    GLTemperedUnitarityStatement.{uF, uV} := by
  intro p _ F T n hn V _ _ ρ hirr htemp
  obtain ⟨B, W, _, _, σ, hσirr, hσL2, j, hj⟩ := hsupp p F T n hn V ρ hirr htemp
  obtain ⟨hs, hu⟩ := T.leviSquareIntegrable_smooth_unitarizable B σ hσirr hσL2
  exact (T.isUnitarizable_normalizedOppositeParabolicInduced hn B σ hs hu).of_injective j hj

/-- Every irreducible analytically tempered GL_n representation admits an
invariant positive definite Hermitian form. -/
theorem glTemperedUnitarity : GLTemperedUnitarityStatement.{uF, uV} :=
  glTemperedUnitarity_of glTemperedDiscreteSeriesSupport.{uF, uV}

end Langlands

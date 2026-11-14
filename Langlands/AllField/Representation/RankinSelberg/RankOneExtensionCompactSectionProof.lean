import Langlands.Representation.RankinSelberg.RankOneExtensionCompactSectionProof
import Langlands.AllField.Group.GL.BlockIwahoriBasis
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionCompactSectionStatement
/-!
# Proof of the normalized compact sections for the strict rank-one extension

The section is the published double-coset section `P̄ · 1 · K` of the lower
induction, for a compact open subgroup `K` with block Iwahori factorization for the
lower shape, and value `vol(L)⁻¹ (w ⊗ 1)` at the identity, where `L = {y | u(y) ∈ K}`.
The test function is `vol(L)⁻¹ 1_L`. Since `P̄` meets the upper radical trivially,
the factorization `K = (K ∩ N̄) (K ∩ M) (K ∩ N)` identifies the section on the whole
upper cell and its support.
-/

noncomputable section

open MeasureTheory Topology

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneExtensionCompactSectionStatement RankOneExtensionLDivisibilityStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement exists_rankOneExtensionCellSection isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isSmooth_oppositeInducing normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneExtensionCompactSection rankOneExtensionLowerFamily rankOneExtensionLowerFamily_isSmooth rankOneExtensionLowerInduced rankOneExtensionLowerInducing_isSmooth rankOneExtensionLowerModel rankOneExtensionLowerSection rankOneExtensionLowerSectionCoefficient rankOneExtensionLowerSectionEval rankOneExtensionLowerToUpperEquiv rankOneExtensionWhittakerContraction rankOneWhittakerType
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV uW uX

section Cell



end Cell

section Smooth

variable {F : Type uF} [Field F]

/-- The inflated and twisted inducing representation of a smooth Levi representation
is smooth on the lower parabolic. -/
theorem isSmooth_oppositeInducing (T : LocalFieldData F) {n : ℕ} (B : BlockShape n)
    {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (σ : Representation ℂ (B.Levi F) X)
    (hσ : letI := T.topology; IsSmooth σ) :
    letI := T.topology
    IsSmooth (twist (T.oppositeParabolicHalfModulus B)
      (σ.comp (B.oppositeLeviProjection F))) := by
  let := T.topology
  exact (isSmooth_twist_iff _ _ (T.isOpen_ker_oppositeParabolicHalfModulus B)).2
    (isSmooth_comp _ (T.oppositeBlockLeviProjection B).continuous hσ)

end Smooth

section Construction

variable (F : Type uF) [Field F]

/-- The cell-section construction for an arbitrary smooth representation `ρ` of the
lower parabolic of the lower shape and an arbitrary vector `x₀`. -/
theorem exists_rankOneExtensionCellSection [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (t k : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ (Langlands.GeneralLinear ((1 + (t + 1)) + (k + 1)) F) V)
    (ρ : Representation ℂ ((rankOneExtensionLowerShape t).oppositeParabolic F) X)
    (v : V) (x₀ : X)
    (hπ : IsSmooth π)
    (hρ : IsSmooth ρ) :
    letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (1 + (t + 1))
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ O : Set (Fin (t + 1) → F), IsOpen O → (0 : Fin (t + 1) → F) ∈ O →
      ∃ (φ : SchwartzBruhat (Fin (t + 1) → F))
        (s : Induction.SmoothFunctions
          ((rankOneExtensionLowerShape t).oppositeParabolic F) ρ),
        Function.support φ ⊆ O ∧
        Integrable φ (rowMeasure ν.val (t + 1)) ∧
        ∫ y, φ y ∂rowMeasure ν.val (t + 1) = 1 ∧
        (∀ y : Fin (t + 1) → F,
          Induction.eval _ ρ s (rankOneExtensionUpperCell t y) = φ y • x₀) ∧
        (∀ g : Langlands.GeneralLinear (1 + (t + 1)) F,
          Induction.eval _ ρ s g ≠ 0 →
            ∃ q : (rankOneExtensionLowerShape t).oppositeParabolic F,
              ∃ y ∈ Function.support φ,
                g = (q : Langlands.GeneralLinear (1 + (t + 1)) F) *
                  rankOneExtensionUpperCell t y) ∧
        (∀ y ∈ Function.support φ,
          π (rankInclusion (k + 1) (rankOneExtensionUpperCell t y)) v = v) := by
  intro O hO hO0
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.generalLinearTopologicalGroup (1 + (t + 1))
  let := borel F
  have : BorelSpace F := ⟨rfl⟩
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  have := T.secondCountableTopology
  have := T.sigmaCompactSpace
  have : IsTopologicalRing F := inferInstance
  let B := rankOneExtensionLowerShape t
  let P := B.oppositeParabolic F
  let G := Langlands.GeneralLinear (1 + (t + 1)) F
  -- Open stabilizers of `v` and `x₀`.
  obtain ⟨Kπ, hKπ⟩ := hπ v
  obtain ⟨H, hH⟩ := hρ x₀
  obtain ⟨O', hO'open, hO'⟩ := isOpen_induced_iff.mp H.isOpen
  let U : Set G := O' ∩ (rankInclusion (k + 1)) ⁻¹' (Kπ : Set _) ∩
    rankOneExtensionCellCoordinate t ⁻¹' O
  have hU : U ∈ 𝓝 (1 : G) := by
    refine IsOpen.mem_nhds ?_ ?_
    · exact (hO'open.inter (Kπ.isOpen.preimage
        (rankInclusionContinuous (R := F) (n := 1 + (t + 1)) (k + 1)).continuous)).inter
        (hO.preimage (continuous_rankOneExtensionCellCoordinate t))
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · have h1 : (1 : P) ∈ (Subtype.val ⁻¹' O' : Set P) := by
          rw [hO']
          exact H.one_mem
        exact h1
      · change rankInclusion (k + 1) (1 : G) ∈ Kπ
        rw [map_one]
        exact Kπ.one_mem
      · change rankOneExtensionCellCoordinate t (1 : G) ∈ O
        have h1 : rankOneExtensionCellCoordinate t (1 : G) = 0 := by
          rw [← rankOneExtensionUpperCell_zero (t := t), rankOneExtensionCellCoordinate_upperCell]
        rw [h1]
        exact hO0
  -- A compact open subgroup with block Iwahori factorization inside `U`.
  obtain ⟨K, hKc, hKU, hKfac⟩ := (Langlands.AllField.GeneralLinear.BlockShape.exists_compactOpenSubgroup_hasBlockIwahoriFactorization B) T hU
  have hfac : ∀ g ∈ K, ∃ q ∈ P, ∃ n ∈ K, n ∈ B.unipotentSubgroup F ∧ g = q * n := by
    intro g hg
    obtain ⟨⟨l, m, n⟩, hlmn⟩ :=
      (Langlands.AllField.GeneralLinear.BlockShape.HasBlockIwahoriFactorization.bijective _ _ hKfac).2 ⟨g, hg⟩
    have he : l.val * m.val * n.val = g := congrArg Subtype.val hlmn
    exact ⟨l.val * m.val,
      P.mul_mem (B.oppositeUnipotentSubgroup_le_oppositeParabolic F l.property.2)
        (B.leviSubgroup_le_oppositeParabolic F m.property.2),
      n.val, n.property.1, n.property.2, he.symm⟩
  -- The normalized test function.
  let L : Set (Fin (t + 1) → F) := rankOneExtensionUpperCell t ⁻¹' (K : Set G)
  have hLopen : IsOpen L := K.isOpen.preimage (continuous_rankOneExtensionUpperCell t)
  have hLclosed : IsClosed L := K.isClosed.preimage (continuous_rankOneExtensionUpperCell t)
  have hL0 : (0 : Fin (t + 1) → F) ∈ L := by
    change rankOneExtensionUpperCell t 0 ∈ K
    rw [rankOneExtensionUpperCell_zero]
    exact K.one_mem
  have hLsub : L ⊆ rankOneExtensionCellCoordinate t '' (K : Set G) :=
    fun y hy => ⟨rankOneExtensionUpperCell t y, hy, rankOneExtensionCellCoordinate_upperCell t y⟩
  have hLcompact : IsCompact L :=
    (hKc.image (continuous_rankOneExtensionCellCoordinate t)).of_isClosed_subset hLclosed hLsub
  let μ := rowMeasure ν.val (t + 1)
  have hLmeas : MeasurableSet L := hLopen.measurableSet
  have hμpos : 0 < μ L := hLopen.measure_pos μ ⟨0, hL0⟩
  have hμfin : μ L < ⊤ := hLcompact.measure_lt_top
  have hreal : 0 < μ.real L := ENNReal.toReal_pos hμpos.ne' hμfin.ne
  let c : ℂ := ((μ.real L : ℝ) : ℂ)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (by exact_mod_cast hreal.ne')
  let φf : (Fin (t + 1) → F) → ℂ := L.indicator (fun _ => c)
  have hφlc : IsLocallyConstant φf :=
    (LocallyConstant.indicator (LocallyConstant.const _ c) ⟨hLclosed, hLopen⟩).isLocallyConstant
  have hφcs : HasCompactSupport φf :=
    HasCompactSupport.intro' hLcompact hLclosed (fun y hy => Set.indicator_of_notMem hy _)
  let φ : SchwartzBruhat (Fin (t + 1) → F) := ⟨φf, hφlc, hφcs⟩
  have hφL : ∀ y, y ∈ L → φ y = c := fun y hy => by
    change L.indicator (fun _ => c) y = c
    exact Set.indicator_of_mem hy _
  have hφnL : ∀ y, y ∉ L → φ y = 0 := fun y hy => by
    change L.indicator (fun _ => c) y = 0
    exact Set.indicator_of_notMem hy _
  have hsupp : Function.support φ = L := by
    ext y
    by_cases hy : y ∈ L
    · simp only [Function.mem_support, hφL y hy, hy, iff_true]
      exact hc
    · simp only [Function.mem_support, hφnL y hy, hy, ne_eq, not_true_eq_false]
  -- The double-coset section.
  have hx : c • x₀ ∈ fixedVectors ρ (Induction.conjOpenSubgroup P K 1).toSubgroup := by
    rintro ⟨q, hq⟩
    have hqK : (q : G) ∈ K := by
      simpa using Induction.mem_conjOpenSubgroup.mp hq
    have hqH : q ∈ H := by
      have h1 : q ∈ (Subtype.val ⁻¹' O' : Set P) := (hKU hqK).1.1
      rw [hO'] at h1
      exact h1
    change ρ q (c • x₀) = c • x₀
    rw [map_smul]
    exact congrArg (c • ·) (hH ⟨q, hqH⟩)
  let s := Induction.compactDoubleCosetSection P ρ K hKc 1 (c • x₀) hx
  have key : ∀ g : G, Induction.eval P ρ s.val g ≠ 0 →
      ∃ q ∈ P, ∃ n ∈ K, n ∈ B.unipotentSubgroup F ∧ g = q * n := by
    intro g hg
    have hmem : Induction.quotientMap P g ∈
        Induction.quotientSupport P (Induction.eval P ρ s.val) := ⟨g, hg, rfl⟩
    obtain ⟨k', hk', hkk⟩ :=
      Induction.compactDoubleCosetSection_support_subset P ρ K hKc 1 (c • x₀) hx hmem
    have hr : g * (1 * k')⁻¹ ∈ P := QuotientGroup.rightRel_apply.mp (Quotient.exact hkk)
    obtain ⟨q₀, hq₀, n, hnK, hnU, hk'eq⟩ := hfac k' hk'
    refine ⟨g * k'⁻¹ * q₀, P.mul_mem (by simpa using hr) hq₀, n, hnK, hnU, ?_⟩
    subst hk'eq
    group
  have hcell : ∀ y, y ∉ L → Induction.eval P ρ s.val (rankOneExtensionUpperCell t y) = 0 := by
    intro y hy
    by_contra hne
    obtain ⟨q, hq, n, hnK, hnU, he⟩ := key _ hne
    have hqU : q ∈ B.unipotentSubgroup F := by
      have : q = rankOneExtensionUpperCell t y * n⁻¹ := by
        rw [he]
        group
      rw [this]
      exact (B.unipotentSubgroup F).mul_mem
        (rankOneExtensionUpperCell_mem_unipotentSubgroup t y)
        ((B.unipotentSubgroup F).inv_mem hnU)
    have hq1 := B.eq_one_of_mem_oppositeParabolic_of_mem_unipotentSubgroup F hq hqU
    apply hy
    change rankOneExtensionUpperCell t y ∈ K
    rw [he, hq1, one_mul]
    exact hnK
  refine ⟨φ, s.val, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- support in `O`
    rw [hsupp]
    intro y hy
    have h := (hKU hy).2
    change rankOneExtensionCellCoordinate t (rankOneExtensionUpperCell t y) ∈ O at h
    rwa [rankOneExtensionCellCoordinate_upperCell] at h
  · -- integrability
    exact (integrableOn_const hμfin.ne).integrable_indicator hLmeas
  · -- integral one
    change ∫ y, L.indicator (fun _ => c) y ∂μ = 1
    rw [integral_indicator_const _ hLmeas, Complex.real_smul]
    exact mul_inv_cancel₀ (by exact_mod_cast hreal.ne')
  · -- restriction to the upper cell
    intro y
    by_cases hy : y ∈ L
    · have h := Induction.compactDoubleCosetSection_apply P ρ K hKc 1 (c • x₀) hx 1
        ⟨rankOneExtensionUpperCell t y, hy⟩
      simp only [OneMemClass.coe_one, one_mul, map_one] at h
      rw [hφL y hy]
      exact h
    · rw [hφnL y hy, zero_smul]
      exact hcell y hy
  · -- support in `P̄ · u(supp φ)`
    intro g hg
    obtain ⟨q, hq, n, hnK, hnU, he⟩ := key g hg
    have hn := eq_rankOneExtensionUpperCell_of_mem_unipotentSubgroup t hnU
    refine ⟨⟨q, hq⟩, rankOneExtensionCellCoordinate t n, ?_, ?_⟩
    · rw [hsupp]
      change rankOneExtensionUpperCell t (rankOneExtensionCellCoordinate t n) ∈ K
      rw [← hn]
      exact hnK
    · rw [he, ← hn]
  · -- `v` is fixed on the support
    intro y hy
    rw [hsupp] at hy
    exact hKπ ⟨_, (hKU hy).1.2⟩

end Construction

section Final

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] (t : ℕ)
  (χ : Quasicharacter F)
  (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)

/-- The two block factors `(σ, χ)` of the lower induction are smooth. -/
theorem rankOneExtensionLowerFamily_isSmooth
    (ψ : UnitaryAdditiveCharacter F)
    (hσ : IsSmooth σ) :
    ∀ i, IsSmooth (rankOneExtensionLowerFamily F t (rankOneExtensionCharacter.{uF, uW} F χ) σ i) := by
  intro i
  fin_cases i
  · exact hσ
  · exact rankOneExtensionCharacter_isSmooth F ψ χ

/-- The inducing representation of the lower induction of `(σ, χ)` is smooth. -/
theorem rankOneExtensionLowerInducing_isSmooth
    (ψ : UnitaryAdditiveCharacter F)
    (hσ : IsSmooth σ) :
    letI : ∀ i : Fin (rankOneExtensionLowerShape t).length,
        AddCommGroup (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
      Shahidi.pairCarrier.instAddCommGroup i.rev
    letI : ∀ i : Fin (rankOneExtensionLowerShape t).length,
        Module ℂ (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
      Shahidi.pairCarrier.instModule ℂ i.rev
    IsSmooth (twist (V := PiTensorProduct ℂ (rankOneExtensionLowerCarrier (W := W)))
      ((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (rankOneExtensionLowerShape t))
      (((rankOneExtensionLowerShape t).blockTensor
        (V := rankOneExtensionLowerCarrier (W := W))
        (rankOneExtensionLowerFamily F t (rankOneExtensionCharacter.{uF, uW} F χ) σ)).comp
        ((rankOneExtensionLowerShape t).oppositeLeviProjection F))) := by
  let : ∀ i : Fin (rankOneExtensionLowerShape t).length,
      AddCommGroup (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
    Shahidi.pairCarrier.instAddCommGroup i.rev
  let : ∀ i : Fin (rankOneExtensionLowerShape t).length,
      Module ℂ (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
    Shahidi.pairCarrier.instModule ℂ i.rev
  exact isSmooth_oppositeInducing (⟨⟩ : LocalFieldData F) (rankOneExtensionLowerShape t) _
    (FiniteTensor.isSmooth_external _ (rankOneExtensionLowerFamily_isSmooth F t χ σ ψ hσ))

end Final

/-- JPSS (1983), Lemma (5.5), formulas (5)–(7): normalized compact sections of the actual
lower induction of `(σ, χ)`. -/
theorem rankOneExtensionCompactSection :
    RankOneExtensionCompactSectionStatement.{uF, uV, uW} := by
  intro F _ _ _ _ ψ ν t k V _ _ W _ _ π σ χ v w hπ hσ O hO hO0
  obtain ⟨φ, s, h1, h2, h3, h4, h5, h6⟩ :=
    exists_rankOneExtensionCellSection F ψ ν t k π _ v
      (rankOneExtensionLowerPureTensor w (ULift.up 1)) hπ
      (rankOneExtensionLowerInducing_isSmooth F t χ σ ψ hσ) O hO hO0
  refine ⟨φ, (rankOneExtensionLowerModel F t χ σ).asModuleEquiv.symm s,
    h1, h2, h3, ?_, ?_, h6⟩
  · exact h4
  · exact h5

end Langlands.AllField.RankinSelberg

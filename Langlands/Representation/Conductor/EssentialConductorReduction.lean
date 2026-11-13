import Langlands.Representation.Conductor.EssentialUniquenessReduction
import Langlands.Representation.Conductor.EssentialDualSetup
import Langlands.Representation.Conductor.EssentialConductorAssembly
import Langlands.Representation.Conductor.EssentialScaledUniqueness
import Langlands.Representation.Conductor.JacquetRestrictionInvariance
import Langlands.Representation.Conductor.EssentialIntegralLastRowSupportProof
import Langlands.Representation.Conductor.ConductorMinimalityStatement
import Langlands.Representation.Conductor.EssentialDualComparisonStatement
import Langlands.Representation.Conductor.TrivialCharacterEpsilonStatement
import Langlands.Representation.Whittaker.MirabolicRestrictionInjectivityStatement
import Langlands.Representation.Conductor.RankOneTateReduction
import Langlands.Representation.GodementJacquet.LocalTateConductorProof
import Langlands.Representation.RankinSelberg.UnipotentQuotient

/-!
# The essential-vector and conductor theorems from their inputs

JPSS 1981, Theorem (5.1), and Jacquet 2012, Theorem 1, assembled from the existence of
essential vectors and four published statements: mirabolic restriction injectivity,
the JPSS (5.3) dual comparison, the JPSS 1981 minimality and scaled identity, and the
existence of the epsilon factor against the trivial character of `GL_1`. The integral
last-row support of the essential vector and the rank-one case are published theorems.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial
open Langlands.GeneralLinear.Iwasawa

universe uF uV

/-- The existence half of `EssentialVectorStatement`: under Jacquet's normalizations,
every nonzero Whittaker model of an irreducible admissible generic representation of
`GL_(n+2)(F)` contains an essential vector. -/
def EssentialVectorExistence : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
    [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (ϖ : Fˣ)
    (μ : Measure (LeftUnipotentQuotient n F)) (h : IsJacquetNormalization q ψ abv ϖ μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V),
    IsGeneric ψ (n + 1) π →
    ∀ ℓ : glFunctionals ψ (n + 1) π, ℓ.val ≠ 0 →
      ∃ w : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ w

/-- **Jacquet 2012, Theorem 1 with uniqueness**, from existence and mirabolic restriction
injectivity. -/
theorem essentialVectorStatement_of_existence (hex : EssentialVectorExistence.{uF, uV})
    (hmir : MirabolicRestrictionInjectivityStatement.{uF, uV}) :
    EssentialVectorStatement.{uF, uV} := by
  intro F _ _ _ _ n _ _ _ _ _ _ _ _ q ψ abv ϖ μ h V _ _ π hπ ℓ hℓ
  exact existsUnique_isEssentialVector_of_exists h π ℓ hπ.2.1.1
    (hmir F (n + 1) ψ π hπ ℓ hℓ) (hex F n q ψ abv ϖ μ h π hπ ℓ hℓ)

section Jacquet

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ} {ϖ : Fˣ}
  {μ : Measure (LeftUnipotentQuotient n F)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- An essential vector of a generic representation is fixed by the integral Jacquet
mirabolic `H(0)`, given mirabolic restriction injectivity: its restriction to
`diag(GL_(n+1), 1)` is right `GL_(n+1)(O)`-invariant and supported on integral last
rows (the published `essentialIntegralLastRowSupport`). -/
theorem IsEssentialVector.mem_jacquetFixedVectors (h : IsJacquetNormalization q ψ abv ϖ μ)
    (hmir : MirabolicRestrictionInjectivityStatement.{uF, uV})
    (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
    (hπ : IsGeneric ψ (n + 1) π) (ℓ : glFunctionals ψ (n + 1) π) (hℓ : ℓ.val ≠ 0)
    {w : (coefficientModel π ℓ).toSubmodule} (hw : IsEssentialVector h π ℓ w) :
    w ∈ fixedVectors (modelRepresentation π ℓ)
      (fieldJacquetMirabolic (ValuativeRel.valuation F).integer (n + 1)) :=
  mem_jacquetFixedVectors_of_integral_restriction ψ π ℓ h.conductor.1
    (modelMirabolicRestriction_injective_of_carrier ψ π ℓ (hmir F (n + 1) ψ π hπ ℓ hℓ)) w
    hw.2 (essentialIntegralLastRowSupport F n q ψ abv ϖ μ h π hπ ℓ hℓ w hw)

/-- The same invariance, as right invariance of the Whittaker function. -/
theorem IsEssentialVector.right_jacquet_invariant (h : IsJacquetNormalization q ψ abv ϖ μ)
    (hmir : MirabolicRestrictionInjectivityStatement.{uF, uV})
    (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
    (hπ : IsGeneric ψ (n + 1) π) (ℓ : glFunctionals ψ (n + 1) π) (hℓ : ℓ.val ≠ 0)
    {w : (coefficientModel π ℓ).toSubmodule} (hw : IsEssentialVector h π ℓ w) :
    ∀ k ∈ fieldJacquetMirabolic (ValuativeRel.valuation F).integer (n + 1),
      ∀ g, w.val.val (g * k) = w.val.val g := by
  intro k hk g
  have hfix := IsEssentialVector.mem_jacquetFixedVectors h hmir π hπ ℓ hℓ hw ⟨k, hk⟩
  exact congrArg (fun z : (coefficientModel π ℓ).toSubmodule => z.val.val g) hfix

end Jacquet

/-- **JPSS 1981, Theorem (5.1)(ii), first clause**, from existence, mirabolic restriction
injectivity and the JPSS (5.3) dual comparison: the essential vector is fixed at the
level of the epsilon exponent. -/
theorem essentialVectorLevelStatement_of (hex : EssentialVectorExistence.{uF, uV})
    (hmir : MirabolicRestrictionInjectivityStatement.{uF, uV})
    (hdual : EssentialDualComparisonStatement.{uF, uV}) :
    EssentialVectorLevelStatement.{uF, uV} := by
  intro F _ _ _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ q ψ abv ϖ μ h ν hν V _ _ π hπ ℓ hℓ w hw c m hε
  have h' := h.scaleNegOne
  have hπ' := isGeneric_inverseTransposePullback ψ π hπ
  have hℓ' := scaledDualFunctional_ne_zero ψ π ℓ hℓ
  obtain ⟨w', hw'⟩ := hex F n q (ψ.scale (-1)) abv ϖ μ h' (inverseTransposePullback π) hπ'
    (scaledDualFunctional ψ π ℓ) hℓ'
  obtain ⟨C, hC⟩ := hdual F n q ψ abv ϖ μ h h' ν hν π hπ ℓ hℓ w hw
    (scaledDualFunctional ψ π ℓ) rfl w' hw' c m hε
  exact mem_levelFixedVectors_of_rankInclusion_dual_comparison ϖ h.uniformizer m ψ π ℓ w
    w'.val.val C hC (IsEssentialVector.mem_jacquetFixedVectors h hmir π hπ ℓ hℓ hw)
    (IsEssentialVector.right_jacquet_invariant h' hmir _ hπ' _ hℓ' hw')

/-- **JPSS 1981, Theorem (5.1)(i)-(iii)**, from existence, mirabolic restriction
injectivity, the JPSS (5.3) dual comparison, the JPSS 1981 minimality and scaled
identity, and the existence of the epsilon factor. Rank one is the published Tate case;
in rank `n + 2` the epsilon exponent `m` is nonnegative by the dual comparison, the
essential vector is fixed at level `m`, and minimality makes level `m` the line of the
essential vector with no lower nonzero fixed vectors. -/
theorem conductorExponentStatement_of (hex : EssentialVectorExistence.{uF, uV})
    (hmir : MirabolicRestrictionInjectivityStatement.{uF, uV})
    (hdual : EssentialDualComparisonStatement.{uF, uV})
    (hmin : ConductorMinimalityStatement.{uF, uV})
    (heps : TrivialCharacterEpsilonStatement.{uF, uV}) :
    ConductorExponentStatement.{uF, uV} := by
  intro F _ _ _ _ _ _ _ _ _ _ _ _ _ _ q hq abv ϖ hϖ habvϖ habvunit ψ hψ ν hν n V _ _ π hπ
  cases n with
  | zero =>
    exact conductorExponent_rankOne_of_localTate F q hq abv ϖ hϖ habvϖ habvunit ψ hψ ν hν
      GodementJacquet.localTateConductor π hπ
  | succ k =>
    let : MeasurableSpace (Langlands.GeneralLinear (k + 1) F) := borel _
    have : BorelSpace (Langlands.GeneralLinear (k + 1) F) := ⟨rfl⟩
    let : MeasurableSpace (upperUnipotent (k + 1) F) := borel _
    have : BorelSpace (upperUnipotent (k + 1) F) := ⟨rfl⟩
    let : MeasurableSpace (LeftUnipotentQuotient k F) := borel _
    have hborel : BorelSpace (LeftUnipotentQuotient k F) := ⟨rfl⟩
    have h : IsJacquetNormalization q ψ abv ϖ (unipotentQuotientHaar F k) :=
      { residueCardinality := hq
        uniformizer := hϖ
        abv_uniformizer := habvϖ
        abv_unit := habvunit
        conductor := hψ
        measure := unipotentQuotientHaar_isCompatible F k
        borel := hborel
        borel_rankOne := inferInstance }
    obtain ⟨⟨c, m⟩, hε⟩ := heps F q hq abv ϖ hϖ habvϖ habvunit ψ hψ ν hν (k + 1) π hπ
    obtain ⟨ℓ, hℓ⟩ := hπ.2.2
    obtain ⟨w, hw⟩ := hex F k q ψ abv ϖ _ h π hπ ℓ hℓ
    have huniq : ∀ u : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ u → u = w :=
      fun u hu => IsEssentialVector.eq_of_mirabolicRestrictionInjective h π ℓ hπ.2.1.1
        (hmir F (k + 1) ψ π hπ ℓ hℓ) hu hw
    -- the dual essential vector and the dual comparison with the integer exponent `m`
    have h' := h.scaleNegOne
    have hπ' := isGeneric_inverseTransposePullback ψ π hπ
    have hℓ' := scaledDualFunctional_ne_zero ψ π ℓ hℓ
    obtain ⟨w', hw'⟩ := hex F k q (ψ.scale (-1)) abv ϖ _ h' (inverseTransposePullback π) hπ'
      (scaledDualFunctional ψ π ℓ) hℓ'
    obtain ⟨C, hC⟩ := hdual F k q ψ abv ϖ _ h h' ν hν π hπ ℓ hℓ w hw
      (scaledDualFunctional ψ π ℓ) rfl w' hw' c m hε
    have hw0 : w.val ≠ 0 := by
      intro hz
      exact IsEssentialVector.ne_zero h π ℓ hw (Subtype.ext hz)
    obtain ⟨hm0, -⟩ := right_level_toNat_invariant_of_dual_comparison ψ (Nat.succ_pos k)
      ϖ hϖ m w.val hw0 _ C
      (hasJacquetDualComparison_of_rankInclusion_scalar ϖ m w.val.val w'.val.val C hC)
      (IsEssentialVector.right_jacquet_invariant h hmir π hπ ℓ hℓ hw)
      (right_invariant_central_translate _ _ w'.val.val
        (IsEssentialVector.right_jacquet_invariant h' hmir _ hπ' _ hℓ' hw'))
    obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hm0
    have hlev := essentialVectorLevelStatement_of hex hmir hdual F k q ψ abv ϖ _ h ν hν
      π hπ ℓ hℓ w hw c a hε
    obtain ⟨P, hP, -⟩ := hw.1
    have hminw := hmin F k q ψ abv ϖ _ h ν hν π hπ ℓ hℓ P hP c a hε
    have hL : IsLevelLine (modelRepresentation π ℓ) a w := by
      refine ⟨hlev, fun b hb v hv => ?_, ?_⟩
      · by_contra hv0
        have hle := (hminw b v hv).1 hv0
        omega
      · exact exists_eq_smul_of_mem_levelFixedVectors h hw huniq hP
          (fun v hv => (hminw a v hv).2 rfl)
    exact ⟨c, a, hε, isNewvectorConductor_and_finrank_of_essential h π hπ ℓ hℓ w hw a hL⟩

/-- **The corrected essential-vector and JPSS conductor theorems**, from the existence of
essential vectors and the four published statements on mirabolic restriction
injectivity, the dual comparison, minimality and the epsilon factor. -/
theorem essentialConductorStatement_of (hex : EssentialVectorExistence.{uF, uV})
    (hmir : MirabolicRestrictionInjectivityStatement.{uF, uV})
    (hdual : EssentialDualComparisonStatement.{uF, uV})
    (hmin : ConductorMinimalityStatement.{uF, uV})
    (heps : TrivialCharacterEpsilonStatement.{uF, uV}) :
    EssentialConductorStatement.{uF, uV} :=
  ⟨essentialVectorStatement_of_existence hex hmir,
    conductorExponentStatement_of hex hmir hdual hmin heps,
    essentialVectorLevelStatement_of hex hmir hdual⟩

end Langlands.Conductor

import Langlands.Representation.Conductor.SupercuspidalPadicConductorExponentStatement
import Langlands.Representation.Conductor.SupercuspidalPadicEssentialExistence
import Langlands.Representation.Conductor.EssentialConductorReduction
import Langlands.Representation.Conductor.EssentialDualComparisonProof
import Langlands.Representation.Conductor.ConductorMinimalityProof
import Langlands.Representation.Conductor.TrivialCharacterEpsilonProof
import Langlands.Representation.Whittaker.MirabolicRestrictionInjectivityProof

/-!
# Proof of the JPSS conductor theorem for supercuspidal representations of p-adic fields

JPSS 1981, Theorem (5.1)(i)-(iii), for supercuspidal representations of `GL_(n+1)(K)`
with `K` a p-adic field. Rank one is the published Tate case. In rank `n + 2` the
essential vectors of `π` and of its inverse-transpose dual are the Kirillov lifts of the
zero-cell Whittaker functions (`SupercuspidalPadic.exists_isEssentialVector`), and the
argument of `Conductor.conductorExponentStatement_of` applies with the published
mirabolic restriction injectivity, dual comparison, minimality and epsilon existence.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial
open Langlands.GeneralLinear.Iwasawa

universe uF uV

/-- **JPSS 1981, Theorem (5.1)(i)-(iii), for supercuspidal representations of p-adic
fields.** The epsilon factor of `π` against the trivial character of `GL_1` is
`c q^(-ms)` with `m` a natural number, the level-`m` fixed vectors form a line, and no
lower level fixes a nonzero vector. -/
theorem supercuspidalPadicConductorExponent :
    SupercuspidalPadicConductorExponentStatement.{uF, uV} := by
  intro p _ K
  let := K.canonicalTopologicalData.topology
  let := K.canonicalTopologicalData.valuativeRel
  let := K.canonicalTopologicalData.localField
  intro _ _ _ _ _ _ _ _ _ _ q hq abv ϖ hϖ habvϖ habvunit ψ hψ ν hν n V _ _ π hπ
    hsc
  have hmir := Langlands.Whittaker.mirabolicRestrictionInjectivity.{uF, uV}
  have hdual := essentialDualComparison.{uF, uV}
  have hmin := conductorMinimalityStatement.{uF, uV}
  have heps := trivialCharacterEpsilon.{uF, uV}
  cases n with
  | zero =>
    exact conductorExponent_rankOne_of_localTate K.Carrier q hq abv ϖ hϖ habvϖ habvunit ψ hψ
      ν hν GodementJacquet.localTateConductor π hπ
  | succ k =>
    let : MeasurableSpace (Langlands.GeneralLinear (k + 1) K.Carrier) := borel _
    have : BorelSpace (Langlands.GeneralLinear (k + 1) K.Carrier) := ⟨rfl⟩
    let : MeasurableSpace (upperUnipotent (k + 1) K.Carrier) := borel _
    have : BorelSpace (upperUnipotent (k + 1) K.Carrier) := ⟨rfl⟩
    let : MeasurableSpace (LeftUnipotentQuotient k K.Carrier) := borel _
    have hborel : BorelSpace (LeftUnipotentQuotient k K.Carrier) := ⟨rfl⟩
    have h : IsJacquetNormalization q ψ abv ϖ (unipotentQuotientHaar K.Carrier k) :=
      { residueCardinality := hq
        uniformizer := hϖ
        abv_uniformizer := habvϖ
        abv_unit := habvunit
        conductor := hψ
        measure := unipotentQuotientHaar_isCompatible K.Carrier k
        borel := hborel
        borel_rankOne := inferInstance }
    obtain ⟨⟨c, m⟩, hε⟩ := heps K.Carrier q hq abv ϖ hϖ habvϖ habvunit ψ hψ ν hν (k + 1) π hπ
    obtain ⟨ℓ, hℓ⟩ := hπ.2.2
    obtain ⟨w, hw⟩ := SupercuspidalPadic.exists_isEssentialVector K h π hπ hsc ℓ hℓ
    have huniq : ∀ u : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ u → u = w :=
      fun u hu => IsEssentialVector.eq_of_mirabolicRestrictionInjective h π ℓ hπ.2.1.1
        (hmir K.Carrier (k + 1) ψ π hπ ℓ hℓ) hu hw
    -- the dual essential vector and the dual comparison with the integer exponent `m`
    have h' := h.scaleNegOne
    have hπ' := isGeneric_inverseTransposePullback ψ π hπ
    have hsc' : IsSupercuspidal (inverseTransposePullback π) :=
      isSupercuspidal_comp_inverseTranspose π hsc
    have hℓ' := scaledDualFunctional_ne_zero ψ π ℓ hℓ
    obtain ⟨w', hw'⟩ := SupercuspidalPadic.exists_isEssentialVector K h'
      (inverseTransposePullback π) hπ' hsc' (scaledDualFunctional ψ π ℓ) hℓ'
    obtain ⟨C, hC⟩ := hdual K.Carrier k q ψ abv ϖ _ h h' ν hν π hπ ℓ hℓ w hw
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
    -- the essential vector is fixed at level `a` (JPSS 1981, Theorem (5.1)(ii))
    have hlev : w ∈ levelFixedVectors (modelRepresentation π ℓ) a :=
      mem_levelFixedVectors_of_rankInclusion_dual_comparison ϖ h.uniformizer a ψ π ℓ w
        w'.val.val C hC (IsEssentialVector.mem_jacquetFixedVectors h hmir π hπ ℓ hℓ hw)
        (IsEssentialVector.right_jacquet_invariant h' hmir _ hπ' _ hℓ' hw')
    obtain ⟨P, hP, -⟩ := hw.1
    have hminw := hmin K.Carrier k q ψ abv ϖ _ h ν hν π hπ ℓ hℓ P hP c a hε
    have hL : IsLevelLine (modelRepresentation π ℓ) a w := by
      refine ⟨hlev, fun b hb v hv => ?_, ?_⟩
      · by_contra hv0
        have hle := (hminw b v hv).1 hv0
        omega
      · exact exists_eq_smul_of_mem_levelFixedVectors h hw huniq hP
          (fun v hv => (hminw a v hv).2 rfl)
    exact ⟨c, a, hε, isNewvectorConductor_and_finrank_of_essential h π hπ ℓ hℓ w hw a hL⟩

end Langlands.Conductor

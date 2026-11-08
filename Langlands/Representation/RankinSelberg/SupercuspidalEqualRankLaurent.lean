import Langlands.Representation.RankinSelberg.EqualRankCompactLaurent
import Langlands.Representation.RankinSelberg.EqualRankVectorContinuation
import Langlands.Representation.Whittaker.KirillovStatement
import Langlands.Representation.Whittaker.PrerequisiteInterfaces
import Langlands.Representation.Conductor.Congruence

/-! # Supercuspidal coefficient regularity and the central denominator bound -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance supercuspidalEqualRankLaurentTopologicalSpace : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance supercuspidalEqualRankLaurentValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance supercuspidalEqualRankLaurentIsNonarchimedeanLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance supercuspidalEqualRankLaurentT2Space : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
  {ψ : UnitaryAdditiveCharacter F.Carrier} {ℓ : glFunctionals ψ n π}

/-- The support part of the full Kirillov statement applies to every right
translate of an actual supercuspidal coefficient. -/
theorem hasMirabolicCompactTranslates_of_supercuspidalKirillov
    (hK : SupercuspidalKirillovStatement.{uF,uV})
    (hπ : IsSupercuspidal π) (hiπ : π.IsIrreducible) (hℓ : ℓ.val ≠ 0) (v : V) :
    HasMirabolicCompactTranslates (fun g => ℓ.val (π g v)) := by
  have hψ : ψ.complex ≠ 1 := by
    intro h
    apply ψ.nontrivial
    ext x
    exact congrArg (fun χ : AddChar F.Carrier ℂ => χ x) h
  have hk := (hK p inferInstance F n V π ψ.complex ψ.continuous_complex hψ
    ψ.norm_complex hπ hiπ).2 ℓ.val hℓ (by
      intro g hg v
      exact (mem_glFunctionals_iff_entrywise ψ π ℓ.val).mp ℓ.property
        g (fun _ _ hij => hg.1 _ _ hij) hg.2 v)
  intro a
  obtain ⟨C, hC, hs⟩ := (hk.1 (π a v)).2.2
  refine ⟨C, hC, ?_⟩
  intro q hq
  have hq' : ℓ.val (π q.val (π a v)) ≠ 0 := by
    simpa only [map_mul, Module.End.mul_apply] using hq
  obtain ⟨u, c, hu, hc, he⟩ := hs q.val q.property hq'
  exact ⟨⟨u, ⟨fun _ _ hij => hu.1 _ _ hij, hu.2⟩⟩, c, hc, he⟩

/-- A chosen smooth vector stabilizer intersected with the compact
level-zero subgroup of the actual general linear group. -/
def compactCoefficientStabilizer (hπ : IsSmooth π) (v : V) :
    OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  (hπ v).choose ⊓ Conductor.levelOpenSubgroup F.Carrier n 0

/-- Intersecting a vector stabilizer with the level-zero subgroup gives a
compact open subgroup fixing its entire coefficient on the right. -/
theorem exists_compact_open_coefficient_stabilizer
    (hπ : IsSmooth π) (v : V) :
    ∃ J : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier),
      IsCompact (J : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∧
      ∀ g, ∀ j : J, ℓ.val (π (g * j.val) v) = ℓ.val (π g v) := by
  let J := compactCoefficientStabilizer hπ v
  have hK := (hπ v).choose_spec
  refine ⟨J, ?_, ?_⟩
  · exact (Conductor.isCompact_levelOpenSubgroup F.Carrier n 0).of_isClosed_subset
      J.isClosed (fun _ h => h.2)
  · intro g j
    rw [map_mul, Module.End.mul_apply, show π j.val v = v from hK ⟨j.val, j.property.1⟩]

local instance quotientMeasurable : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) :=
  borel _
local instance quotientBorel : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
  {ℓ' : glInverseFunctionals ψ n σ}
  {μ : Measure (LeftUnipotentQuotient n F.Carrier)}

/-- Under the full Kirillov theorem, every actual vector continuation with a
row test vanishing at zero belongs to the Laurent subring. -/
theorem equalRankVectorContinuation_laurent_of_supercuspidalKirillov
    (hK : SupercuspidalKirillovStatement.{uF,uV})
    (hπ : IsSupercuspidal π) (hiπ : π.IsIrreducible) (hℓ : ℓ.val ≠ 0)
    (hA : EqualRankAnalyticConclusion F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μ π σ ℓ ℓ')
    (v : V) (w : W) (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (hΦ : Φ 0 = 0) :
    ∃ L : LaurentCoefficients, laurentToRatFunc L =
      equalRankVectorContinuation F.canonicalTopologicalData.residueCardinality_gt_one hA v w Φ := by
  have hmir := hasMirabolicCompactTranslates_of_supercuspidalKirillov hK hπ hiπ hℓ v
  obtain ⟨J, hJ, hfix⟩ := exists_compact_open_coefficient_stabilizer (ℓ := ℓ) hπ.1.1 v
  exact HasMirabolicCompactTranslates.exists_laurent_equalRankContinuation
    F.canonicalTopologicalData μ ψ (modelMap π ℓ v).val hmir J hJ hfix
    (modelMap σ ℓ' w).val Φ hΦ (hA.1 _ _ Φ)
    _ (equalRankContinuationFamily_spec F.canonicalTopologicalData.residueCardinality_gt_one
      hA (modelMap π ℓ v) (modelMap σ ℓ' w) Φ)

/-- Combining actual supercuspidal regularity with the inverse-uniformizer
recurrence bounds the normalized denominator by a squarefree binomial. -/
theorem equalRank_normalizedGenerator_bound_of_supercuspidalKirillov
    (hK : SupercuspidalKirillovStatement.{uF,uV})
    (hπ : IsSupercuspidal π) (hiπ : π.IsIrreducible) (hℓ : ℓ.val ≠ 0)
    (hσ : IsAdmissible σ) (hiσ : σ.IsIrreducible)
    (hA : EqualRankAnalyticConclusion F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μ π σ ℓ ℓ')
    (hμ : ∀ g, MeasurePreserving
      (rightTranslate (upperUnipotent (n + 1) F.Carrier) g) μ μ)
    {P : Polynomial ℂ}
    (hP : IsNormalizedGenerator (equalRankRationalValues
      F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μ π σ ℓ ℓ') P) :
    ∃ c : ℂ, c ≠ 0 ∧ P ∣ Polynomial.X ^ (n + 1) - Polynomial.C c ∧
      P.Separable ∧ Squarefree P := by
  obtain ⟨c, hc, hshift⟩ := equalRankVectorContinuation_inverseUniformizer
    F.canonicalTopologicalData n hA hμ hπ.1 hiπ hσ hiσ
  refine ⟨c, hc, ?_⟩
  exact CentralShiftLaw.normalizedGenerator_bound hP
    (equalRankVectorContinuation F.canonicalTopologicalData.residueCardinality_gt_one hA)
    (fun R hR => (mem_equalRankRationalValues_iff_vector
      F.canonicalTopologicalData.residueCardinality_gt_one hA R).mp hR)
    _ c hc (n + 1) (Nat.succ_ne_zero n) hshift rowEvaluationAtZero
    (fun Φ => rowEvaluationAtZero_translate _ Φ)
    (fun v w Φ hΦ => equalRankVectorContinuation_laurent_of_supercuspidalKirillov
      hK hπ hiπ hℓ hA v w Φ hΦ)

end Langlands.RankinSelberg

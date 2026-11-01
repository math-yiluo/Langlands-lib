import Langlands.Representation.RankinSelberg.TwoBlockDominantJacquetSeries
import Langlands.Representation.RankinSelberg.TwoBlockDualSectionJacquetProof
import Langlands.Representation.RankinSelberg.DualWhittakerType

/-!
# Actual reversed-dual Jacquet coefficient realization

Internal assembly of the published reversed-dual section equivalence and
ordinary Jacquet coefficient realization. No block functional equation is asserted.
-/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

section Transport

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {U : Type uW} [AddCommGroup U] [Module ℂ U] {n : ℕ}
  (ψ : UnitaryAdditiveCharacter K)
  (ρ : Representation ℂ (GeneralLinear (n + 1) K) V)
  {ρD : Representation ℂ (GeneralLinear (n + 1) K) U}
  (E : Representation.Equiv (inverseTransposePullback ρ) ρD)

/-- The Weyl-translated inverse functional transported through an actual
inverse-transpose representation equivalence. -/
def transportedSecondDualFunctional (J : glInverseFunctionals ψ n ρ) :
    glInverseFunctionals (ψ.scale (-1)) n ρD :=
  Whittaker.functionalsCongr E (secondDualFunctional ψ ρ J)

/-- Transport preserves the actual second-dual coefficient function. -/
theorem transportedSecondDualFunctional_coefficient
    (J : glInverseFunctionals ψ n ρ) (v : V) :
    (modelMap ρD (transportedSecondDualFunctional ψ ρ E J) (E v)).val =
      secondDualFunction ψ n (modelMap ρ J v).val := by
  change coefficientMap ρD (transportedSecondDualFunctional ψ ρ E J) (E v) =
    secondDualFunction ψ n (coefficientMap ρ J v)
  rw [secondDualFunction_coefficient]
  apply Subtype.ext
  funext g
  change (transportedSecondDualFunctional ψ ρ E J).val (ρD g (E v)) =
    (secondDualFunctional ψ ρ J).val (inverseTransposePullback ρ g v)
  simp only [transportedSecondDualFunctional, Whittaker.functionalsCongr_apply]
  apply congrArg (secondDualFunctional ψ ρ J).val
  calc
    E.symm (ρD g (E v)) =
        inverseTransposePullback ρ g (E.symm (E v)) :=
      Representation.IntertwiningMap.isIntertwining _ _ E.symm.toIntertwiningMap g (E v)
    _ = inverseTransposePullback ρ g v :=
      congrArg (inverseTransposePullback ρ g) (E.symm_apply_apply v)

/-- A nonzero reference functional remains nonzero after dualization and
transport through the actual equivalence. -/
theorem transportedSecondDualFunctional_ne_zero
    {J : glInverseFunctionals ψ n ρ} (hJ : J.val ≠ 0) :
    (transportedSecondDualFunctional ψ ρ E J).val ≠ 0 := by
  intro hz
  apply secondDualFunctional_ne_zero ψ ρ hJ
  ext v
  have hv := LinearMap.congr_fun hz (E v)
  simpa only [transportedSecondDualFunctional, Whittaker.functionalsCongr_apply,
    E.symm_apply_apply, LinearMap.zero_apply] using hv

end Transport

section ActualJacquet

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))

local instance dualJacquetTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance dualJacquetValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance dualJacquetLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance dualJacquetSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance dualJacquetMeasurable : MeasurableSpace F.Carrier := borel F.Carrier
local instance dualJacquetBorel : BorelSpace F.Carrier := ⟨rfl⟩

/-- Full type of every reversed inverse-transpose block at the negated
character. The entire dependent block family is reversed. -/
theorem reversedDualBlocks_whittakerType
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) :
    ∀ i : Fin 2, IsOfWhittakerType (m i.rev)
      (standardCharacter (ψ.scale (-1)) (m i.rev))
      (inverseTransposePullback (σ i.rev)) := by
  intro i
  simpa only [standardCharacter_scale_neg_one] using
    isOfWhittakerType_inverseTransposePullback ψ (σ i.rev) (hσ i.rev)

set_option maxHeartbeats 1600000 in
/-- One actual section equivalence, chosen before the additive character,
block functionals, additive Haar measure and induced functional, identifies
the transported dual coefficient with the ordinary reversed-dual Jacquet
function and its actual unfolded slice series. -/
theorem exists_reversedDualJacquetRealization
    (hσ : ∀ i, IsSmooth (σ i)) :
    let mD : Fin 2 → ℕ := fun i => m i.rev
    let hD : ∑ i, (mD i + 1) = t + 1 :=
      (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h
    let WD : Fin 2 → Type uW := fun i => W i.rev
    letI : ∀ i, AddCommGroup (WD i) := fun i => hadd i.rev
    letI : ∀ i, Module ℂ (WD i) := fun i => hmod i.rev
    let σD : ∀ i, Representation ℂ (GeneralLinear (mD i + 1) F.Carrier) (WD i) :=
      fun i => inverseTransposePullback (σ i.rev)
    ∃ E : Representation.Equiv
        (inverseTransposePullback (TwoBlockJacquet.inducedRep F h σ))
        (TwoBlockJacquet.inducedRep F hD σD),
      ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
        (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
        (ν : AdditiveHaarMeasure F.Carrier)
        (J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ)),
        let ψD := ψ.scale (-1)
        let ellD : ∀ i, glInverseFunctionals ψD (mD i) (σD i) :=
          fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev)
        let μR := rectangularMeasure ν (m 0 + 1) (m 1 + 1)
        let μD := rectangularMeasure ν (m 1 + 1) (m 0 + 1)
        let JD := transportedSecondDualFunctional ψ (TwoBlockJacquet.inducedRep F h σ) E J
        (∀ (f : TwoBlockJacquet.Sections F h σ)
          (g : GeneralLinear (t + 1) F.Carrier),
          J.val (TwoBlockJacquet.inducedRep F h σ g f) =
            TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val) μR f g) →
        (∀ fD : TwoBlockJacquet.Sections F hD σD,
          (modelMap (TwoBlockJacquet.inducedRep F hD σD) JD fD).val =
            secondDualFunction ψ t
              (modelMap (TwoBlockJacquet.inducedRep F h σ) J (E.symm fD)).val) ∧
        (∀ (fD : TwoBlockJacquet.Sections F hD σD)
          (g : GeneralLinear (t + 1) F.Carrier),
          JD.val (TwoBlockJacquet.inducedRep F hD σD g fD) =
            TwoBlockJacquet.jacquetFunction ψD (fun i => (ellD i).val) μD fD g) ∧
        (J.val ≠ 0 → JD.val ≠ 0) ∧
        (∀ fD : TwoBlockJacquet.Sections F hD σD,
          TwoBlockJacquet.IsAbsIntegrable ψD (fun i => (ellD i).val) μD fD ↔
            TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ell i).val) μR (E.symm fD)) ∧
        ∀ (μN : letI := borel (LeftUnipotentQuotient t F.Carrier);
          Measure (LeftUnipotentQuotient t F.Carrier))
          (fD : TwoBlockJacquet.Sections F hD σD)
          (Wtest : WhittakerFunctions ψD t)
          (Φ : SchwartzBruhat (Fin (t + 1) → F.Carrier)),
          unfoldedJacquetSeries F hD ψD σD ellD μD μN fD Wtest Φ =
            equalRankSliceCoefficient F.canonicalTopologicalData μN ψD Wtest
              (secondDualFunction ψ t
                (modelMap (TwoBlockJacquet.inducedRep F h σ) J (E.symm fD)).val) Φ := by
  dsimp only
  obtain ⟨E, -, -, hE⟩ := twoBlockDualSectionJacquet p F t m h W σ hσ
  refine ⟨E, ?_⟩
  intro ψ ell ν J hJ
  let mD : Fin 2 → ℕ := fun i => m i.rev
  let hD : ∑ i, (mD i + 1) = t + 1 :=
    (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h
  let WD : Fin 2 → Type uW := fun i => W i.rev
  let : ∀ i, AddCommGroup (WD i) := fun i => hadd i.rev
  let : ∀ i, Module ℂ (WD i) := fun i => hmod i.rev
  let σD : ∀ i, Representation ℂ (GeneralLinear (mD i + 1) F.Carrier) (WD i) :=
    fun i => inverseTransposePullback (σ i.rev)
  let ψD := ψ.scale (-1)
  let ellD : ∀ i, glInverseFunctionals ψD (mD i) (σD i) :=
    fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev)
  let μR := rectangularMeasure ν (m 0 + 1) (m 1 + 1)
  let μD := rectangularMeasure ν (m 1 + 1) (m 0 + 1)
  let JD := transportedSecondDualFunctional ψ (TwoBlockJacquet.inducedRep F h σ) E J
  obtain ⟨-, -, hν⟩ := hE ψ ell
  obtain ⟨-, -, -, -, habs, hjac⟩ := hν ν
  have hcoeff (fD : TwoBlockJacquet.Sections F hD σD) :
      (modelMap (TwoBlockJacquet.inducedRep F hD σD) JD fD).val =
        secondDualFunction ψ t
          (modelMap (TwoBlockJacquet.inducedRep F h σ) J (E.symm fD)).val := by
    have hh := transportedSecondDualFunctional_coefficient ψ
      (TwoBlockJacquet.inducedRep F h σ) E J (E.symm fD)
    simpa only [E.apply_symm_apply] using hh
  have hJD (fD : TwoBlockJacquet.Sections F hD σD)
      (g : GeneralLinear (t + 1) F.Carrier) :
      JD.val (TwoBlockJacquet.inducedRep F hD σD g fD) =
        TwoBlockJacquet.jacquetFunction ψD (fun i => (ellD i).val) μD fD g := by
    have hh := congrArg (fun Z : InverseWhittakerFunctions ψD t => Z.val g) (hcoeff fD)
    change JD.val (TwoBlockJacquet.inducedRep F hD σD g fD) =
      J.val (TwoBlockJacquet.inducedRep F h σ
        (weylLong (t + 1) F.Carrier * inverseTranspose (t + 1) F.Carrier g)
        (E.symm fD)) at hh
    rw [hh, hJ]
    simpa only [E.apply_symm_apply] using (hjac (E.symm fD) g).symm
  refine ⟨hcoeff, hJD, transportedSecondDualFunctional_ne_zero ψ
    (TwoBlockJacquet.inducedRep F h σ) E, ?_, ?_⟩
  · intro fD
    simpa only [E.apply_symm_apply] using habs (E.symm fD)
  · intro μN fD Wtest Φ
    rw [unfoldedJacquetSeries_eq F hD ψD σD ellD μD μN JD hJD fD Wtest Φ,
      hcoeff]

end ActualJacquet

end Langlands.RankinSelberg.DominantRankTransport

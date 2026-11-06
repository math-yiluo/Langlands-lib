import Langlands.Correspondence.SupercuspidalFiniteEpsilonStatement
import Langlands.Correspondence.FiniteAuxiliaryProof
import Langlands.Representation.RankinSelberg.LocalConverseStatement

/-!
# Finite selection and lifting of actual epsilon tests

Finite lifting is proved from the statement's supplied rankwise surjections.
Finite separation retains the local converse as an explicit premise.
-/

noncomputable section

namespace Langlands.Henniart

universe uF uC uT uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : MeasurableSpace F.Carrier := borel F.Carrier
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : NonarchimedeanRing F.Carrier := by
  convert! ValuativeRel.nonarchimedeanRing F.Carrier
  exact Valuation.toTopologicalSpace_eq _

namespace FiniteEpsilon

/-- Rankwise surjectivity gives surjectivity of the rank-preserving projection. -/
theorem project_surjective {k : ℕ} (lower : LowerRankMaps.{uF, uT, uW} F k)
    (hsurj : ∀ r : Fin (k + 1), Function.Surjective (lower r)) :
    Function.Surjective (project lower) := by
  rintro ⟨r, τ⟩
  obtain ⟨σ, hσ⟩ := hsurj r τ
  refine ⟨⟨r, σ⟩, ?_⟩
  change (⟨r, lower r σ⟩ : SupercuspidalTest F k) = ⟨r, τ⟩
  rw [hσ]

/-- Coverage by the selected lifts transports separation to those lifts. -/
theorem liftedSeparates_of_exactImage
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier}
    {ν : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier} {k : ℕ}
    {P : Set (PadicField.SupercuspidalClass.{uC, uF} F (k + 2) (by omega))}
    {D : Finset (SupercuspidalTest.{uF, uT} F k)}
    {lower : LowerRankMaps.{uF, uT, uW} F k}
    {S : Finset (WeilTest.{uF, uW} F k)}
    (hsep : Separates F ψ ν P D) (himage : ExactImage F lower D S) :
    LiftedSeparates F ψ ν P lower S := by
  intro π hπ π' hπ' hequal
  apply hsep π hπ π' hπ'
  intro t ht
  obtain ⟨s, hs, hst⟩ := himage.2 t ht
  rw [← hst]
  exact hequal s hs

end FiniteEpsilon

open FiniteEpsilon

/-- The actual finite lifting target needs only its stated surjections. -/
theorem finiteSupercuspidalEpsilonLifting :
    FiniteSupercuspidalEpsilonLiftingStatement.{uF, uC, uT, uW} F := by
  intro ψ ν _hdual k P D lower hsep hsurj
  obtain ⟨S, hmaps, hcover⟩ :=
    finiteTestLifting (WeilTest F k) (SupercuspidalTest F k)
      D (project lower) (fun t _ => project_surjective F lower hsurj t)
  exact ⟨S, ⟨hmaps, hcover⟩,
    liftedSeparates_of_exactImage F hsep ⟨hmaps, hcover⟩⟩

/-- Choose one failed common-certificate test per distinct finite candidate pair. -/
theorem finiteSupercuspidalEpsilonSeparation_of_localConverse
    (hconverse : RankinSelberg.SupercuspidalLocalConverseStatement.{uF, uC, uT}) :
    FiniteSupercuspidalEpsilonSeparationStatement.{uF, uC, uT} F := by
  classical
  intro ψ ν hdual k P hP
  have distinguish (π π' :
      PadicField.SupercuspidalClass.{uC, uF} F (k + 2) (by omega))
      (hne : π ≠ π') :
      ∃ t : SupercuspidalTest.{uF, uT} F k, ¬ Agree F ψ ν π π' t := by
    by_contra! hall
    apply hne
    apply hconverse p F ψ ⟨ν, hdual⟩ k π π'
    intro r hr τ
    exact hall ⟨⟨r, by omega⟩, τ⟩
  let := hP.fintype
  let pairs := {a : P × P // a.1.val ≠ a.2.val}
  let pick : pairs → SupercuspidalTest.{uF, uT} F k :=
    fun a => Classical.choose (distinguish a.1.1 a.1.2 a.2)
  refine ⟨Finset.univ.image pick, ?_⟩
  intro π hπ π' hπ' hequal
  by_contra hne
  let a : pairs := ⟨(⟨π, hπ⟩, ⟨π', hπ'⟩), hne⟩
  have ha : pick a ∈ Finset.univ.image pick :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  exact (Classical.choose_spec (distinguish π π' hne)) (hequal (pick a) ha)

/-- Apply finite separation to the published central-character level stratum. -/
theorem supercuspidalStratumEpsilonSeparation_of_finiteSeparation
    (hsep : FiniteSupercuspidalEpsilonSeparationStatement.{uF, uC, uT} F) :
    SupercuspidalStratumEpsilonSeparationStatement.{uF, uC, uT} F := by
  intro hfinite ψ ν hdual k χ b
  exact hsep ψ ν hdual k
    (GeneralLinear.SupercuspidalClass.centralLevelStratum.{uF, uC} χ b)
    (hfinite F.Carrier (k + 1) χ b)

/-- The finite family reduces to local converse and the stated stratum premise. -/
theorem supercuspidalFiniteEpsilon_of_localConverse
    (hconverse : RankinSelberg.SupercuspidalLocalConverseStatement.{uF, uC, uT}) :
    SupercuspidalFiniteEpsilonStatement.{uF, uC, uT, uW} := by
  intro p _ F
  have hsep := finiteSupercuspidalEpsilonSeparation_of_localConverse F hconverse
  exact ⟨hsep, supercuspidalStratumEpsilonSeparation_of_finiteSeparation F hsep,
    finiteSupercuspidalEpsilonLifting F⟩

end Langlands.Henniart

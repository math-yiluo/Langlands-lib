import Langlands.Representation.RankinSelberg.EpsilonFactor
import Langlands.Correspondence.SupercuspidalFinitenessStatement
import Langlands.Weil.Local.Parameters
import Langlands.LocalField.Topology
import Mathlib.Data.Finset.Basic

/-!
# Finite epsilon tests on actual supercuspidal classes

Proposition definitions for the finite-selection and lower-rank lifting
reformulation of Henniart 1993, Corollary p.340 and Theorem 4.1 p.348,
used in Henniart 2000, Section 4.3. Candidate rank is `k + 2`; tests indexed
by `r : Fin (k + 1)` have rank `r.val + 1`.
-/

noncomputable section

namespace Langlands.Henniart

universe uF uC uT uW

namespace FiniteEpsilon

variable {p : ℕ} [Fact p.Prime]

/-- Actual supercuspidal tests of every rank from 1 through `k + 1`. -/
abbrev SupercuspidalTest (F : PadicField.{uF} p) (k : ℕ) :=
  (r : Fin (k + 1)) ×
    PadicField.SupercuspidalClass.{uT, uF} F (r.val + 1) (Nat.succ_pos _)

/-- Actual irreducible local Weil classes with the same lower-rank indices. -/
abbrev WeilTest (F : PadicField.{uF} p) (k : ℕ) :=
  (r : Fin (k + 1)) ×
    Weil.Local.LocalContinuousIrreducibleWeilClasses.{uF, uW} F (r.val + 1)

-- Both carrier universes occur in the maximum of the map type; they must
-- remain independent even though their roles are different.
set_option linter.checkUnivs false in
/-- A map at every allowed rank; surjectivity is a separate premise. -/
abbrev LowerRankMaps (F : PadicField.{uF} p) (k : ℕ) :=
  (r : Fin (k + 1)) →
    Weil.Local.LocalContinuousIrreducibleWeilClasses.{uF, uW} F (r.val + 1) →
      PadicField.SupercuspidalClass.{uT, uF} F (r.val + 1) (Nat.succ_pos _)

/-- Projection retains the rank and applies the supplied map at that rank. -/
def project {F : PadicField.{uF} p} {k : ℕ}
    (lower : LowerRankMaps.{uF, uT, uW} F k)
    (s : WeilTest.{uF, uW} F k) : SupercuspidalTest.{uF, uT} F k :=
  ⟨s.1, lower s.1 s.2⟩

variable (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : MeasurableSpace F.Carrier := borel F.Carrier
local instance : BorelSpace F.Carrier := ⟨rfl⟩

/-- Agreement means one entire epsilon monomial witnesses both actual relations.
Self-duality is imposed by the statement targets below. -/
def Agree (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
    (ν : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier) {k : ℕ}
    (π π' : PadicField.SupercuspidalClass.{uC, uF} F (k + 2) (by omega))
    (t : SupercuspidalTest.{uF, uT} F k) : Prop :=
  ∃ e : ℂˣ × ℤ,
    RankinSelberg.IsClassEpsilonFactor F ψ ν π t.2 e ∧
      RankinSelberg.IsClassEpsilonFactor F ψ ν π' t.2 e

/-- One fixed finite family separates every pair of members of `P`. -/
def Separates (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
    (ν : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier) {k : ℕ}
    (P : Set (PadicField.SupercuspidalClass.{uC, uF} F (k + 2) (by omega)))
    (D : Finset (SupercuspidalTest.{uF, uT} F k)) : Prop :=
  ∀ π ∈ P, ∀ π' ∈ P, (∀ t ∈ D, Agree F ψ ν π π' t) → π = π'

/-- The selected lifts project onto exactly the selected supercuspidal tests. -/
def ExactImage {k : ℕ} (lower : LowerRankMaps.{uF, uT, uW} F k)
    (D : Finset (SupercuspidalTest.{uF, uT} F k))
    (S : Finset (WeilTest.{uF, uW} F k)) : Prop :=
  (∀ s ∈ S, project lower s ∈ D) ∧
    ∀ t ∈ D, ∃ s ∈ S, project lower s = t

/-- Separation after evaluating each actual Weil class at its supplied image.
This is not an assertion about arithmetic tensor epsilon factors. -/
def LiftedSeparates (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
    (ν : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier) {k : ℕ}
    (P : Set (PadicField.SupercuspidalClass.{uC, uF} F (k + 2) (by omega)))
    (lower : LowerRankMaps.{uF, uT, uW} F k)
    (S : Finset (WeilTest.{uF, uW} F k)) : Prop :=
  ∀ π ∈ P, ∀ π' ∈ P,
    (∀ s ∈ S, Agree F ψ ν π π' (project lower s)) → π = π'

end FiniteEpsilon

open FiniteEpsilon

section Statements

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

/-- Every finite set of rank-`k+2` supercuspidal classes admits a finite
separating family of actual lower-rank tests, for one fixed character and
its self-dual Haar measure. No common central character is required. -/
def FiniteSupercuspidalEpsilonSeparationStatement : Prop :=
  ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
    (ν : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier),
    HarmonicAnalysis.IsSelfDual ψ ν →
    ∀ (k : ℕ)
      (P : Set (PadicField.SupercuspidalClass.{uC, uF} F (k + 2) (by omega))),
      P.Finite →
        ∃ D : Finset (SupercuspidalTest.{uF, uT} F k), Separates F ψ ν P D

/-- Application to the exact published fixed-central-character, bounded-first-level
strata, with the owner's bounded-level finiteness target as an explicit premise. -/
def SupercuspidalStratumEpsilonSeparationStatement : Prop :=
  SupercuspidalBoundedLevelFinitenessStatement.{uF, uC} →
  ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
    (ν : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier),
    HarmonicAnalysis.IsSelfDual ψ ν →
    ∀ (k : ℕ) (χ : Subgroup.center (GeneralLinear (k + 2) F.Carrier) →* ℂˣ) (b : ℕ),
      ∃ D : Finset (SupercuspidalTest.{uF, uT} F k),
        Separates F ψ ν
          (GeneralLinear.SupercuspidalClass.centralLevelStratum.{uF, uC} χ b) D

/-- Rankwise surjectivity lifts a given finite separating family to actual
irreducible Weil classes, with exact projected image and preserved separation. -/
def FiniteSupercuspidalEpsilonLiftingStatement : Prop :=
  ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
    (ν : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier),
    HarmonicAnalysis.IsSelfDual ψ ν →
    ∀ (k : ℕ)
      (P : Set (PadicField.SupercuspidalClass.{uC, uF} F (k + 2) (by omega)))
      (D : Finset (SupercuspidalTest.{uF, uT} F k))
      (lower : LowerRankMaps.{uF, uT, uW} F k),
      Separates F ψ ν P D →
      (∀ r : Fin (k + 1), Function.Surjective (lower r)) →
        ∃ S : Finset (WeilTest.{uF, uW} F k),
          ExactImage F lower D S ∧ LiftedSeparates F ψ ν P lower S

end Statements

/-- The finite epsilon-test and lifting family for genuine local objects.
All ranks at least two are covered; rank-one reciprocity is a separate input. -/
def SupercuspidalFiniteEpsilonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    FiniteSupercuspidalEpsilonSeparationStatement.{uF, uC, uT} F ∧
    SupercuspidalStratumEpsilonSeparationStatement.{uF, uC, uT} F ∧
    FiniteSupercuspidalEpsilonLiftingStatement.{uF, uC, uT, uW} F

end Langlands.Henniart

import Langlands.Correspondence.HenniartExtensionDual
import Langlands.Correspondence.HenniartExtensionRankOne
import Langlands.Correspondence.HenniartExtensionDeterminant
import Langlands.Correspondence.HenniartExtensionFactors
import Langlands.Correspondence.BaseGeometricResidue
import Langlands.Correspondence.BaseReciprocityCandidate
import Langlands.ClassFieldTheory.Local.ReciprocitySystemStatement
import Langlands.Correspondence.SupercuspidalUniquenessFromConverse

/-!
# Henniart's construction from stable images

Henniart (2000), §4.4, with Henniart (1993), §§4.3–4.4. The stable images of the
rank induction, extended to all irreducible classes by unramified twists, form a
supercuspidal correspondence agreeing with the stable images on finite-image
unitary classes. The rank induction, candidate existence, the unramified-twist
independence, the unitary twists of supercuspidal classes, local class field
theory, the existence of local constants and the unramified-twist laws of pair
factors are explicit hypotheses. With local converse, which identifies any two
correspondences, this gives the all-field supercuspidal correspondence.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap
open LocalFactor LocalFactor.CommonClosure

universe uK uW uV uE

/-- Henniart's §4.4 as a conditional statement: candidate existence, the rank
induction and the unramified-twist independence of Henniart's stable map,
together with the unitary twists of supercuspidal classes, the existence of
normalized local reciprocity and of local constants, and the unramified-twist
laws of the pair factors on both sides, give Henniart's construction statement. -/
def HenniartConstructionReductionStatement : Prop :=
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
  StableCorrespondenceStatement.{uK, uW, uV, uW} →
  UnramifiedTwistIndependenceStatement.{uK, uW, uV, uW} →
  SupercuspidalUnitaryFiniteOrderTwistStatement.{uK, uV} →
  LocalClassField.CommonClosureReciprocityExistence.{uK} →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (eC : ReciprocityFamily K),
    NonabelianSystem.Exists.{uK, uW} K eC) →
  RankinSelberg.UnramifiedTwistEpsilonStatement.{uK, uV, uV} →
  ArithmeticPairUnramifiedTwistStatement.{uK, uW} →
  HenniartConstructionStatement.{uK, uW, uV, uW}

theorem henniartConstructionReduction :
    HenniartConstructionReductionStatement.{uK, uW, uV} := by
  intro hCE hSC hUTI hunit hrec hsys hGLε hWtw p _ K
  obtain ⟨eC, heC⟩ := hrec p K K.canonicalTopologicalData
  obtain ⟨ε, hε⟩ := hsys p K eC heC
  let e := baseReciprocityCandidate K eC
  have he : IsGeometricReciprocity K e := baseGeometricReciprocityProof K eC heC
  refine ⟨extensionMap K hSC, ⟨extensionMap_rankwiseBijective K hCE hSC hUTI hunit he,
    extensionMap_dual K hSC hUTI, e, he, extensionMap_rankOne K hCE hSC hUTI he,
    extensionMap_determinant K hSC he, extensionMap_twist K hCE hSC hUTI he,
    eC, ε, hε, baseReciprocityCandidate_spec K eC,
    extensionMap_pairFactors K hCE hSC hGLε hWtw eC ε hε⟩, ?_⟩
  intro σ hσ
  exact extensionMap_agrees K hSC hUTI σ hσ

/-- Henniart's construction gives existence over every p-adic field. The
local-constant universe `uE` of the stable images is arbitrary. -/
theorem supercuspidalCorrespondenceExistence_of_henniartConstruction
    (hconstruction : HenniartConstructionStatement.{uK, uW, uV, uE})
    (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) :
    SupercuspidalCorrespondenceExistence.{uK, uW, uV} K := by
  obtain ⟨c, hc, -⟩ := hconstruction p K
  exact ⟨c, hc⟩

/-- Local converse and Henniart's construction statement give the all-field
supercuspidal correspondence. -/
theorem supercuspidalCorrespondenceStatement_of_localConverse_of_henniartConstruction
    (hconverse : RankinSelberg.SupercuspidalLocalConverseStatement.{uK, uV, uV})
    (hconstruction : HenniartConstructionStatement.{uK, uW, uV, uE}) :
    SupercuspidalCorrespondenceStatement.{uK, uW, uV} :=
  supercuspidalCorrespondenceStatement_of_localConverse_of_existence hconverse
    (fun p _ K => supercuspidalCorrespondenceExistence_of_henniartConstruction hconstruction p K)

/-- Henniart's route to the all-field supercuspidal correspondence, with every
remaining input explicit: local converse, candidate existence, the rank induction
and unramified-twist independence of the stable map, the unitary twists of
supercuspidal classes, normalized local reciprocity, local constants, and the
unramified-twist laws of the pair factors on both sides. -/
def SupercuspidalCorrespondenceHenniartReductionStatement : Prop :=
  RankinSelberg.SupercuspidalLocalConverseStatement.{uK, uV, uV} →
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
  StableCorrespondenceStatement.{uK, uW, uV, uW} →
  UnramifiedTwistIndependenceStatement.{uK, uW, uV, uW} →
  SupercuspidalUnitaryFiniteOrderTwistStatement.{uK, uV} →
  LocalClassField.CommonClosureReciprocityExistence.{uK} →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (eC : ReciprocityFamily K),
    NonabelianSystem.Exists.{uK, uW} K eC) →
  RankinSelberg.UnramifiedTwistEpsilonStatement.{uK, uV, uV} →
  ArithmeticPairUnramifiedTwistStatement.{uK, uW} →
  SupercuspidalCorrespondenceStatement.{uK, uW, uV}

theorem supercuspidalCorrespondenceHenniartReduction :
    SupercuspidalCorrespondenceHenniartReductionStatement.{uK, uW, uV} := by
  intro hconverse hCE hSC hUTI hunit hrec hsys hGLε hWtw
  exact supercuspidalCorrespondenceStatement_of_localConverse_of_henniartConstruction
    hconverse (henniartConstructionReduction hCE hSC hUTI hunit hrec hsys hGLε hWtw)

end Langlands.Henniart.Extension

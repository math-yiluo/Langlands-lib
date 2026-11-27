import Langlands.BaseChange.ConductorGlobalizationChoices
import Langlands.BaseChange.CuspidalSigmaLiftConductorFromWeakPresentations
import Langlands.BaseChange.PrescribedSupercuspidalsInCuspidalPresentation
import Langlands.BaseChange.SupercuspidalExistenceProof
import Langlands.BaseChange.WeakCyclicLiftFromLowerPresentation
import Langlands.Global.AdeleQuotientCompactProof
import Langlands.Global.AdelicNormOneHaarRightInvariantProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective
import Langlands.GroupScheme.Rational.GeneralLinearCharacterAdapters
import Langlands.TraceFormula.CyclicFieldGlobalizationProof

/-! # The conductor formula from the global existence and uniqueness inputs -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v uV uW

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.BaseChange

open Automorphic Automorphic.GroupSchemeFunctions Global Global.AdelicFunctoriality
open Global.AdelicGroupPoints Global.CompletionPadic Global.CuspidalPairFunctionalEquation
open GeneralLinear GroupScheme HarmonicAnalysis TraceFormula
open scoped FiniteExtension

local instance conductorGlobalGLAffine (F : Type) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance conductorGlobalGLSmooth (F : Type) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)
local instance conductorGlobalRationalGroup (F : Type) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance conductorGlobalContinuousGroup (F : Type) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance conductorGlobalSmoothGroup (F : Type) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance conductorGlobalFormsGroup (F : Type) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.AutomorphicForms F n) := Submodule.addCommGroup _
local instance conductorGlobalLocalGroup {F : Type} [Field F] [NumberField F] {n : ℕ} {p : FinitePlace F}
    (D : LocalRealization F n p) : AddCommGroup D.Space := Submodule.addCommGroup _

set_option maxHeartbeats 5200000 in
private theorem prescribedSupercuspidals_for_scalarCentre
    (hGlob : GeneralLinearSupercuspidalGlobalizationStatement.{0, uV})
    (hReal : GeneralLinearCuspidalSummandRealizationStatement.{0})
    (K : Type) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)] (r : ℕ)
    (Sc : Finset (FinitePlace K)) (hSc : Sc.Nonempty)
    (vaux : FinitePlace K) (haux : vaux ∉ Sc)
    (V : FinitePlace K → Type uV) [∀ p, AddCommGroup (V p)] [∀ p, Module ℂ (V p)]
    (ρ : ∀ p : FinitePlace K, Representation ℂ (GeneralLinear (r + 1) (p.adicCompletion K)) (V p))
    (hρ : ∀ p ∈ Sc, (ρ p).IsIrreducible ∧ IsSupercuspidal (ρ p)) :
    ∃ (R : CuspidalOperatorRealization K r) (D : CuspidalSpectralPresentation.{0, 0} R),
      HasIrreducibleAdmissibleComponents D ∧
      ∀ p ∈ Sc, (D.localComponent p).IsSupercuspidal ∧
        ∃ ξ : Quasicharacter (p.adicCompletion K),
          (padicField p).canonicalTopologicalData.IsUnramifiedCharacter ξ.toMonoidHom ∧
          Nonempty ((twist (ξ.toMonoidHom.comp determinant) (ρ p)).Equiv (D.localComponent p).representation) := by
  let G := GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of K)
  let T := Gm (Spec (CommRingCat.of K))
  let i : T.toGrp ⟶ G := GroupScheme.GeneralLinear.scalarTorus (Fin (r + 1)) (CommRingCat.of K)
  have hG := GroupScheme.isConnectedReductive_generalLinear K (Fin (r + 1))
  let : Nonempty (Fin (r + 1)) := ⟨⟨0, Nat.succ_pos r⟩⟩
  have hs := GroupScheme.GeneralLinear.scalarTorus_isSplitComponent (n := Fin (r + 1)) K
  have hi : Function.Injective (characterRestrict i) :=
    characterRestrict_injective_of_centralSplitTorusCharacter centralSplitTorusCharacter hG hs
  let : (characterRestrict i).range.FiniteIndex := hs.finiteIndex_range_characterRestrict hG
  let : (Measure.haar : Measure (normOneSubgroup K G)).IsMulRightInvariant :=
    normOneHaarRightInvariant K G hG.smooth hG.connectedSpace
  let (p : FinitePlace K) : MeasurableSpace (GeneralLinear (r + 1) (p.adicCompletion K)) := borel _
  let (p : FinitePlace K) : BorelSpace (GeneralLinear (r + 1) (p.adicCompletion K)) := ⟨rfl⟩
  let (p : FinitePlace K) : LocallyCompactSpace (GeneralLinear (r + 1) (p.adicCompletion K)) := by
    let : ValuativeRel (p.adicCompletion K) := (topologicalData p).valuativeRel
    let : IsNonarchimedeanLocalField (p.adicCompletion K) := (topologicalData p).localField
    exact LocalFieldTopology.generalLinear_locallyCompactSpace (p.adicCompletion K) (r + 1)
  let (p : FinitePlace K) : TotallyDisconnectedSpace (GeneralLinear (r + 1) (p.adicCompletion K)) := by
    let : ValuativeRel (p.adicCompletion K) := (topologicalData p).valuativeRel
    let : IsNonarchimedeanLocalField (p.adicCompletion K) := (topologicalData p).localField
    exact LocalFieldTopology.generalLinear_totallyDisconnectedSpace (p.adicCompletion K) (r + 1)
  exact prescribedSupercuspidalsInCuspidalPresentation K r hGlob hReal parabolicDynamic T i hi
    PUnit (splitTorus.gmIso (Spec (CommRingCat.of K))) hs.isCentralSplitTorus.2 Sc hSc vaux haux V ρ hρ

set_option maxHeartbeats 8200000 in
/-- Choose the global fields and prescribed finite components, then apply
the any-degree lift to the actual unitary lower presentation. -/
theorem weakPresentationData_of_cyclicGlobalization
    (hGlob : GeneralLinearSupercuspidalGlobalizationStatement.{0, uV})
    (hReal : GeneralLinearCuspidalSummandRealizationStatement.{0})
    (hLift : CuspidalCyclicBaseChangeLiftAnyDegreeStatement.{0, 0, 0}) :
    CuspidalSigmaLiftWeakPresentationDataStatement.{u, v, uV, uW} := by
  classical
  intro F _ _ _ _ _ E _ _ _ _ _ _ σ l hcyc r _ V _ _ π _ hπs hπi
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨K, L, fK, fL, nK, nL, aKL, σ₀, gKL, hcyc₀, hinfinite,
    p, v₁, v₂, vaux, w, hw, a, b, ha, ha', hb, hb', hab, hσb, _, _, h₁₂, haux, h₁, h₂, _, W, _,
    _, ρ, hρ, eρ⟩ :=
    conductorGlobalizationChoices cyclicFieldGlobalization supercuspidalExistence.{0, uV}
      F E σ l hcyc r V π hπi hπs
  let : FiniteDimensional K L := hcyc₀.1
  have hcard : orderOf σ₀ = Nat.card (L ≃ₐ[K] L) := by
    rw [IsGalois.card_aut_eq_finrank, hcyc₀.2.1, hcyc₀.2.2.2.1]
  let cKL : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_orderOf_eq_card σ₀ hcard
  let ck := compactSpace_adeleQuotient K
  let cl := compactSpace_adeleQuotient L
  let Sc : Finset (FinitePlace K) := {p, v₁, v₂}
  have hp : p ∈ Sc := by simp [Sc]
  have hv₁ : v₁ ∈ Sc := by simp [Sc]
  have hv₂ : v₂ ∈ Sc := by simp [Sc]
  obtain ⟨T, D, hD, hpres⟩ := prescribedSupercuspidals_for_scalarCentre hGlob hReal
    K r Sc ⟨p, hp⟩ vaux haux W ρ (fun q _ => hρ q)
  obtain ⟨hDs, ξ, hξ, ⟨d⟩⟩ := hpres p hp
  let R := π.comp (Matrix.GeneralLinearGroup.map a.symm.toRingHom)
  have eπ : Nonempty (π.Equiv (R.comp (Matrix.GeneralLinearGroup.map a.toRingHom))) := by
    let aG := fieldEquiv (r + 1) a ha ha'
    have h : R.comp (Matrix.GeneralLinearGroup.map a.toRingHom) = π :=
      MonoidHom.ext fun g => congrArg π (aG.symm_apply_apply g)
    exact ⟨equivOfRepresentationEq h.symm⟩
  obtain ⟨g⟩ := eρ
  have eR : Nonempty ((twist (ξ.toMonoidHom.comp determinant) R).Equiv (D.localComponent p).representation) :=
    ⟨(twistEquiv (ξ.toMonoidHom.comp determinant) g).trans d⟩
  obtain ⟨T', U, D', Q, hD', hQ, ξ', hξ', eR', htensor, hD's, hweak⟩ :=
    weakCyclicLiftFromLowerPresentation hLift σ₀ l hcyc₀ hinfinite p v₁ v₂ h₁₂ h₁ h₂ w hw D hD
      hDs (hpres v₁ hv₁).1 (hpres v₂ hv₂).1 R ξ hξ eR
  exact ⟨K, L, fK, nK, fL, nL, aKL, gKL, cKL, ck, cl, σ₀, p, w, hw, a, b, ha, ha', hb, hb',
    hab, hσb, T', U, D', Q, hD', hQ, R, ξ', hξ', eπ, eR', htensor, hD's, hweak⟩

/-- The conductor statement follows from the completed standard equations
and the stated global existence and local uniqueness inputs. -/
def CuspidalSigmaLiftConductorFromGlobalizationStatement : Prop :=
  GeneralLinearSupercuspidalGlobalizationStatement.{0, uV} →
  GeneralLinearCuspidalSummandRealizationStatement.{0} →
  CuspidalCyclicBaseChangeLiftAnyDegreeStatement.{0, 0, 0} →
  CuspidalPairGlobalFunctionalEquationStatement.{0, 0} →
  SigmaLiftUniquenessStatement.{u, v, uV, uW, 0} →
    CuspidalSigmaLiftConductorStatement.{u, v, uV, uW}

theorem cuspidalSigmaLiftConductorFromGlobalization :
    CuspidalSigmaLiftConductorFromGlobalizationStatement.{u, v, uV, uW} :=
  fun hGlob hReal hLift hFE hUnique =>
    cuspidalSigmaLiftConductorFromWeakPresentations hFE hUnique
      (weakPresentationData_of_cyclicGlobalization hGlob hReal hLift)

end Langlands.BaseChange

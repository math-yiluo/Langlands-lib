import Langlands.BaseChange.GlobalHeckeNormTwistDepth
import Langlands.BaseChange.GlobalNormCharacterRestriction
import Langlands.Representation.Unramified.WeakTransfer

/-! # A simultaneous auxiliary twist for weak base change -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.BaseChange

open Automorphic Correspondence Global Global.AdelicFunctoriality Global.CompletionPadic
open Global.CuspidalPairFunctionalEquation Global.HeckeFunctionalEquation
open HarmonicAnalysis LocalClassField Unramified
open LocalFactor.PadicAbelian (epsilonExponent)
open scoped NumberField FiniteExtension

universe u uQ

local instance auxiliaryTwistRationalGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance auxiliaryTwistContinuousGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance auxiliaryTwistSmoothGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance auxiliaryTwistFormsGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _

section Local

variable {K : Type u} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
  {r : ℕ} {T : CuspidalOperatorRealization K r}
  (D : CuspidalSpectralPresentation.{u, uQ} T) (hD : HasIrreducibleAdmissibleComponents D)
  (v : FinitePlace K) (χ : QuasiCharacter (padicField v))

/-- Every supplied standard factor choice of this local twist has the
highly ramified polynomial and exponent formulas. -/
def HasHighlyRamifiedStandardFactors : Prop :=
  letI := (padicField v).canonicalTopologicalData.topology
  ∀ c : StandardTwistFactorChoice (padicField v) (standardFiniteAdditiveComponent K v)
    ((D.localComponent v).padicObject (hD v).1 (hD v).2) χ,
    c.lPolynomial = 1 ∧ c.epsilon.2 = (r + 1 : ℕ) *
      epsilonExponent (padicField v).canonicalTopologicalData χ (standardFiniteAdditiveComponent K v)

private theorem exists_conductorBound_presentedStandardFactors :
    ∃ B : ℕ, ∀ φ : QuasiCharacter (padicField v),
      B ≤ (padicField v).canonicalTopologicalData.multiplicativeConductor φ →
        HasHighlyRamifiedStandardFactors D hD v φ := by
  exact exists_conductorBound_standardTwistFactors (padicField v) (standardFiniteAdditiveComponent K v)
    ((D.localComponent v).padicObject (hD v).1 (hD v).2)
    (Automorphic.CuspidalPairPartialGamma.localGenericity K r T D v (hD v).1 (hD v).2
      (standardFiniteAdditiveComponent K v))

end Local

section Global

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
  {r : ℕ} {T Td : CuspidalOperatorRealization K r} {U Ud : CuspidalOperatorRealization L r}
  (D : CuspidalSpectralPresentation.{u, uQ} T) (Dd : CuspidalSpectralPresentation.{u, uQ} Td)
  (Q : CuspidalSpectralPresentation.{u, uQ} U) (Qd : CuspidalSpectralPresentation.{u, uQ} Ud)
  (hD : HasIrreducibleAdmissibleComponents D) (hDd : HasIrreducibleAdmissibleComponents Dd)
  (hQ : HasIrreducibleAdmissibleComponents Q) (hQd : HasIrreducibleAdmissibleComponents Qd)

/-- Defined spherical parameters at the lower place and every upper place,
related by the actual residue-degree power. -/
def HasSphericalPowerData (v : FinitePlace K) : Prop :=
  ∃ (hv : v ∉ D.exceptional) (hw : ∀ w : FinitePlacesAbove L v, w.1 ∉ Q.exceptional),
    ∀ w : FinitePlacesAbove L v, Q.spectralSystem.eigenvalues w.1 (hw w) =
      (D.spectralSystem.eigenvalues v hv).power (w.1.asIdeal.inertiaDeg (𝓞 K))

variable [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

/-- At the specified auxiliary place the original forward factors can be
compared spherically, or both pairs have the highly ramified formulas. -/
def HasCommonTwistAuxiliaryData (ν : HeckeCharacter K) (v : FinitePlace K) : Prop :=
  HasSphericalPowerData D Q v ∨
    (letI := (padicField v).canonicalTopologicalData.topology
     let η := quasicharacterBase v (ν.finiteComponent v)
     ∀ (w : FinitePlacesAbove L v) (κ : QuasiCharacter (padicField v)),
       IsNormTrivial (w.1.adicCompletion L) κ.toMonoidHom →
       HasHighlyRamifiedStandardFactors D hD v (κ * η) ∧
         HasHighlyRamifiedStandardFactors Dd hDd v (κ * η)⁻¹) ∧
    (∀ w : FinitePlacesAbove L v,
      letI := (padicField w.1).canonicalTopologicalData.topology
      let η := quasicharacterBase w.1 ((ν.normComp (L := L)).finiteComponent w.1)
      HasHighlyRamifiedStandardFactors Q hQ w.1 η ∧
        HasHighlyRamifiedStandardFactors Qd hQd w.1 η⁻¹)

variable (v₀ : FinitePlace K)

/-- A weak spherical base change admits a common Hecke twist trivial at the
chosen place. At every other finite place, the original spherical power data
or the highly ramified standard factor formulas are available. The ramified
formulas include the inverse twists of the supplied dual presentations. -/
def WeakBaseChangeAuxiliaryTwistStatement : Prop :=
  Q.spectralSystem.IsArithmeticWeakBaseChangeOf D.spectralSystem →
  ∃ ν : HeckeCharacter K, ν.HasFiniteOrder ∧ ν.finiteComponent v₀ = 1 ∧
    (∀ w : FinitePlacesAbove L v₀, (ν.normComp (L := L)).finiteComponent w.1 = 1) ∧
    ∀ v : FinitePlace K, v ≠ v₀ → HasCommonTwistAuxiliaryData D Dd Q Qd hD hDd hQ hQd ν v

set_option maxHeartbeats 1900000 in
/-- Apply finite Hecke character prescription to the exceptional finite places
of the weak comparison. -/
theorem weakBaseChangeAuxiliaryTwist : WeakBaseChangeAuxiliaryTwistStatement D Dd Q Qd hD hDd hQ hQd v₀ := by
  classical
  intro hweak
  have hgood : ∀ᶠ v in Filter.cofinite, HasSphericalPowerData D Q v :=
    hweak.mono fun v ⟨hv, hw, _, hpower⟩ => ⟨hv, hw, hpower⟩
  let bad := (Filter.eventually_cofinite.mp hgood).toFinset
  let S := bad.erase v₀
  choose bD hbD using fun v => exists_conductorBound_presentedStandardFactors D hD v
  choose bDd hbDd using fun v => exists_conductorBound_presentedStandardFactors Dd hDd v
  choose bQ hbQ using fun w => exists_conductorBound_presentedStandardFactors Q hQ w
  choose bQd hbQd using fun w => exists_conductorBound_presentedStandardFactors Qd hQd w
  let I := (L ≃ₐ[K] L) →* ℂˣ
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨χ, _, _, _, hres⟩ := globalNormCharacterRestriction K L
  obtain ⟨ν, hν, hν₀, hν₀', hlevels⟩ := globalHeckeNormTwistDepth K L I χ v₀ S (Finset.notMem_erase _ _)
    (fun v _ w κ => (hres v w κ).1) (fun v => max (bD v) (bDd v)) (fun w => max (bQ w) (bQd w))
  refine ⟨ν, hν, hν₀, hν₀', fun v hv => ?_⟩
  by_cases hS : v ∈ S
  · refine Or.inr ⟨?_, ?_⟩
    · intro η w κ hκ
      let := (padicField v).canonicalTopologicalData.topology
      obtain ⟨i, hi⟩ := (hres v w κ.toMonoidHom).1.mp hκ
      have he : quasicharacterBase v ((χ i).finiteComponent v) = κ :=
        ContinuousMonoidHom.toMonoidHom_injective hi
      have hl := (hlevels v hS).1 i
      rw [he] at hl
      refine ⟨hbD v _ ((le_max_left _ _).trans hl), hbDd v _ ?_⟩
      rw [conductor_inv_eq (padicField v).canonicalTopologicalData]
      exact (le_max_right _ _).trans hl
    · intro w η
      have hl := (hlevels v hS).2 w
      refine ⟨hbQ w.1 _ ((le_max_left _ _).trans hl), hbQd w.1 _ ?_⟩
      rw [conductor_inv_eq (padicField w.1).canonicalTopologicalData]
      exact (le_max_right _ _).trans hl
  · refine Or.inl ?_
    by_contra h
    have hbad : v ∈ bad := (Set.Finite.mem_toFinset _).mpr h
    exact hS (Finset.mem_erase.mpr ⟨hv, hbad⟩)

end Global

end Langlands.BaseChange

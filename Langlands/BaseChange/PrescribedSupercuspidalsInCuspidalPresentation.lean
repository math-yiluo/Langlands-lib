import Langlands.Automorphic.CuspidalAdmissible.Existence
import Langlands.Automorphic.CuspidalSlicePresentation
import Langlands.Automorphic.PresentedLocalComponentHilbertOccurrence
import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Global.Factors.RelativeWeilLocalEulerBridge
import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.TraceFormula.GeneralLinearSupercuspidalGlobalizationStatement

/-! # Realizing prescribed supercuspidal occurrences in spectral presentations -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.BaseChange

open Automorphic Automorphic.GroupSchemeFunctions Correspondence GeneralLinear Global
open Global.AdelicGroupPoints Global.CompletionPadic Global.PositiveRealTorus
open Global.CuspidalPairFunctionalEquation GroupScheme HarmonicAnalysis TraceFormula

local instance prescribedGLAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance prescribedGLSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)
local instance prescribedRationalGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance prescribedContinuousGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance prescribedSmoothGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance prescribedFormsGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.AutomorphicForms F n) := Submodule.addCommGroup _
local instance prescribedStableGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance prescribedLocalGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} {v : FinitePlace F}
    (D : LocalRealization F n v) : AddCommGroup D.Space := Submodule.addCommGroup _

section Local

variable {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)

set_option maxHeartbeats 1000000 in
private theorem exists_unramifiedQuasicharacter
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ x : (v.adicCompletion F)ˣ, Valued.v (x : v.adicCompletion F) = 1 → χ x = 1) :
    ∃ ξ : Quasicharacter (v.adicCompletion F),
      ξ.toMonoidHom = χ ∧
      (padicField v).canonicalTopologicalData.IsUnramifiedCharacter χ ∧
      IsOpen (χ.ker : Set (v.adicCompletion F)ˣ) := by
  let K := padicField v
  let B := topologicalData v
  let : Algebra (Padic (residuePrime v)) K.Carrier := K.algebra
  let : FiniteDimensional (Padic (residuePrime v)) K.Carrier := K.finiteDimensional
  have hB : B.IsUnramifiedCharacter χ := by
    intro x hx
    have he : B.normalizedAbs x = 1 := by
      have hh : B.normalizedAbsUnits x = 1 := MonoidHom.mem_ker.mp hx
      change (((B.normalizedAbsUnits x).val : ℝ≥0) : ℝ) = 1
      rw [hh]
      rfl
    rw [B.normalizedAbs_eq_canonicalNorm_pow_degree] at he
    have hnonneg : 0 ≤ K.canonicalNorm (x : K.Carrier) := by
      rw [← PadicField.canonicalValuation_coe]
      exact NNReal.coe_nonneg _
    have hn : K.canonicalNorm (x : K.Carrier) = 1 :=
      (pow_left_inj₀ hnonneg zero_le_one Module.finrank_pos.ne').mp
        (he.trans (one_pow _).symm)
    apply hχ x
    apply (CompletionPadic.valued_isEquiv v).eq_one_iff_eq_one.mpr
    rw [← NNReal.coe_inj, PadicField.canonicalValuation_coe, hn]
    rfl
  let z := χ B.uniformizerUnit
  have hEq : χ = B.unramifiedCharacter z := B.eq_unramifiedCharacter χ hB
  refine ⟨B.unramifiedCharacterContinuous z, hEq.symm, ?_, ?_⟩
  · rw [← topologicalData_eq_canonicalTopologicalData v]
    exact hB
  · rw [hEq]
    exact B.isOpen_ker_unramifiedCharacter z

private theorem LocalRealization.isSupercuspidal_of_matrixAction {r : ℕ}
    (A : LocalRealization F (r + 1) v) (hi : A.IsIrreducible)
    (hA : GeneralLinear.IsSupercuspidal A.representation) : A.IsSupercuspidal := by
  let K := padicField v
  let A₀ := A.padicObject hi hA.1
  let : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
  let : TopologicalSpace (GeneralLinear (r + 1) K.Carrier) := K.canonicalGeneralLinearTopology (r + 1)
  have hsc : GeneralLinear.IsSupercuspidal A₀.obj.representation :=
    ⟨A.isAdmissible_canonical_iff.mpr hA.1, hA.2⟩
  let σ : GeneralLinear.SupercuspidalRep.{u, u} (F := K.Carrier) (n := r + 1) :=
    ⟨A₀.obj, hi, hsc⟩
  exact ⟨hi, hA.1, σ.isoClass, rfl⟩

end Local

section Global

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)

local notation "G" => GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)
local notation "hG" => GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))

set_option maxHeartbeats 2200000 in
/-- The Hilbert globalization and summand realization propositions give a
spectral presentation with the prescribed finite supercuspidal actions up
to unramified determinant twists. -/
def PrescribedSupercuspidalsInCuspidalPresentationStatement : Prop :=
  GeneralLinearSupercuspidalGlobalizationStatement.{u, uV} →
  GeneralLinearCuspidalSummandRealizationStatement.{u} →
  ∀ (_hPD : ParabolicDynamicStatement.{u})
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (_hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I] (_e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (_hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
    [∀ v : FinitePlace F, MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion F))]
    [∀ v : FinitePlace F, BorelSpace (GeneralLinear (r + 1) (v.adicCompletion F))]
    [∀ v : FinitePlace F, LocallyCompactSpace (GeneralLinear (r + 1) (v.adicCompletion F))]
    [∀ v : FinitePlace F, TotallyDisconnectedSpace (GeneralLinear (r + 1) (v.adicCompletion F))]
    (Sc : Finset (FinitePlace F)), Sc.Nonempty →
    ∀ (vaux : FinitePlace F), vaux ∉ Sc →
    ∀ (V : FinitePlace F → Type uV) [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
      (ρ : ∀ v : FinitePlace F, Representation ℂ (GeneralLinear (r + 1) (v.adicCompletion F)) (V v)),
      (∀ v ∈ Sc, (ρ v).IsIrreducible ∧ GeneralLinear.IsSupercuspidal (ρ v)) →
      ∃ (R : CuspidalOperatorRealization F r) (D : CuspidalSpectralPresentation.{u, u} R),
        HasIrreducibleAdmissibleComponents D ∧
        ∀ v ∈ Sc, (D.localComponent v).IsSupercuspidal ∧
          ∃ ξ : Quasicharacter (v.adicCompletion F),
            (padicField v).canonicalTopologicalData.IsUnramifiedCharacter ξ.toMonoidHom ∧
            Nonempty ((twist (ξ.toMonoidHom.comp determinant) (ρ v)).Equiv
              (D.localComponent v).representation)

set_option maxHeartbeats 6500000 in
theorem prescribedSupercuspidalsInCuspidalPresentation :
    PrescribedSupercuspidalsInCuspidalPresentationStatement.{u, uV} F r := by
  intro hGlob hReal hPD T i hi _ I _ e hc _ _ _ hLC hTD Sc hSc vaux haux V _ _ ρ hρ
  let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
  let πc := fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
  obtain ⟨P, hComplete, hPne, hPinv, hPirr, -, hlocal⟩ :=
    hGlob F (r + 1) hPD hG T i hi I e hc Sc hSc vaux haux V ρ hρ
  let : CompleteSpace P := hComplete
  have hClosed : IsClosed (P : Set S) := (completeSpace_coe_iff_isComplete.mp hComplete).isClosed
  obtain ⟨R, Φ, hΦ, hclosure⟩ := hReal F r hPD T i hi I e hc P ⟨hPne, hClosed, hPinv, hPirr⟩
  have hΦP : LinearMap.range Φ ≤ P := hclosure ▸ Submodule.le_topologicalClosure _
  obtain ⟨B, hBi, hBa⟩ := cuspidalIrreducibleAdmissibleFiniteSliceExistence F r R
  obtain ⟨D, hD⟩ := R.exists_presentation_of_finiteSlice B hBi hBa
  refine ⟨R, D, hD, fun v hv => ?_⟩
  obtain ⟨χ, hχ, ⟨tv, htv, htvEq⟩, -⟩ := hlocal v hv
  obtain ⟨ξ, hξeq, hξ, hOpen⟩ := exists_unramifiedQuasicharacter v χ hχ
  let δ : GeneralLinear (r + 1) (v.adicCompletion F) →* ℂˣ := χ.comp determinant
  let τ := twist δ (ρ v)
  have hτI : τ.IsIrreducible := (isIrreducible_twist_iff δ (ρ v)).mpr (hρ v hv).1
  have hδ : IsOpen (δ.ker : Set (GeneralLinear (r + 1) (v.adicCompletion F))) := by
    change IsOpen ((determinant : GeneralLinear (r + 1) (v.adicCompletion F) → (v.adicCompletion F)ˣ) ⁻¹'
      (χ.ker : Set (v.adicCompletion F)ˣ))
    exact hOpen.preimage Matrix.GeneralLinearGroup.continuous_det
  have hτsc : GeneralLinear.IsSupercuspidal τ :=
    (isSupercuspidal_twist_iff _ hδ (ker_determinant_le_ker_comp χ) _).mpr (hρ v hv).2
  let a : PlaceGroupPoints F G (.inr v) ≃ₜ* GeneralLinear (r + 1) (v.adicCompletion F) :=
    localGLHomeomorph F (r + 1) (.inr v)
  let τG := τ.comp a.toMonoidHom
  let : MeasurableSpace (PlaceGroupPoints F G (.inr v)) := borel _
  let : BorelSpace (PlaceGroupPoints F G (.inr v)) := ⟨rfl⟩
  let : LocallyCompactSpace (PlaceGroupPoints F G (.inr v)) :=
    a.toHomeomorph.locallyCompactSpace_iff.mpr (hLC v)
  let : TotallyDisconnectedSpace (GeneralLinear (r + 1) (v.adicCompletion F)) := hTD v
  let : TotallyDisconnectedSpace (PlaceGroupPoints F G (.inr v)) :=
    a.toHomeomorph.symm.totallyDisconnectedSpace
  have hτGI := (isIrreducible_comp_continuousMulEquiv_iff τ a).2 hτI
  have hτGA := (isAdmissible_comp_continuousMulEquiv_iff τ a).2 hτsc.1
  let j₀ := P.subtype.comp tv
  have hj₀ : j₀ ≠ 0 := by
    intro h
    apply htv
    apply LinearMap.ext
    intro x
    exact Subtype.ext (DFunLike.congr_fun h x)
  have hj₀P : LinearMap.range j₀ ≤ P := fun _ ⟨x, hx⟩ => hx ▸ (tv x).property
  have hj₀e (y : PlaceGroupPoints F G (.inr v)) (x : V v) :
      j₀ (τG y x) = πc (ofPlace F G (.inr v) y) (j₀ x) := by
    have ht := htvEq (a y) x
    change j₀ (τ (a y) x) = πc (ofPlace F G (.inr v) (a.symm (a y))) (j₀ x) at ht
    change j₀ (τ (a y) x) = _
    simpa only [a.symm_apply_apply] using ht
  obtain ⟨b⟩ := presentedLocalComponentEquivOfHilbertOccurrence F r hPD T i hi I e hc P hPinv hPirr
    R Φ hΦ hΦP D v (hD v).1 τG hτGA hτGI j₀ hj₀ hj₀P hj₀e
  let c : (D.localComponent v).representation.Equiv τ :=
    Representation.Equiv.mk b.toLinearEquiv (fun g => by
      apply LinearMap.ext
      intro x
      have ht := Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap (a.symm g) x
      change b ((D.localComponent v).representation (a (a.symm g)) x) =
        τ (a (a.symm g)) (b x) at ht
      change b ((D.localComponent v).representation g x) = τ g (b x)
      simpa only [a.apply_symm_apply] using ht)
  refine ⟨LocalRealization.isSupercuspidal_of_matrixAction v _ (hD v).1
    (isSupercuspidal_of_equiv c.symm hτsc), ξ, ?_, ?_⟩
  · simpa only [hξeq] using hξ
  · rw [hξeq]
    exact ⟨c.symm⟩

end Global

end Langlands.BaseChange

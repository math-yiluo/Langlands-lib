import Langlands.Automorphic.TranslatedBlockLeviOperators
import Langlands.Automorphic.CuspidalCentralCharacterRealization
import Langlands.Automorphic.HeckeTwist.ContragredientTwist

/-! # Levi slices in an actual fixed-character cuspidal realization -/

noncomputable section
universe u
open NumberField
open scoped Classical
set_option autoImplicit false
set_option quotPrecheck false

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL Langlands.GeneralLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}

local instance cuspLeviCoefficientRationalGroup (d : ℕ) : AddCommGroup (RationalInvariantFunctions F d) :=
  Submodule.addCommGroup _
local instance cuspLeviCoefficientContinuousGroup (d : ℕ) : AddCommGroup (ContinuousRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance cuspLeviCoefficientSmoothGroup (d : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance cuspLeviCoefficientFormGroup (d : ℕ) : AddCommGroup (AutomorphicForms F d) :=
  Submodule.addCommGroup _
local instance cuspLeviCoefficientStableGroup (d : ℕ) : AddCommGroup (StableAutomorphicFunctions F d) :=
  Submodule.addCommGroup _
local instance cuspLeviCoefficientRealizationGroup {d : ℕ} (W : OperatorRealization F d) : AddCommGroup W.Space :=
  Submodule.addCommGroup _
local instance cuspLeviCoefficientOperatorRing (d : ℕ) : Ring (automorphicOperatorAlgebra F d) :=
  Subalgebra.toRing _

/-- Include an operator realization in the actual finite-smooth function carrier. -/
def OperatorRealization.finiteSmoothAmbient {d : ℕ} (W : OperatorRealization F d) :
    W.Space →ₗ[ℂ] FiniteSmoothRationalFunctions F d :=
  (automorphicOperatorCore F d).toSubmodule.subtype.comp W.toSubmodule.subtype

theorem OperatorRealization.finiteSmoothAmbient_injective {d : ℕ} (W : OperatorRealization F d) :
    Function.Injective (W.finiteSmoothAmbient F) :=
  Subtype.val_injective.comp Subtype.val_injective

variable (B : BlockShape n) (S : OperatorRealization F n)
  {C : Type*} [AddCommGroup C] [Module ℂ C]
  (j : C →ₗ[ℂ] TranslatedBlockConstantTerms F B S)
  (i : Fin B.length)

local notation "M" => AdelicBlockParabolic.FullLevi F B
local notation "d" => B.size i
local notation "V" => FiniteSmoothRationalFunctions F d
local notation "L" => translatedBlockLeviSlice F B S i
local notation "α" => translatedBlockTermOperatorAction F B S
local notation "ρ" => translatedBlockTermFiniteAction F B S

/-- Slice maps into an actual operator realization and their equality with the evaluated period. -/
abbrev RealizedBlockLeviSlices (W : OperatorRealization F d) :=
  { slice : M → C →ₗ[ℂ] W.Space // ∀ (m : M) (w : C),
    W.finiteSmoothAmbient F (slice m w) = L m (j w) }

section Character

variable [CompactSpace (AdeleQuotient F)] (ω : HeckeCharacter F)

local notation "W₀" => centralCharacterCuspidalOperatorRealization F d ω

set_option maxHeartbeats 550000 in
/-- The actual coordinate slices lie in the cuspidal realization at the restricted character. -/
def realizedBlockLeviSlices_of_character
    (χ : (Fin B.length → Ideles F) →* ℂˣ)
    (hχ : ∀ (w : C) z, translatedFunctionAction (blockConstantTermScalarAction F B)
      (realizedBlockConstantTerm F B S) z (j w) = (χ z : ℂ) • j w)
    (hω : ∀ z : Ideles F, ω.onIdeles z = χ (Pi.mulSingle i z))
    (href : ∀ (f : S.Space) (t : Finset (Fin (n - 1))), B.cuts ⊂ t →
      finiteSmoothBlockConstantTerm F (standardBlockWeight t) (S.ambient f) = 0) :
    RealizedBlockLeviSlices F B S j i W₀ := by
  let a (m : M) : C →ₗ[ℂ] V := (L m).comp j
  have ha (m : M) (w : C) : a m w ∈ (automorphicOperatorCore F d).toSubmodule := by
    rw [automorphicOperatorCore_eq F d]
    exact (mem_automorphicSubrepresentation F d _).mpr
      (translatedBlockLeviSlice_isAutomorphic F B S i m (j w))
  let b (m : M) := (a m).codRestrict (automorphicOperatorCore F d).toSubmodule (ha m)
  have hb (m : M) (w : C) : b m w ∈ W₀ := by
    refine (mem_centralCharacterCuspidalOperatorRealization F d ω (b m w)).mpr ⟨?_, ?_⟩
    · intro z x
      let e := finiteSmoothFunctionEvaluation F d (a m w)
      change e (AdelicGL.scalar F d z * x) = (ω.onIdeles z : ℂ) * e x
      have he := translatedBlockLeviSlice_scalar F B S i χ (j w)
        (hχ w) m z x
      exact (congrArg e (AdelicGL.scalar_commute F d z x).eq).trans
        (he.trans (congrArg (fun c : ℂˣ => (c : ℂ) * e x) (hω z).symm))
    · exact translatedBlockLeviSlice_isCuspidal F B S i href m (j w)
  exact ⟨fun m => (b m).codRestrict (W₀).toSubmodule (hb m), fun _ _ => rfl⟩

end Character

namespace RealizedBlockLeviSlices

variable {F B S j i} {W : OperatorRealization F (B.size i)}

local notation "R" => RealizedBlockLeviSlices F B S j i W

/-- The linear map at a chosen Levi argument. -/
def slice (D : R) (m : M) : C →ₗ[ℂ] W.Space := D.val m

theorem ambient_slice (D : R) (m : M) (w : C) :
    W.finiteSmoothAmbient F (D.slice m w) = L m (j w) := D.property m w

section Actions

variable {A : automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ C}
  (hj : ∀ (a : automorphicOperatorAlgebra F n) (w : C),
    j (A a w) = translatedBlockTermOperatorAction F B S a (j w))

include hj in
set_option maxHeartbeats 550000 in
/-- The slice in the realization respects the embedded finite operator. -/
theorem finite (D : R) (m : M) (b : FiniteAdelicGL F d) (w : C) :
    D.slice m (A (finiteOperator F n (blockShapeFiniteBlockEmbedding F B i b)) w) =
      W.finiteRepresentation b (D.slice m w) := by
  apply W.finiteSmoothAmbient_injective F
  calc
    _ = L m (ρ (blockShapeFiniteBlockEmbedding F B i b) (j w)) := (D.ambient_slice _ _).trans
      (congrArg (L m) (hj
        (finiteOperator F n (blockShapeFiniteBlockEmbedding F B i b)) w))
    _ = finiteSmoothFiniteRightAction F d b (L m (j w)) :=
      translatedBlockLeviSlice_finite F B S i m b (j w)
    _ = _ := congrArg (finiteSmoothFiniteRightAction F d b) (D.ambient_slice m w).symm

include hj in
set_option maxHeartbeats 550000 in
/-- The slice in the realization respects the embedded compact operator. -/
theorem compact (D : R) (m : M) (k : standardInfiniteCompact F d) (w : C) :
    D.slice m (A (compactOperator F n (blockShapeInfiniteCompactEmbedding B F i k)) w) =
      W.compactRepresentation k (D.slice m w) := by
  apply W.finiteSmoothAmbient_injective F
  calc
    _ = L m (α (compactOperator F n (blockShapeInfiniteCompactEmbedding B F i k)) (j w)) :=
      (D.ambient_slice _ _).trans (congrArg (L m) (hj
        (compactOperator F n (blockShapeInfiniteCompactEmbedding B F i k)) w))
    _ = finiteSmoothCompactRightAction F d k (L m (j w)) :=
      translatedBlockLeviSlice_compact F B S i m k (j w)
    _ = _ := congrArg (finiteSmoothCompactRightAction F d k) (D.ambient_slice m w).symm

include hj in
set_option maxHeartbeats 550000 in
/-- The slice in the realization respects the embedded real Lie action. -/
theorem realLie (D : R) (m : M) (X : RealLieAlgebra F d) (w : C) :
    D.slice m (A (differentialOperator F n (envelopingGenerator F n
      (complexify F n (blockShapeRealLieInclusion F B i X)))) w) = W.lieAction X (D.slice m w) := by
  apply W.finiteSmoothAmbient_injective F
  calc
    _ = L m (α (differentialOperator F n (envelopingGenerator F n
        (complexify F n (blockShapeRealLieInclusion F B i X)))) (j w)) :=
      (D.ambient_slice _ _).trans (congrArg (L m) (hj
        (differentialOperator F n (envelopingGenerator F n
          (complexify F n (blockShapeRealLieInclusion F B i X)))) w))
    _ = finiteSmoothEnvelopingAction F d (envelopingGenerator F d (complexify F d X)) (L m (j w)) :=
      translatedBlockLeviSlice_realGenerator F B S i m X (j w)
    _ = _ := congrArg (finiteSmoothEnvelopingAction F d (envelopingGenerator F d (complexify F d X)))
      (D.ambient_slice m w).symm

end Actions

/-- The slice after actual determinant multiplication in the chosen block. -/
def twistedSlice (D : R) (μ : HeckeCharacter F) (m : M) : C →ₗ[ℂ] (W.heckeDeterminantTwist μ).Space :=
  (W.heckeDeterminantTwistEquiv μ).toLinearMap.comp (D.slice m)

set_option maxHeartbeats 550000 in
/-- Evaluation of the twisted slice is multiplication by the actual determinant character. -/
theorem twistedSlice_evaluation (D : R) (μ : HeckeCharacter F) (m : M) (w : C) (x : AdelicGL F d) :
    ContinuousRationalFunctions.evaluate F d
      ((W.heckeDeterminantTwist μ).toContinuous (D.twistedSlice μ m w)) x =
      (μ.adelicDeterminant d x : ℂ) * translatedBlockLeviRestriction F B S (j w) (Function.update m i x) := by
  calc
    _ = (μ.adelicDeterminant d x : ℂ) *
        finiteSmoothFunctionEvaluation F d (W.finiteSmoothAmbient F (D.slice m w)) x :=
      W.evaluate_heckeDeterminantTwistEquiv μ (D.slice m w) x
    _ = (μ.adelicDeterminant d x : ℂ) * finiteSmoothFunctionEvaluation F d (L m (j w)) x :=
      congrArg (fun a : V => (μ.adelicDeterminant d x : ℂ) * finiteSmoothFunctionEvaluation F d a x)
        (D.ambient_slice m w)
    _ = _ := congrArg ((μ.adelicDeterminant d x : ℂ) * ·)
      (translatedBlockLeviSlice_evaluation F B S i m (j w) x)

set_option maxHeartbeats 550000 in
/-- The ambient function underlying the twisted slice is the actual multiplied slice. -/
theorem ambient_twistedSlice (D : R) (μ : HeckeCharacter F) (m : M) (w : C) :
    (W.heckeDeterminantTwist μ).finiteSmoothAmbient F (D.twistedSlice μ m w) =
      FiniteSmoothRationalFunctions.heckeDeterminantMultiplier d μ (L m (j w)) :=
  congrArg (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier d μ) (D.ambient_slice m w)

end RealizedBlockLeviSlices

end Langlands.Automorphic

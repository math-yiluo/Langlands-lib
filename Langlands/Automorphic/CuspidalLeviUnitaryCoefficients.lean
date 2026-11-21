import Langlands.Automorphic.CuspidalLeviCoefficientTensor
import Langlands.Automorphic.CuspidalContragredientExistenceProof

/-! # The actual cuspidal Levi coefficients at unitary central character -/

noncomputable section
universe u
open NumberField
open scoped Classical
set_option autoImplicit false
set_option quotPrecheck false

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL Langlands.GeneralLinear FiniteVectors

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}

local instance unitaryLeviRationalGroup (d : ℕ) : AddCommGroup (RationalInvariantFunctions F d) :=
  Submodule.addCommGroup _
local instance unitaryLeviContinuousGroup (d : ℕ) : AddCommGroup (ContinuousRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance unitaryLeviSmoothGroup (d : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance unitaryLeviStableGroup (d : ℕ) : AddCommGroup (StableAutomorphicFunctions F d) :=
  Submodule.addCommGroup _
local instance unitaryLeviFormGroup (d : ℕ) : AddCommGroup (AutomorphicForms F d) := Submodule.addCommGroup _
local instance unitaryLeviRealizationGroup {d : ℕ} (W : OperatorRealization F d) : AddCommGroup W.Space :=
  Submodule.addCommGroup _
local instance unitaryLeviOperatorRing (d : ℕ) : Ring (automorphicOperatorAlgebra F d) :=
  Subalgebra.toRing _

variable (B : BlockShape n) (ω : Fin B.length → HeckeCharacter F)

local notation "I" => Fin B.length

/-- The determinant twist making each prescribed block character unitary. -/
def cuspidalLeviUnitarizingTwist (i : I) : HeckeCharacter F :=
  unitarizingCharacter (B.size i - 1) (ω i)

local notation "μ" => cuspidalLeviUnitarizingTwist F B ω

/-- The central character of the unitarized block. -/
def cuspidalLeviUnitaryCharacter (i : I) : HeckeCharacter F := μ i ^ B.size i * ω i

local notation "ω₁" => cuspidalLeviUnitaryCharacter F B ω

theorem cuspidalLeviUnitaryCharacter_isUnitary (i : I) : (ω₁ i).IsUnitary := by
  intro z
  have hd : B.size i - 1 + 1 = B.size i := Nat.sub_add_cancel (Nat.succ_le_iff.mpr (B.positive i))
  have h := norm_unitarizingCharacter_pow_mul (B.size i - 1) (ω i) z
  change ‖((μ i ^ (B.size i - 1 + 1) * ω i) z : ℂ)‖ = 1 at h
  rw [hd] at h
  exact h

variable [CompactSpace (AdeleQuotient F)]

local notation "W" => fun i : I => centralCharacterCuspidalOperatorRealization F (B.size i) (ω i)

/-- The actual fixed-character cuspidal realization after determinant multiplication. -/
def cuspidalLeviUnitaryRealization (i : I) : OperatorRealization F (B.size i) :=
  ((W) i).heckeDeterminantTwist (μ i)

local notation "W₁" => cuspidalLeviUnitaryRealization F B ω

theorem cuspidalLeviUnitaryRealization_isCuspidal (i : I) : (W₁ i).IsCuspidal :=
  (((W) i).heckeDeterminantTwist_isCuspidal_iff (μ i)).mpr
    (centralCharacterCuspidalOperatorRealization_isCuspidal F (B.size i) (ω i))

set_option maxHeartbeats 550000 in
theorem cuspidalLeviUnitaryRealization_hasCentralCharacter (i : I) : (W₁ i).HasCentralCharacter (ω₁ i) := by
  change (((W) i).heckeDeterminantTwist (μ i)).toFiniteRealization.HasCentralCharacter (ω₁ i)
  rw [OperatorRealization.toFiniteRealization_heckeDeterminantTwist]
  exact (((W) i).toFiniteRealization.heckeDeterminantTwist_hasCentralCharacter (μ i) (ω i))
    (centralCharacterCuspidalOperatorRealization_hasCentralCharacter F (B.size i) (ω i))

local instance unitaryLeviBlockGroups : ∀ i : I, AddCommGroup (W₁ i).Space :=
  fun _ => Submodule.addCommGroup _

variable (S : OperatorRealization F n)
  {C : Type*} [AddCommGroup C] [Module ℂ C]
  (j : C →ₗ[ℂ] TranslatedBlockConstantTerms F B S)
  (A : automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ C)

local notation "ρc" => (AlgHom.toMonoidHom' A).comp (compactOperator F n)
local notation "rOp" => fun (X : RealLieAlgebra F n) => differentialOperator F n
  (envelopingGenerator F n (complexify F n X))
local notation "M" => AdelicBlockParabolic.FullLevi F B
local notation "V" => PiTensorProduct ℂ (fun i : I => (W₁ i).Space)
local notation "e" => fun i : I => (W₁ i).coefficientEvaluation F

set_option maxHeartbeats 1000000 in
/-- After unitarizing the block characters, the actual Levi coefficients are linear tensors
with the evaluated restriction and the genuine single-block derivative. -/
theorem exists_unitaryCuspidalLeviCoefficients
    (hj : ∀ (a : automorphicOperatorAlgebra F n) w,
      j (A a w) = translatedBlockTermOperatorAction F B S a (j w))
    (hκ : ∀ w : C, IsFiniteVector ρc w)
    (η : (Fin B.length → Ideles F) →* ℂˣ)
    (hη : ∀ (w : C) z, translatedFunctionAction (blockConstantTermScalarAction F B)
      (realizedBlockConstantTerm F B S) z (j w) = (η z : ℂ) • j w)
    (hω : ∀ i (z : Ideles F), (ω i).onIdeles z = η (Pi.mulSingle i z))
    (href : ∀ (f : S.Space) (t : Finset (Fin (n - 1))), B.cuts ⊂ t →
      finiteSmoothBlockConstantTerm F (standardBlockWeight t) (S.ambient f) = 0) :
    ∃ g : C →ₗ[ℂ] V,
      (∀ w (m : M), functionTensorEvaluation e (g w) m = twistedLeviCoefficient F B S j μ w m) ∧
      ∀ (i : I) (X : RealLieAlgebra F (B.size i)) w, ∃ c : ℂ,
        g (A ((rOp) (blockShapeRealLieInclusion F B i X)) w) =
          tensorCoordinateEnd i ((W₁ i).complexLieAction (complexify F (B.size i) X)) (g w) + c • g w := by
  let D (i : I) : RealizedBlockLeviSlices F B S j i ((W) i) :=
    realizedBlockLeviSlices_of_character F B S j i (ω i) η hη (hω i) href
  obtain ⟨g, hg⟩ := exists_twistedLeviCoefficientTensor D A hj hκ
    (cuspidalLeviUnitaryRealization_isCuspidal F B ω) ω₁ (cuspidalLeviUnitaryCharacter_isUnitary F B ω)
    (cuspidalLeviUnitaryRealization_hasCentralCharacter F B ω)
  exact ⟨g, hg, fun i X w => ⟨-OperatorRealization.heckeLieShift (μ i) X,
    twistedLeviTensor_realLie D A hj g hg i X w⟩⟩

end Langlands.Automorphic

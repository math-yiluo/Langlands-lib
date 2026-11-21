import Langlands.Global.Factors.CuspidalBlockPlaceCoefficients
import Langlands.Global.Factors.GroupedTensorScalarEvaluation

/-! # Translation of the realized scalar Levi coefficient tensor -/

noncomputable section

open scoped BigOperators Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 70000
set_option synthInstance.maxHeartbeats 40000

universe u uQ

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic FiniteAdelicGL AdelicBlockParabolic
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r k : ℕ} {m : Fin k → ℕ}
variable (hm : ∑ i, (m i + 1) = r + 1)
variable {T : ∀ i, CuspidalOperatorRealization F (m i)}
variable (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
variable (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))

local notation "B" => blockShape hm
local notation "D" => finiteReferences hm P
local notation "S" => (fun (i : Fin k) => CuspidalOperatorRealization.realization (T i))
local notation "CF" => (fun i : Fin k => BlockInducedReferences.BlockCoefficients D i)
local notation "CI" => (fun (p : InfinitePlaceFamily.Index F) (i : Fin k) =>
  InfiniteBlockCoefficient T i p)
local notation "E" => groupedCoefficientEquiv hm P h

private local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance {n : ℕ} (V : OperatorRealization F n) : AddCommGroup V.Space :=
  Submodule.addCommGroup _
private local instance {n : ℕ} {v : FinitePlace F} (V : LocalRealization F n v) : AddCommGroup V.Space :=
  Submodule.addCommGroup _
private local instance (i : Fin k) (p : InfinitePlaceFamily.Index F) : AddCommGroup (CI p i) :=
  Submodule.addCommGroup _

local notation "FinCoeff" => (⨂[ℂ] i, CF i)
local notation "InfCoeff" => (⨂[ℂ] p, InfinitePlaceCoefficients T p)

/-- Evaluate the realized grouped Levi coefficient at one scalar argument. -/
def groupedCoefficientEvaluation (z : FullLevi F B) : FinCoeff ⊗[ℂ] InfCoeff →ₗ[ℂ] ℂ :=
  (LinearMap.proj z).comp ((AdelicBlockScalarSections.coefficientValues F B S).subtype.comp
    (groupedCoefficientEquiv hm P h).toLinearMap)

/-- The scalar factor of a pure grouped coefficient from a single cuspidal block. -/
def groupedBlockValue (z : FullLevi F B) (i : Fin k) (a : CF i) (c : ∀ p, CI p i) : ℂ :=
  let V := S i
  let f := blockVectorEquiv hm P h i (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ c)
  ContinuousRationalFunctions.evaluate F (m i + 1) (V.toContinuous f) (z i)

theorem groupedCoefficientEvaluation_pure (z : FullLevi F B) (a : ∀ i, CF i) (c : ∀ p i, CI p i) :
    groupedCoefficientEvaluation hm P h z (groupedPure a c) =
      ∏ i, groupedBlockValue hm P h z i (a i) (fun p => c p i) :=
  groupedCoefficientEquiv_tprod hm P h a c z

private abbrev finiteCoefficientOperator (d : FiniteLevi F B) (i : Fin k) : Module.End ℂ (CF i) :=
  BlockInducedReferences.blockRepresentation D i (d i)

private theorem groupedBlockValue_finite (d : FiniteLevi F B) (z : FullLevi F B)
    (i : Fin k) (a : CF i) (c : ∀ p, CI p i) :
    groupedBlockValue hm P h z i (finiteCoefficientOperator hm P d i a) c =
      groupedBlockValue hm P h (z * leviPair F B 1 d) i a c := by
  let V := S i
  let q (f : V.Space) (g : AdelicGL F (m i + 1)) :=
    ContinuousRationalFunctions.evaluate F (m i + 1) (V.toContinuous f) g
  let b := PiTensorProduct.tprod ℂ c
  let f := blockVectorEquiv hm P h i (a ⊗ₜ[ℂ] b)
  have ha := blockVectorEquiv_finite hm P h i (d i) a b
  have hb := OperatorRealization.evaluate_finiteRepresentation V (d i) f (z i)
  have hz : (z * leviPair F B 1 d) i = z i * AdelicGL.ofFinite F (m i + 1) (d i) :=
    congrArg (fun g => z i * g) (AdelicGL.ofFinite_eq_pair F (m i + 1) (d i)).symm
  exact (congrArg (fun f => q f (z i)) ha).trans (hb.trans (congrArg (q f) hz.symm))

set_option maxHeartbeats 135000 in
/-- The finite right action on the grouped tensor is the original scalar
coefficient right translation at every adelic Levi point. -/
theorem groupedCoefficientEquiv_finite (d : FiniteLevi F B)
    (a : FinCoeff) (c : InfCoeff) (z : FullLevi F B) :
    groupedCoefficientEvaluation hm P h z (PiTensorProduct.map (finiteCoefficientOperator hm P d) a ⊗ₜ[ℂ] c) =
      groupedCoefficientEvaluation hm P h (z * leviPair F B 1 d) (a ⊗ₜ[ℂ] c) := by
  let z' : FullLevi F B := z * leviPair F B (1 : InfiniteLevi F B) d
  let L := @groupedCoefficientEvaluation F _ _ _ r k m hm T P h z
  let R := @groupedCoefficientEvaluation F _ _ _ r k m hm T P h z'
  let l := @groupedBlockValue F _ _ _ r k m hm T P h z
  let q := @groupedBlockValue F _ _ _ r k m hm T P h z'
  let α := @finiteCoefficientOperator F _ _ _ r k m hm T P d
  let structures {V : Type u} (add : AddCommMonoid V) (mod : @Module ℂ V _ add)
      (_ : @Module.End ℂ V _ add mod) : Σ a : AddCommMonoid V, @Module ℂ V _ a :=
    ⟨add, mod⟩
  let finite (i : Fin k) := structures _ _ (α i)
  let infiniteAdd (p : InfinitePlaceFamily.Index F) (i : Fin k) : AddCommMonoid (CI p i) :=
    Submodule.addCommMonoid (CI p i)
  let infiniteModule (p : InfinitePlaceFamily.Index F) (i : Fin k) :
      @Module ℂ (CI p i) _ (infiniteAdd p i) := Submodule.module (CI p i)
  let indexFinite : Finite (InfinitePlaceFamily.Index F) := inferInstance
  exact @groupedProductCovariance_first (Fin k) (InfinitePlaceFamily.Index F) CF CI
    (fun i => (finite i).1) (fun i => (finite i).2) infiniteAdd infiniteModule
    (Fin.fintype k) indexFinite α L R l q
    (@groupedCoefficientEvaluation_pure F _ _ _ r k m hm T P h z)
    (@groupedCoefficientEvaluation_pure F _ _ _ r k m hm T P h z')
    (@groupedBlockValue_finite F _ _ _ r k m hm T P h d z) a c

end Langlands.Global.CuspidalBlockInduction

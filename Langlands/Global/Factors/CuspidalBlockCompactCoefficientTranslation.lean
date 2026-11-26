import Langlands.Global.Factors.CuspidalBlockCoefficientCovariance
import Langlands.Global.Factors.CuspidalBlockCompactCoefficients
import Langlands.Global.FiniteAdelicGL.BlockEvaluationRegrouping

/-! # Translation of cuspidal coefficients by the compact Levi -/

noncomputable section

open scoped BigOperators Classical TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 130000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 90000

universe u uQ

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic FiniteAdelicGL AdelicBlockParabolic InfinitePlaceFamily
open AdelicBlockScalarSections AdelicBlockDeterminantCharacter
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r k : ℕ} {m : Fin k → ℕ} (hm : ∑ i, (m i + 1) = r + 1)
variable {T : ∀ i, CuspidalOperatorRealization F (m i)}
variable (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
variable (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))

local notation "B" => blockShape hm
local notation "D" => finiteReferences hm P
local notation "S" => (fun i : Fin k => CuspidalOperatorRealization.realization (T i))
local notation "CF" => (fun i : Fin k => BlockInducedReferences.BlockCoefficients D i)
local notation "CI" => (fun (p : Index F) (i : Fin k) => InfiniteBlockCoefficient T i p)

private local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance {n : ℕ} (V : OperatorRealization F n) : AddCommGroup V.Space := Submodule.addCommGroup _
private local instance (p : Index F) (i : Fin k) : AddCommGroup (CI p i) := Submodule.addCommGroup _

local notation "FinCoeff" => (⨂[ℂ] i, CF i)
local notation "InfCoeff" => (⨂[ℂ] p, InfinitePlaceCoefficients T p)
local notation "ev" => groupedCoefficientEvaluation hm P h

private theorem groupedBlockValue_compact
    (d : ∀ i : Fin k, standardInfiniteCompact F (m i + 1)) (z : FullLevi F B)
    (i : Fin k) (a : CF i) (c : ∀ p, CI p i) :
    groupedBlockValue hm P h z i a (fun p => (T i).placeDensityModels.sourceCompact p
      (infiniteCompactCoordinates F _ (d i) p) (c p)) =
      groupedBlockValue hm P h (z * leviPair F B (fun j => (d j).val) 1) i a c := by
  let Q := S i
  let value (f : Q.Space) (g : AdelicGL F (m i + 1)) :=
    ContinuousRationalFunctions.evaluate F (m i + 1) (Q.toContinuous f) g
  let f := blockVectorEquiv hm P h i (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ c)
  have hblock := blockVectorEquiv_compact_tprod hm P h i (d i) a c
  have htranslate := Q.evaluate_compactRepresentation (d i) f (z i)
  have hpoint : (z * leviPair F B (fun j => (d j).val) 1) i =
      z i * AdelicGL.ofInfinite F (m i + 1) (d i).val :=
    congrArg (z i * ·) (AdelicGL.ofInfinite_eq_pair F (m i + 1) (d i).val).symm
  exact (congrArg (fun y => value y (z i)) hblock).trans
    (htranslate.trans (congrArg (value f) hpoint.symm))

/-- Translating the infinite coefficient tensor by block compact elements is
actual scalar right translation at the full adelic Levi argument. -/
theorem groupedCoefficientEquiv_compact
    (d : ∀ i : Fin k, standardInfiniteCompact F (m i + 1))
    (a : FinCoeff) (c : InfCoeff) (z : FullLevi F B) :
    ev z (a ⊗ₜ[ℂ] infiniteCoefficientCompactMap T d c) =
      ev (z * leviPair F B (fun i => (d i).val) 1) (a ⊗ₜ[ℂ] c) := by
  let z' := z * leviPair F B (fun i => (d i).val) 1
  let β (p : Index F) (i : Fin k) := (T i).placeDensityModels.sourceCompact p
    (infiniteCompactCoordinates F _ (d i) p)
  exact groupedProductCovariance_second β (ev z) (ev z')
    (groupedBlockValue hm P h z) (groupedBlockValue hm P h z')
    (groupedCoefficientEvaluation_pure hm P h z) (groupedCoefficientEvaluation_pure hm P h z')
    (groupedBlockValue_compact hm P h d z) a c

local notation "LocalSpace" => (fun w (i : Fin k) => ((P i).localComponent w).Space)
local notation "LocalGroup" => (fun w (i : Fin k) => Submodule.addCommGroup (LocalSpace w i))
local notation "LocalModule" => (fun w (i : Fin k) => Submodule.module (LocalSpace w i))

/-- Evaluate the finite inducing tensor in the grouped local coefficients. -/
abbrev finiteBlockEvaluation :=
  @BlockInducedReferences.blockEvaluation F _ _ (r + 1) B LocalSpace LocalGroup LocalModule
    (finiteBlockAction P) D (finiteReferences_blockReference_ne_zero hm P)

end Langlands.Global.CuspidalBlockInduction

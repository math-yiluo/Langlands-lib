import Langlands.Automorphic.TransposeOperatorRealization
import Langlands.Global.RankinSelberg.CuspidalTransposeInverseContragredientReduction

/-! # Reduction to the pairing of the actual cuspidal transpose realization -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open NumberField Langlands.Automorphic

local instance transposePairingReductionRationalGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance transposePairingReductionContinuousGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance transposePairingReductionSmoothGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance transposePairingReductionFormsGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance transposePairingReductionStableGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance transposePairingReductionSpaceGroup
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    {r : ℕ} (T : CuspidalOperatorRealization F r) :
    AddCommGroup T.Space := Submodule.addCommGroup _

section Concrete

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    {r : ℕ} (T : CuspidalOperatorRealization F r)

/-- The actual transpose equivalence intertwines all three operator families. -/
theorem cuspidalTransposeEquiv_isTransposeIntertwining :
    T.realization.IsTransposeIntertwining T.transpose.realization T.transposeEquiv :=
  ⟨T.transposeEquiv_finite, T.transposeEquiv_compact, T.transposeEquiv_lieAction⟩

/-- The actual transpose vector has exactly the dual cusp function of the source vector. -/
theorem cuspFunction_transposeEquiv (x : T.Space) :
    cuspFunction F T.transpose (T.transposeEquiv x) =
      dualFunction F (r + 1) (cuspFunction F T x) :=
  cuspFunction_eq_dualFunction_of_transposeDual F T T.transpose x (T.transposeEquiv x)
    ((T.toContinuous_transposeEquiv x).trans (continuousTranspose_eq_transposeDual _))

/-- The remaining contragredient identification is precisely the intrinsic pairing condition. -/
theorem cuspidalTranspose_isContragredientOf_iff :
    T.transpose.realization.IsContragredientOf T.realization ↔
      T.realization.HasTransposeContragredientPairing :=
  (cuspidalTransposeEquiv_isTransposeIntertwining T).isContragredientOf_iff

end Concrete

/-- B1 is realized by the actual cuspidal transpose image, with no additional premise. -/
theorem cuspidalTransposeRealization : CuspidalTransposeRealizationStatement.{u} := by
  intro F _ _ _ r T
  refine ⟨T.transpose, T.transposeEquiv,
    cuspidalTransposeEquiv_isTransposeIntertwining T, ?_⟩
  intro x
  exact (T.toContinuous_transposeEquiv x).trans (continuousTranspose_eq_transposeDual _)

/-- Only B2, the intrinsic full-operator transpose pairing, remains as an open premise. -/
def CuspidalTransposePairingReductionStatement : Prop :=
  CuspidalTransposePairingStatement.{u} →
    CuspidalTransposeInverseContragredientStatement.{u}

/-- The actual transpose realization discharges B1 in the earlier conditional reduction. -/
theorem cuspidalTransposePairingReduction :
    CuspidalTransposePairingReductionStatement.{u} :=
  cuspidalTransposeInverseContragredientReduction cuspidalTransposeRealization

end Langlands.Global.RankinSelbergGlobal

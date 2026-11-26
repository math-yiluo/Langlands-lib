import Langlands.Global.Factors.CuspidalBlockFiniteEvaluation

/-! # Bundled evaluation in grouped finite Levi coefficients -/

noncomputable section

open scoped BigOperators Classical TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true

universe u uQ

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic FiniteAdelicGL GeneralLinear AdelicBlockParabolic AdelicBlockDeterminantCharacter

section FiniteEvaluation

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} {B : BlockShape n}
variable {V : FinitePlace F → Fin B.length → Type u}
variable [∀ v i, AddCommGroup (V v i)] [∀ v i, Module ℂ (V v i)]
variable {σ : ∀ v i, Representation ℂ (FiniteLocalGL F (B.size i) v) (V v i)}
variable (D : BlockInducedReferences F B σ)
variable (hD : ∀ w ∉ D.exceptional, ∀ i, D.blockReference w i ≠ 0)

local notation "Vf" => (⨂[ℂ] i, D.BlockCoefficients i)
local notation "Gf" => FiniteAdelicGL F n
local notation "Pf" => AdelicBlockParabolic.Finite F B
local notation "Kf" => ↥(FiniteAdelicGL.standardIntegral F n)

/-- The ordinary finite Levi representation on the tensor grouped by block. -/
abbrev groupedFiniteLeviAction : Representation ℂ (FiniteLevi F B) Vf :=
  FiniteTensor.external D.blockRepresentation

/-- The additive group inherited from the restricted block factors. -/
abbrev groupedFiniteCoefficientGroup : AddCommGroup Vf := inferInstance

/-- Package the finite inducing evaluation in its restricted Levi coefficients
with its right, parabolic and compact separation laws. -/
def groupedFiniteEvaluation :
    @FiniteEvaluationData Gf (FiniteLevi F B) Pf Kf D.Source Vf
      _ _ _ _ (groupedFiniteCoefficientGroup D) _ D.sourceRepresentation (groupedFiniteLeviAction D)
      (fun p g => p.val * g)
      (fun p => parabolicHalfCharacter F B (ofFinite F B p))
      (B.leviProjection (FiniteAdeles F)) Subtype.val where
  evaluate := D.blockEvaluation hD
  right := D.blockEvaluation_right hD
  parabolic := D.blockEvaluation_parabolic hD
  compact_injective := D.blockEvaluation_compact_injective hD

end FiniteEvaluation

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r k : ℕ} {m : Fin k → ℕ} (hm : ∑ i, (m i + 1) = r + 1)
variable {T : ∀ i, CuspidalOperatorRealization F (m i)}
variable (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))

attribute [local instance] LocalRealization.localRealizationSpaceAddCommGroup

/-- Use the compatible section and coefficient references obtained from the
cuspidal spectral presentations. -/
def cuspidalGroupedFiniteEvaluation :=
  groupedFiniteEvaluation (finiteReferences hm P) (finiteReferences_blockReference_ne_zero hm P)

end Langlands.Global.CuspidalBlockInduction

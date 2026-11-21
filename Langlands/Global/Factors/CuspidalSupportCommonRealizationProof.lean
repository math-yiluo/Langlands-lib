import Langlands.Automorphic.CuspidalSupportSelectedPeriod
import Langlands.Global.Factors.CuspidalSupportCommonRealization
import Langlands.Global.Factors.CuspidalSupportPeriodGK

/-! # A common cuspidal realization from the actual selected period -/

noncomputable section

open scoped BigOperators Classical TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxHeartbeats 60000
set_option maxHeartbeats 220000

universe u

namespace Langlands.Global

open Langlands.Automorphic Langlands.GeneralLinear ArchimedeanGL FiniteParametrizedBlockInduction
open FiniteVectors

variable {F : Type u} [Field F] [NumberField F]

attribute [local instance] subquotientRationalGroup subquotientContinuousGroup
  subquotientSmoothGroup subquotientFormGroup subquotientStableGroup subquotientRealizationGroup

local instance selectedPeriodRealizationOperatorRing (d : ℕ) :
    Ring (automorphicOperatorAlgebra F d) := Subalgebra.toRing _

attribute [local instance 100] LieRing.ofAssociativeRing

section CyclicPeriod

variable {r c : ℕ} {m : Fin c → ℕ} (hm : ∑ i, (m i + 1) = r + 1)
  (S : OperatorRealization F (r + 1)) (Q : IrreducibleOperatorSubquotient F r)

local notation "N" => r + 1
local notation "B" => (⟨c, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩ : BlockShape N)
local notation "U" => automorphicOperatorAlgebra F N
local notation "α" => translatedBlockTermOperatorAction F B S
local notation "β" => blockConstantTermScalarAction F B
local notation "φ" => realizedBlockConstantTerm F B S

variable (v : TranslatedBlockConstantTerms F ⟨c, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩ S)

local notation "C" => BlockTermCyclicSpace F B S v
local notation "A" => blockTermCyclicAction F B S v
local notation "j" => blockTermCyclicInclusion F B S v
local notation "v₀" => blockTermCyclicGenerator F B S v
local notation "σ" => translatedFunctionAction β φ
local notation "ρf" => (AlgHom.toMonoidHom' A).comp (finiteOperator F N)

include v

private theorem selectedPeriod_regularCompact :
    HasRegularCompactOperatorAction (F := F) (n := N) (W := C) A := by
  exact ⟨fun w => blockTermCyclic_compactFinite F B S v w,
    blockTermCyclic_weaklyContinuousOrbits F B S v,
    blockTermCyclic_compactDualDerivative F B S v⟩

variable [CompactSpace (AdeleQuotient F)]

private theorem commonRealization_of_cyclicPeriod
    (χ : (Fin c → Ideles F) →ₜ* ℂˣ)
    (q : Representation.IntertwiningMap (AlgHom.toMonoidHom' A) Q.representation)
    (hq : Function.Surjective q)
    (hχ : ∀ z : Fin c → Ideles F, σ z v = (χ z : ℂ) • v)
    (hp : ∀ a : Fin c → Fˣ, χ (fun i => diagonalUnits F (a i)) = 1)
    (href : ∀ (w : S.Space) (t : Finset (Fin r)), (B).cuts ⊂ t →
      finiteSmoothBlockConstantTerm F (standardBlockWeight (n := N) t) (S.ambient w) = 0) :
    HasRestoredCuspidalIdentityRealization Q := by
  have hj : Function.Injective (j).toLinearMap := Subtype.val_injective
  have hji (a : U) (w : C) : (j).toLinearMap (A a w) = α a ((j).toLinearMap w) :=
    Representation.IntertwiningMap.isIntertwining _ _ j a w
  have hf : IsSmooth ρf := blockTermCyclic_finiteSmooth F B S v
  have hgen : orbitSpan (AlgHom.toMonoidHom' A) v₀ = ⊤ :=
    blockTermCyclicGenerator_orbitSpan F B S v
  have heigen (w : C) (z : Fin c → Ideles F) : σ z (j w) = (χ z : ℂ) • j w :=
    blockTermCyclic_eigen F B S v χ.toMonoidHom hχ w z
  exact commonRealization_of_selectedPeriod (W := C) hm Q S A q (j).toLinearMap hq hj hji
    (selectedPeriod_regularCompact hm S v) hf v₀ hgen χ heigen hp href

end CyclicPeriod

/-- Apply the actual selected period and its cusp-form factor decomposition. -/
theorem commonCuspidalRealization : CommonCuspidalRealizationStatement.{u} := by
  intro F _ _ _ r Q
  obtain ⟨c, m, hm, S, v, χ, q, hq, hχ, hp, href⟩ := exists_cuspidalSupportSelectedPeriod F Q
  exact commonRealization_of_cyclicPeriod hm S Q v χ q hq hχ hp href

/-- The common global construction reduces the exact assertion to real-place
parameters for the actual cuspidal factors. Complex parameters are already proved. -/
theorem cuspidalSupportEveryPlace_of_realCuspidalParameters
    (hParam : ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
      (r : ℕ) (T : CuspidalOperatorRealization F r) (v : {v : NumberField.InfinitePlace F // v.IsReal}),
      ∃ ds, T.realization.HasRealPlaceParameter v ds) : CuspidalSupportEveryPlaceStatement.{u} :=
  cuspidalSupportEveryPlace_of_commonRealization commonCuspidalRealization hParam

end Langlands.Global

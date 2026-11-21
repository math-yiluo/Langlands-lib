import Langlands.Automorphic.CompactDerivativeTransfer
import Langlands.Automorphic.TranslatedFunctionSpan
import Langlands.Global.AdelicBlockPeriodPlaceCompact
import Langlands.Global.AdelicBlockPeriodPlaceLie
import Langlands.Global.Factors.CuspidalSupportRestoredIdentity
import Langlands.Global.Factors.CuspidalSupportSourceGK
import Langlands.Representation.TensorProduct.ProductFunctionSlices

/-! # The source of a selected Levi coefficient after stable kernel descent -/

noncomputable section

open scoped BigOperators TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
set_option synthInstance.maxHeartbeats 120000

universe u

namespace Langlands.Global

open Langlands.Automorphic Langlands.GeneralLinear ArchimedeanGL FiniteParametrizedBlockInduction

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance supportKernelRationalGroup (d : ℕ) :
    AddCommGroup (RationalInvariantFunctions F d) := Submodule.addCommGroup _
local instance supportKernelContinuousGroup (d : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F d) := Submodule.addCommGroup _
local instance supportKernelSmoothGroup (d : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F d) := Submodule.addCommGroup _
local instance supportKernelFormGroup (d : ℕ) :
    AddCommGroup (AutomorphicForms F d) := Submodule.addCommGroup _
local instance supportKernelStableGroup (d : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F d) := Submodule.addCommGroup _
local instance supportKernelRealizationGroup {d : ℕ} (S : OperatorRealization F d) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance supportKernelOperatorRing (d : ℕ) :
    Ring (automorphicOperatorAlgebra F d) := Subalgebra.toRing _

attribute [local instance 100] LieRing.ofAssociativeRing

section CompactLaws

variable {W Y : Type u} [AddCommGroup W] [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]
  (A : automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ W)
  (A' : automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ Y)

private abbrev sourceLieForCompactLaws {V : Type u} [AddCommGroup V] [Module ℂ V]
    (L : automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ V) :
    ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ V :=
  ((L.comp (differentialOperator F n)).toLieHom).comp (envelopingGenerator F n)

local notation "κ" => A.toMonoidHom.comp (compactOperator F n)
local notation "κ'" => A'.toMonoidHom.comp (compactOperator F n)
local notation "D" => sourceLieForCompactLaws A
local notation "D'" => sourceLieForCompactLaws A'

/-- Full compact finiteness, scalar continuity and derivative compatibility for
an action of the actual automorphic operator algebra. -/
def HasRegularCompactOperatorAction : Prop :=
  (∀ w : W, FiniteVectors.IsFiniteVector κ w) ∧ HasWeaklyContinuousOrbits κ ∧ CompactDualDerivative κ D

variable (j : Representation.IntertwiningMap A.toMonoidHom A'.toMonoidHom)

private def fullCompactIntertwiner : Representation.IntertwiningMap κ κ' where
  toLinearMap := j.toLinearMap
  isIntertwining' k := j.isIntertwining' (compactOperator F n k)

private theorem fullCompactIntertwiner_lie (X : ComplexLieAlgebra F n) (x : W) :
    (fullCompactIntertwiner A A' j).toLinearMap (D X x) =
      D' X ((fullCompactIntertwiner A A' j).toLinearMap x) :=
  LinearMap.congr_fun (j.isIntertwining' (differentialOperator F n (envelopingGenerator F n X))) x

/-- A fully intertwined subsource inherits regularity of the full compact action. -/
theorem HasRegularCompactOperatorAction.of_injective_intertwiner
    (hj : Function.Injective j.toLinearMap) (h : HasRegularCompactOperatorAction A') :
    HasRegularCompactOperatorAction A := by
  let jK := fullCompactIntertwiner A A' j
  exact ⟨fun x => (FiniteVectors.isFiniteVector_map_iff jK hj x).mp (h.1 _),
    HasWeaklyContinuousOrbits.of_injective_intertwiner jK hj h.2.1,
    CompactDualDerivative.of_injective_intertwiner κ' D' h.2.2 jK hj
      (fullCompactIntertwiner_lie A A' j)⟩

/-- A fully intertwined quotient inherits regularity of the full compact action. -/
theorem HasRegularCompactOperatorAction.of_surjective_intertwiner
    (hj : Function.Surjective j.toLinearMap) (h : HasRegularCompactOperatorAction A) :
    HasRegularCompactOperatorAction A' := by
  let jK := fullCompactIntertwiner A A' j
  have he (k : standardInfiniteCompact F n) (x : W) :
      j.toLinearMap (κ k x) = κ' k (j.toLinearMap x) :=
    LinearMap.congr_fun (jK.isIntertwining' k) x
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := hj y
    exact (h.1 x).map jK
  · intro y μ
    obtain ⟨x, rfl⟩ := hj y
    exact (h.2.1 x (μ.comp j.toLinearMap)).congr fun k => congrArg μ (he k x)
  · intro X c hc0 hc μ y
    obtain ⟨x, rfl⟩ := hj y
    have hd := h.2.2 X c hc0 hc (μ.comp j.toLinearMap) x
    have ht (t : ℝ) : μ (κ' (c t) (j.toLinearMap x)) =
        (μ.comp j.toLinearMap) (κ (c t) x) := congrArg μ (he (c t) x).symm
    exact (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall ht)).congr_deriv
      (congrArg μ (fullCompactIntertwiner_lie A A' j (complexify F n X) x))

end CompactLaws

section Descent

variable {W Y : Type u} [AddCommGroup W] [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]
  (A : automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ W)
  (P : Subrepresentation A.toMonoidHom)
  {τ : Representation ℂ (automorphicOperatorAlgebra F n) Y}
  (q : Representation.IntertwiningMap A.toMonoidHom τ)
  (hkill : P.toSubmodule ≤ q.toLinearMap.ker)

private abbrev kernelQuotientAction :=
  stableQuotientAlgebraAction A P.toSubmodule (fun a _ hw => P.apply_mem_toSubmodule a hw)

private def kernelQuotientIntertwiner :
    Representation.IntertwiningMap (kernelQuotientAction A P).toMonoidHom τ where
  toLinearMap := P.toSubmodule.liftQ q.toLinearMap hkill
  isIntertwining' a := Submodule.linearMap_qext P.toSubmodule <| LinearMap.ext fun w => by
    change q.toLinearMap (A a w) = τ a (q.toLinearMap w)
    exact LinearMap.congr_fun (q.isIntertwining' a) w

private theorem kernelQuotientIntertwiner_surjective
    (hq : Function.Surjective q.toLinearMap) :
    Function.Surjective (kernelQuotientIntertwiner A P q hkill).toLinearMap := by
  intro y
  obtain ⟨w, hw⟩ := hq y
  exact ⟨P.toSubmodule.mkQ w, hw⟩

end Descent

section SelectedKernel

variable [CompactSpace (AdeleQuotient F)] {r c : ℕ} {m : Fin c → ℕ}
  (hm : ∑ i, (m i + 1) = r + 1) (T : ∀ i, CuspidalOperatorRealization F (m i))
  (Q : IrreducibleOperatorSubquotient F r)
  {W : Type u} [AddCommGroup W] [Module ℂ W]
  (A : automorphicOperatorAlgebra F (r + 1) →ₐ[ℂ] Module.End ℂ W)
  (q : Representation.IntertwiningMap A.toMonoidHom Q.representation)
  (ev : W →ₗ[ℂ] (⨂[ℂ] (i : Fin c), ↥((T i).Space)))

private abbrev kernelBlockShape : BlockShape (r + 1) :=
  ⟨c, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩

local notation "N" => r + 1
local notation "B" => kernelBlockShape hm
local notation "κ" => A.toMonoidHom.comp (compactOperator F N)
local notation "D" => periodRealLieOperator A
local notation "ω" => fun i =>
  OperatorRealization.compactRepresentation (CuspidalOperatorRealization.realization (T i))

/-- A selected normalized finite section and its stable kernel yield the common
restored coefficient realization. The identity map and full quotient both
descend to the quotient by the kernel of the translated evaluations. -/
theorem hasRestoredCuspidalIdentityRealization_of_stableKernel
    (hq : Function.Surjective q.toLinearMap) (hreg : HasRegularCompactOperatorAction A)
    (hF : HasSubquotient B (fun i => ((normalizedCuspidalBlocks hm T) i).realization.finiteRepresentation)
      Q.subquotient.finiteRepresentation)
    (hK : IsBlockPeriodCompactEvaluation B κ ω ev)
    (hU : ∀ X, IsStrictUpperBlockLie F B X → ∀ w, ev (D X w) = 0)
    (hD : ∀ (i : Fin c) (X : RealLieAlgebra F (m i + 1)) w,
      ev (D (blockShapeRealLieInclusion F B i X) w) =
        tensorCoordinateEnd i ((T i).realization.lieAction X) (ev w))
    (P : Subrepresentation A.toMonoidHom)
    (hP : ∀ w, w ∈ P ↔ ∀ k g, compactFiniteCoefficientEvaluation A ev k g w = 0)
    (hkill : ∀ w, w ∈ P → q.toLinearMap w = 0) : HasRestoredCuspidalIdentityRealization Q := by
  let H := P.toSubmodule
  let A₁ := kernelQuotientAction A P
  let j : Representation.IntertwiningMap A.toMonoidHom A₁.toMonoidHom :=
    ⟨H.mkQ, fun _ => LinearMap.ext fun _ => rfl⟩
  have hj : Function.Surjective j.toLinearMap := H.mkQ_surjective
  have hzero (w : W) (hw : w ∈ H) : ev w = 0 := by
    have h := (hP w).mp hw 1 1
    simpa only [compactFiniteCoefficientEvaluation, LinearMap.comp_apply, map_one,
      Module.End.one_apply] using h
  let e₁ := H.liftQ ev hzero
  let q₁ := kernelQuotientIntertwiner A P q hkill
  have hq₁ : Function.Surjective q₁.toLinearMap := kernelQuotientIntertwiner_surjective A P q hkill hq
  have hsep₁ (x : W ⧸ H) (hx : ∀ k g, compactFiniteCoefficientEvaluation A₁ e₁ k g x = 0) : x = 0 := by
    obtain ⟨w, hw⟩ := H.mkQ_surjective x
    subst x
    apply (Submodule.Quotient.mk_eq_zero (p := H)).mpr
    apply (hP w).mpr
    intro k g
    exact hx k g
  have hreg₁ := HasRegularCompactOperatorAction.of_surjective_intertwiner A A₁ j hj hreg
  let κ₁ := A₁.toMonoidHom.comp (compactOperator F N)
  let D₁ := periodRealLieOperator A₁
  have hK₁ : IsBlockPeriodCompactEvaluation B κ₁ ω e₁ := by
    intro i k x
    exact Submodule.Quotient.induction_on H x (fun w => hK i k w)
  have hU₁ (X : RealLieAlgebra F N) (hX : IsStrictUpperBlockLie F B X) (x : W ⧸ H) :
      e₁ (D₁ X x) = 0 := by
    exact Submodule.Quotient.induction_on H x (fun w => hU X hX w)
  have hD₁ (i : Fin c) (X : RealLieAlgebra F (m i + 1)) (x : W ⧸ H) :
      e₁ (D₁ (blockShapeRealLieInclusion F B i X) x) =
        tensorCoordinateEnd i ((T i).realization.lieAction X) (e₁ x) := by
    exact Submodule.Quotient.induction_on H x (fun w => hD i X w)
  refine ⟨c, m, hm, T, hF, W ⧸ H, _, _, A₁, q₁, e₁, hq₁, hsep₁, ?_, ?_⟩
  · intro v
    refine ⟨?_, ?_, ?_⟩
    · exact source_isRealGKModule A₁ v hreg₁.1 hreg₁.2.1 hreg₁.2.2
    · exact isBlockCompactEvaluation_real_of_period B κ₁ ω e₁ v hK₁
    · exact isUnnormalizedBlockLieEvaluation_real_of_period B A₁ e₁
        (fun i X => (T i).realization.lieAction X) v hU₁ hD₁
  · intro v
    refine ⟨?_, ?_, ?_⟩
    · exact source_isComplexGKModule A₁ v hreg₁.1 hreg₁.2.1 hreg₁.2.2
    · exact isBlockCompactEvaluation_complex_of_period B κ₁ ω e₁ v hK₁
    · exact isUnnormalizedBlockLieEvaluation_complex_of_period B A₁ e₁
        (fun i X => (T i).realization.lieAction X) v hU₁ hD₁

end SelectedKernel

end Langlands.Global

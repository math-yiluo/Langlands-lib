import Langlands.Shimura.PEL.RationalInput
import Langlands.AbelianScheme.Tate.WeilFrame

/-! # Source coordinates on actual Weil-compatible PEL frames -/

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme.Tate

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme Langlands.Shimura.PEL

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry

variable (polarizationMap : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
    evaluationA stability composition unitCoherence associativity comparison symmetry) (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)

local notation "FullFrame" => WeilAdelicFrame preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
  polarizationMap h i V ψ s

variable (σ : Langlands.Shimura.AlgebraInvolution ℚ D)
  (hPEL : RationalPELConditions σ ψ) [Nontrivial V]

include hPEL

/-- A given actual full Weil frame identifies source similitudes with all full Weil frames. -/
def weilAdelicFrameSourceEquiv (eta : FullFrame) :
    ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ ≃ FullFrame := by
  letI := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
  letI := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  letI := GroupScheme.Tate.finiteAdeleModule A.toGrp (Over.mk s) (fun _ => True) h
  letI := TateTwist.Divisibility.finiteAdeleModule Γ((Over.mk s).left, ⊤)
    (fun _ => True) h
  exact Equiv.ofBijective (FormIso.precomp eta)
    ⟨FormIso.precomp_injective (hPEL.baseChange_attains_one (Global.FiniteAdeles ℚ)) eta,
      FormIso.exists_precomp_eq eta⟩

local notation "FullSourceEquiv" => weilAdelicFrameSourceEquiv preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility polarizationMap h i V ψ s σ hPEL

/-- Source coordinates use the existing right action, eta times g equals eta composed with g. -/
theorem weilAdelicFrameSourceEquiv_apply (eta : FullFrame)
    (g : ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ) :
    letI := weilAdelicFrameRightAction preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
      polarizationMap h i V ψ s
    FullSourceEquiv eta g = MulOpposite.op g • eta := rfl

/-- The source right action on actual full Weil frames is free. -/
theorem weilAdelicFrameRightAction_injective (eta : FullFrame) :
    letI := weilAdelicFrameRightAction preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
      polarizationMap h i V ψ s
    Function.Injective (fun g : ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ =>
      MulOpposite.op g • eta) :=
  (FullSourceEquiv eta).injective

/-- Any two actual full Weil frames differ by a unique source similitude. -/
theorem weilAdelicFrameRightAction_existsUnique (eta xi : FullFrame) :
    letI := weilAdelicFrameRightAction preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
      polarizationMap h i V ψ s
    ∃! g : ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ,
      MulOpposite.op g • eta = xi := by
  change ∃! g, FullSourceEquiv eta g = xi
  refine ⟨(FullSourceEquiv eta).symm xi, (FullSourceEquiv eta).apply_symm_apply xi, ?_⟩
  intro g hg
  exact (FullSourceEquiv eta).injective
    (hg.trans ((FullSourceEquiv eta).apply_symm_apply xi).symm)

variable {m : ℕ} (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

local notation "AwayFrame" => WeilPrimeToAdelicFrame preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
  polarizationMap h i V ψ s hAway

/-- A given actual away Weil frame identifies source similitudes with all away Weil frames. -/
def weilPrimeToAdelicFrameSourceEquiv (eta : AwayFrame) :
    ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ ≃ AwayFrame := by
  letI := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  letI := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp (Over.mk s) hAway
  letI := TateTwist.Divisibility.primeToFiniteAdeleModule Γ((Over.mk s).left, ⊤) hAway
  exact Equiv.ofBijective (FormIso.precomp eta)
    ⟨FormIso.precomp_injective (hPEL.baseChange_attains_one (Global.PrimeToFiniteAdeles m)) eta,
      FormIso.exists_precomp_eq eta⟩

local notation "AwaySourceEquiv" => weilPrimeToAdelicFrameSourceEquiv preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility polarizationMap h i V ψ s σ hPEL hAway

theorem weilPrimeToAdelicFrameSourceEquiv_apply (eta : AwayFrame)
    (g : ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ) :
    letI := weilPrimeToAdelicFrameRightAction preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
      polarizationMap h i V ψ s hAway
    AwaySourceEquiv eta g = MulOpposite.op g • eta := rfl

/-- The source right action on actual away Weil frames is free. -/
theorem weilPrimeToAdelicFrameRightAction_injective (eta : AwayFrame) :
    letI := weilPrimeToAdelicFrameRightAction preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
      polarizationMap h i V ψ s hAway
    Function.Injective (fun g : ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ =>
      MulOpposite.op g • eta) :=
  (AwaySourceEquiv eta).injective

/-- Any two actual away Weil frames differ by a unique source similitude. -/
theorem weilPrimeToAdelicFrameRightAction_existsUnique (eta xi : AwayFrame) :
    letI := weilPrimeToAdelicFrameRightAction preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
      polarizationMap h i V ψ s hAway
    ∃! g : ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ,
      MulOpposite.op g • eta = xi := by
  change ∃! g, AwaySourceEquiv eta g = xi
  refine ⟨(AwaySourceEquiv eta).symm xi, (AwaySourceEquiv eta).apply_symm_apply xi, ?_⟩
  intro g hg
  exact (AwaySourceEquiv eta).injective
    (hg.trans ((AwaySourceEquiv eta).apply_symm_apply xi).symm)

end Langlands.AbelianScheme.Tate

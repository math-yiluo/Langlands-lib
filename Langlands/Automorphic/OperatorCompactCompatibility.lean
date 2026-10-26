import Langlands.Automorphic.OperatorLieAction
import Langlands.Global.ArchimedeanCovarianceProof
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! # Compact compatibility on actual automorphic realizations -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance operatorCompactRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance operatorCompactContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance operatorCompactSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance operatorCompactFormsAddCommGroup : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance operatorCompactStableAddCommGroup : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

/-- The published smooth covariance descends through the faithful family of slices. -/
theorem finiteSmoothRightAction_envelopingAction (g : InfiniteAdelicGL F n)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : FiniteSmoothRationalFunctions F n) :
    finiteSmoothRightAction F n (AdelicGL.ofInfinite F n g)
        (finiteSmoothEnvelopingAction F n a f) =
      finiteSmoothEnvelopingAction F n (ArchimedeanGL.envelopingConjugation F n g a)
        (finiteSmoothRightAction F n (AdelicGL.ofInfinite F n g) f) := by
  apply finiteSmoothSlice_injective F n
  funext b
  dsimp only
  rw [finiteSmoothSlice_ofInfinite_rightAction, finiteSmoothSlice_envelopingAction,
    finiteSmoothSlice_envelopingAction, finiteSmoothSlice_ofInfinite_rightAction]
  exact ArchimedeanGL.envelopingRightCovariance F n g a _

/-- The actual core inherits compact/enveloping covariance by restriction. -/
theorem stableAutomorphicCompactAction_envelopingAction (k : standardInfiniteCompact F n)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : StableAutomorphicFunctions F n) :
    stableAutomorphicCompactAction F n k (stableAutomorphicEnvelopingAction F n a f) =
      stableAutomorphicEnvelopingAction F n
        (ArchimedeanGL.envelopingConjugation F n k.val a)
        (stableAutomorphicCompactAction F n k f) := by
  apply Subtype.ext
  exact finiteSmoothRightAction_envelopingAction k.val a f.val

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance operatorCompactSpaceAddCommGroup : AddCommGroup S.Space := Submodule.addCommGroup _
local instance operatorCompactTargetAddCommGroup : AddCommGroup T.Space := Submodule.addCommGroup _

/-- The actual continuous-function realization intertwines compact translation. -/
def compactContinuousInclusion :
    S.compactRepresentation.IntertwiningMap
      (infiniteSubgroupRightAction F n (standardInfiniteCompact F n)) where
  toLinearMap := S.toContinuous
  isIntertwining' _ := by ext; rfl

theorem compactContinuousInclusion_injective : Function.Injective S.compactContinuousInclusion :=
  S.toContinuous_injective

/-- Every vector of every actual operator realization is compact-finite. -/
theorem compactRepresentation_isFiniteVector (f : S.Space) :
    FiniteVectors.IsFiniteVector S.compactRepresentation f :=
  (FiniteVectors.isFiniteVector_map_iff S.compactContinuousInclusion
    S.compactContinuousInclusion_injective f).mp
      (((mem_automorphicSubrepresentation F n (S.formInclusion f).val).mp
        (S.formInclusion f).property).2.1)

theorem finiteRepresentation_compactRepresentation
    (d : FiniteAdelicGL F n) (k : standardInfiniteCompact F n) (f : S.Space) :
    S.finiteRepresentation d (S.compactRepresentation k f) =
      S.compactRepresentation k (S.finiteRepresentation d f) := by
  apply S.toContinuous_injective
  exact Representation.IntertwiningMap.isIntertwining _ _
    (finiteTranslateIntertwiner F n (standardInfiniteCompact F n) d) k (S.toContinuous f)

/-- Compact translation respects the genuine differential action with its actual adjoint. -/
theorem compactRepresentation_envelopingAction (k : standardInfiniteCompact F n)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : S.Space) :
    S.compactRepresentation k (S.envelopingAction a f) =
      S.envelopingAction (ArchimedeanGL.envelopingConjugation F n k.val a)
        (S.compactRepresentation k f) := by
  apply S.inclusion_injective
  exact stableAutomorphicCompactAction_envelopingAction k a f.val

theorem compactRepresentation_complexLieAction (k : standardInfiniteCompact F n)
    (X : ArchimedeanGL.ComplexLieAlgebra F n) (f : S.Space) :
    S.compactRepresentation k (S.complexLieAction X f) =
      S.complexLieAction (ArchimedeanGL.complexLieConjugation F n k.val X)
        (S.compactRepresentation k f) := by
  simpa only [complexLieAction_apply, ArchimedeanGL.envelopingConjugation_generator] using
    S.compactRepresentation_envelopingAction k (ArchimedeanGL.envelopingGenerator F n X) f

/-- Actual compact translation as an invertible linear map on the realized space. -/
def compactLinearEquiv (k : standardInfiniteCompact F n) : S.Space ≃ₗ[ℂ] S.Space :=
  LinearMap.GeneralLinearGroup.toLinearEquiv (S.compactRepresentation.asGroupHom k)

@[simp]
theorem compactLinearEquiv_apply (k : standardInfiniteCompact F n) (f : S.Space) :
    S.compactLinearEquiv k f = S.compactRepresentation k f := rfl

@[simp]
theorem compactLinearEquiv_symm_apply (k : standardInfiniteCompact F n) (f : S.Space) :
    (S.compactLinearEquiv k).symm f = S.compactRepresentation k⁻¹ f := rfl

/-- Compact translation is in particular an automorphism of the finite adelic representation. -/
def compactFiniteEquivalence (k : standardInfiniteCompact F n) :
    S.finiteRepresentation.Equiv S.finiteRepresentation :=
  Representation.Equiv.mk (S.compactLinearEquiv k)
    (fun d => LinearMap.ext (fun f =>
      (S.finiteRepresentation_compactRepresentation d k f).symm))

/-- Conjugation by actual compact translation on the full endomorphism algebra. -/
def compactEndConjugation (k : standardInfiniteCompact F n) :
    Module.End ℂ S.Space ≃ₐ[ℂ] Module.End ℂ S.Space :=
  (S.compactLinearEquiv k).conjAlgEquiv ℂ

@[simp]
theorem compactEndConjugation_apply (k : standardInfiniteCompact F n)
    (A : Module.End ℂ S.Space) (f : S.Space) :
    S.compactEndConjugation k A f =
      S.compactRepresentation k (A (S.compactRepresentation k⁻¹ f)) := rfl

/-- Conjugation fixes every finite adelic translation operator. -/
theorem compactEndConjugation_finite (k : standardInfiniteCompact F n)
    (d : FiniteAdelicGL F n) :
    S.compactEndConjugation k (S.finiteRepresentation d) = S.finiteRepresentation d := by
  apply LinearMap.ext
  intro f
  calc
    _ = S.compactRepresentation k
        (S.finiteRepresentation d (S.compactRepresentation k⁻¹ f)) := rfl
    _ = S.finiteRepresentation d
        (S.compactRepresentation k (S.compactRepresentation k⁻¹ f)) :=
      (S.finiteRepresentation_compactRepresentation d k
        (S.compactRepresentation k⁻¹ f)).symm
    _ = S.finiteRepresentation d f :=
      congrArg (S.finiteRepresentation d) ((S.compactLinearEquiv k).apply_symm_apply f)

/-- Endomorphism conjugation restricts to the genuine adjoint on enveloping operators. -/
theorem compactEndConjugation_enveloping (k : standardInfiniteCompact F n)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) :
    S.compactEndConjugation k (S.envelopingAction a) =
      S.envelopingAction (ArchimedeanGL.envelopingConjugation F n k.val a) := by
  apply LinearMap.ext
  intro f
  calc
    _ = S.compactRepresentation k
        (S.envelopingAction a (S.compactRepresentation k⁻¹ f)) := rfl
    _ = S.envelopingAction (ArchimedeanGL.envelopingConjugation F n k.val a)
        (S.compactRepresentation k (S.compactRepresentation k⁻¹ f)) :=
      S.compactRepresentation_envelopingAction k a (S.compactRepresentation k⁻¹ f)
    _ = S.envelopingAction (ArchimedeanGL.envelopingConjugation F n k.val a) f :=
      congrArg (S.envelopingAction (ArchimedeanGL.envelopingConjugation F n k.val a))
        ((S.compactLinearEquiv k).apply_symm_apply f)

/-- The same compatibility on the actual complex Lie generators. -/
theorem compactEndConjugation_complexLie (k : standardInfiniteCompact F n)
    (X : ArchimedeanGL.ComplexLieAlgebra F n) :
    S.compactEndConjugation k (S.complexLieAction X) =
      S.complexLieAction (ArchimedeanGL.complexLieConjugation F n k.val X) := by
  simpa only [complexLieAction, LieHom.comp_apply, AlgHom.toLieHom_apply,
    ArchimedeanGL.envelopingConjugation_generator] using
    S.compactEndConjugation_enveloping k (ArchimedeanGL.envelopingGenerator F n X)

namespace Intertwiner

variable {S T}

/-- A full intertwiner retains the same linear map on compact representations. -/
def compactRestriction (L : S.Intertwiner T) :
    S.compactRepresentation.IntertwiningMap T.compactRepresentation where
  toLinearMap := L.toLinearMap
  isIntertwining' k := L.isIntertwining' (compactOperator F n k)

end Intertwiner

namespace Equivalence

variable {S T}

/-- A full equivalence retains its compact representation as well. -/
def compactRestriction (e : S.Equivalence T) :
    S.compactRepresentation.Equiv T.compactRepresentation :=
  Representation.Equiv.mk e.toLinearEquiv
    (fun k => e.toIntertwiningMap.isIntertwining' (compactOperator F n k))

end Equivalence
end OperatorRealization
end Langlands.Automorphic

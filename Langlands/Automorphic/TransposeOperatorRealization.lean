import Langlands.Automorphic.TransposeOperatorCore
import Langlands.Representation.SubrepresentationConjugation
import Langlands.Automorphic.ConjugateContragredient
import Langlands.Global.RankinSelberg.DualWhittakerCore.DualCuspidal

/-! # Actual cuspidal operator realizations under inverse-transpose pullback -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear NumberField IsDedekindDomain
open ContinuousRationalFunctions

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}

local instance transposeRealizationRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance transposeRealizationContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance transposeRealizationFiniteSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance transposeRealizationFormGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance transposeRealizationStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions K n) := Submodule.addCommGroup _

/-- The low-level linear pullback is the existing constant-term transpose dual. -/
theorem continuousTranspose_eq_transposeDual (f : ContinuousRationalFunctions K n) :
    continuousTranspose K n f = transposeDual f := rfl

section Cuspidal

variable [CompactSpace (AdeleQuotient K)]

/-- Reuse the actual block-unipotent constant-term transformation. -/
theorem isCuspidal_continuousTranspose {f : ContinuousRationalFunctions K n}
    (hf : IsCuspidal K n f) : IsCuspidal K n (continuousTranspose K n f) := by
  rw [continuousTranspose_eq_transposeDual]
  exact isCuspidal_transposeDual hf

@[simp] theorem isCuspidal_continuousTranspose_iff (f : ContinuousRationalFunctions K n) :
    IsCuspidal K n (continuousTranspose K n f) ↔ IsCuspidal K n f := by
  constructor
  · intro hf
    simpa only [continuousTranspose_involutive] using isCuspidal_continuousTranspose hf
  · exact isCuspidal_continuousTranspose

end Cuspidal

namespace OperatorRealization

/-- Actual Inverse-transpose pullback gives an order equivalence on the embedded realizations. -/
def transposeOrderIso : OperatorRealization K n ≃o OperatorRealization K n :=
  conjugatedSubrepresentationOrderIso (stableAutomorphicAction K n)
    (stableAutomorphicAction K n) (transposeOperatorConjugation K n).toMulEquiv
    (StableAutomorphicFunctions.transpose K n)
    (StableAutomorphicFunctions.operatorAction_transpose K n)

variable (S : OperatorRealization K n)

local instance transposeRealizationSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The actual image of the function subspace under Inverse-transpose argument pullback. -/
def transpose : OperatorRealization K n := transposeOrderIso S

@[simp] theorem transpose_toSubmodule :
    S.transpose.toSubmodule = S.toSubmodule.map
      (StableAutomorphicFunctions.transpose K n).toLinearMap := rfl

@[simp] theorem transpose_involutive : S.transpose.transpose = S := by
  apply Subrepresentation.toSubmodule_injective
  change (S.toSubmodule.map (StableAutomorphicFunctions.transpose K n).toLinearMap).map
      (StableAutomorphicFunctions.transpose K n).toLinearMap = S.toSubmodule
  rw [← Submodule.map_comp]
  have hc : (StableAutomorphicFunctions.transpose K n).toLinearMap.comp
      (StableAutomorphicFunctions.transpose K n).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    exact StableAutomorphicFunctions.transpose_involutive K n
  rw [hc, Submodule.map_id]

/-- Restrict the actual linear equivalence to the original subspace and its image. -/
def transposeEquiv : S.Space ≃ₗ[ℂ] S.transpose.Space :=
  (StableAutomorphicFunctions.transpose K n).ofSubmodules _ _ rfl

@[simp] theorem transposeEquiv_val (f : S.Space) :
    (S.transposeEquiv f).val = StableAutomorphicFunctions.transpose K n f.val := rfl

@[simp] theorem transposeEquiv_symm_val (f : S.transpose.Space) :
    (S.transposeEquiv.symm f).val = StableAutomorphicFunctions.transpose K n f.val := by
  change (StableAutomorphicFunctions.transpose K n).symm f.val = _
  rw [StableAutomorphicFunctions.transpose_symm]

/-- The whole concrete operator algebra transforms by its actual inverse-transpose automorphism. -/
theorem transposeEquiv_operatorAction (a : automorphicOperatorAlgebra K n) (f : S.Space) :
    S.transpose.representation a (S.transposeEquiv f) =
      S.transposeEquiv (S.representation (transposeOperatorConjugation K n a) f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.operatorAction_transpose K n a f.val

theorem transposeEquiv_finite (d : FiniteAdelicGL K n) (f : S.Space) :
    S.transpose.finiteRepresentation d (S.transposeEquiv f) =
      S.transposeEquiv (S.finiteRepresentation (inverseTranspose n (FiniteAdeleRing (𝓞 K) K) d) f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.finiteAction_transpose K n d f.val

theorem transposeEquiv_compact (k : standardInfiniteCompact K n) (f : S.Space) :
    S.transpose.compactRepresentation k (S.transposeEquiv f) =
      S.transposeEquiv (S.compactRepresentation (ArchimedeanGL.compactTranspose K n k) f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.compactAction_transpose K n k f.val

theorem transposeEquiv_differential
    (a : ArchimedeanGL.EnvelopingAlgebra K n) (f : S.Space) :
    S.transpose.envelopingAction a (S.transposeEquiv f) =
      S.transposeEquiv (S.envelopingAction
        (ArchimedeanGL.envelopingIota K n a) f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.envelopingAction_transpose K n a f.val

/-- Covariance for the genuine real Lie algebra action. -/
theorem transposeEquiv_lieAction (X : ArchimedeanGL.RealLieAlgebra K n) (f : S.Space) :
    S.transpose.lieAction X (S.transposeEquiv f) =
      S.transposeEquiv (S.lieAction (ArchimedeanGL.realLieIota K n X) f) := by
  simpa only [lieAction, ArchimedeanGL.envelopingIota_generator,
    ArchimedeanGL.complexify_apply, ArchimedeanGL.complexLieIota_tmul] using
    S.transposeEquiv_differential
      (ArchimedeanGL.envelopingGenerator K n (ArchimedeanGL.complexify K n X)) f

@[simp] theorem formInclusion_transposeEquiv (f : S.Space) :
    S.transpose.formInclusion (S.transposeEquiv f) =
      AutomorphicForms.transpose K n (S.formInclusion f) := rfl

@[simp] theorem toContinuous_transposeEquiv (f : S.Space) :
    S.transpose.toContinuous (S.transposeEquiv f) =
      continuousTranspose K n (S.toContinuous f) := rfl

@[simp] theorem evaluate_transposeEquiv (f : S.Space) (g : AdelicGL K n) :
    evaluate K n (S.transpose.toContinuous (S.transposeEquiv f)) g =
      evaluate K n (S.toContinuous f) (inverseTranspose n (AdeleRing (𝓞 K) K) g) :=
  evaluate_continuousTranspose K n _ g

@[simp] theorem evaluate_transposeEquiv_symm
    (f : S.transpose.Space) (g : AdelicGL K n) :
    evaluate K n (S.toContinuous (S.transposeEquiv.symm f)) g =
      evaluate K n (S.transpose.toContinuous f) (inverseTranspose n (AdeleRing (𝓞 K) K) g) := by
  change evaluate K n (S.transposeEquiv.symm f).val.val.val g = _
  rw [transposeEquiv_symm_val]
  exact StableAutomorphicFunctions.evaluate_transpose K n f.val g

/-- Inverse-transpose pullback identifies all invariant subspaces of the restricted actions. -/
def transposeSubrepresentationOrderIso :
    Subrepresentation S.representation ≃o Subrepresentation S.transpose.representation :=
  conjugatedSubrepresentationOrderIso S.representation S.transpose.representation
    (transposeOperatorConjugation K n).toMulEquiv S.transposeEquiv
    S.transposeEquiv_operatorAction

/-- Irreducibility for all three operator families is preserved and reflected. -/
theorem transpose_isIrreducible_iff : S.transpose.IsIrreducible ↔ S.IsIrreducible :=
  S.transposeSubrepresentationOrderIso.isSimpleOrder_iff.symm

section Cuspidal

variable [CompactSpace (AdeleQuotient K)]

/-- The actual inverse-transpose image has vanishing constant terms exactly when the source does. -/
theorem transpose_isCuspidal_iff : S.transpose.IsCuspidal ↔ S.IsCuspidal := by
  rw [isCuspidal_iff, isCuspidal_iff]
  constructor
  · intro ht f
    have hf := ht (S.transposeEquiv f)
    rw [toContinuous_transposeEquiv, isCuspidal_continuousTranspose_iff] at hf
    exact hf
  · intro hs f
    obtain ⟨g, rfl⟩ := S.transposeEquiv.surjective f
    rw [toContinuous_transposeEquiv, isCuspidal_continuousTranspose_iff]
    exact hs g

end Cuspidal
end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient K)] {r : ℕ}

/-- Inverse-transpose argument pullback of an actual irreducible cuspidal realization of rank r+1. -/
def transpose (S : CuspidalOperatorRealization K r) : CuspidalOperatorRealization K r where
  realization := S.realization.transpose
  irreducible := S.realization.transpose_isIrreducible_iff.mpr S.irreducible
  cuspidal := S.realization.transpose_isCuspidal_iff.mpr S.cuspidal

@[simp] theorem transpose_involutive (S : CuspidalOperatorRealization K r) :
    S.transpose.transpose = S := by
  cases S
  simp only [transpose, OperatorRealization.transpose_involutive]

variable (T : CuspidalOperatorRealization K r)

/-- Actual inverse-transpose pullback on vectors of a cuspidal realization. -/
def transposeEquiv : T.Space ≃ₗ[ℂ] T.transpose.Space :=
  T.realization.transposeEquiv

@[simp] theorem toContinuous_transposeEquiv (x : T.Space) :
    T.transpose.realization.toContinuous (T.transposeEquiv x) =
      continuousTranspose K (r + 1) (T.realization.toContinuous x) := rfl

/-- Finite covariance with the inverse-transpose twist on the original realization. -/
theorem transposeEquiv_finite (d : FiniteAdelicGL K (r + 1)) (x : T.Space) :
    T.transposeEquiv
        (T.realization.finiteRepresentation
          (inverseTranspose (r + 1) (FiniteAdeleRing (𝓞 K) K) d) x) =
      T.transpose.realization.finiteRepresentation d (T.transposeEquiv x) :=
  (T.realization.transposeEquiv_finite d x).symm

/-- Compact covariance with the inverse-transpose twist on the original realization. -/
theorem transposeEquiv_compact (k : standardInfiniteCompact K (r + 1)) (x : T.Space) :
    T.transposeEquiv
        (T.realization.compactRepresentation (ArchimedeanGL.compactTranspose K (r + 1) k) x) =
      T.transpose.realization.compactRepresentation k (T.transposeEquiv x) :=
  (T.realization.transposeEquiv_compact k x).symm

/-- Real Lie covariance with negative transpose on the original realization. -/
theorem transposeEquiv_lieAction
    (X : ArchimedeanGL.RealLieAlgebra K (r + 1)) (x : T.Space) :
    T.transposeEquiv
        (T.realization.lieAction (ArchimedeanGL.realLieIota K (r + 1) X) x) =
      T.transpose.realization.lieAction X (T.transposeEquiv x) :=
  (T.realization.transposeEquiv_lieAction X x).symm

end CuspidalOperatorRealization
end Langlands.Automorphic

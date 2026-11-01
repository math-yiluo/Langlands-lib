import Langlands.Representation.SubrepresentationConjugation
import Langlands.Automorphic.StableAutomorphicCMTransport
import Langlands.Automorphic.CuspidalCMTransport
import Langlands.Automorphic.CuspidalOperatorRealization

/-! # Actual CM images of full automorphic operator realizations -/

noncomputable section
universe uK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {K : Type uK} [Field K] [NumberField K] [NumberField.IsCMField K] {n : ℕ}

local instance operatorCMRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance operatorCMContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance operatorCMFiniteSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance operatorCMFormGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance operatorCMStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions K n) := Submodule.addCommGroup _

namespace OperatorRealization

/-- Actual CM pullback gives an order equivalence on the embedded realizations. -/
def complexConjOrderIso : OperatorRealization K n ≃o OperatorRealization K n :=
  conjugatedSubrepresentationOrderIso (stableAutomorphicAction K n)
    (stableAutomorphicAction K n) (cmOperatorConjugation n).toMulEquiv
    (StableAutomorphicFunctions.complexConj n).toLinearEquiv
    (StableAutomorphicFunctions.operatorAction_complexConj n)

variable (S : OperatorRealization K n)

local instance operatorCMSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The actual image of the function subspace under CM argument pullback. -/
def complexConj : OperatorRealization K n := complexConjOrderIso S

@[simp] theorem complexConj_toSubmodule :
    S.complexConj.toSubmodule = S.toSubmodule.map
      (StableAutomorphicFunctions.complexConj n).toLinearMap := rfl

@[simp] theorem complexConj_complexConj : S.complexConj.complexConj = S := by
  apply Subrepresentation.toSubmodule_injective
  change (S.toSubmodule.map (StableAutomorphicFunctions.complexConj n).toLinearMap).map
      (StableAutomorphicFunctions.complexConj n).toLinearMap = S.toSubmodule
  rw [← Submodule.map_comp]
  have hc : (StableAutomorphicFunctions.complexConj (K := K) n).toLinearMap.comp
      (StableAutomorphicFunctions.complexConj n).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    exact StableAutomorphicFunctions.complexConj_complexConj n
  rw [hc, Submodule.map_id]

/-- Restrict the actual continuous equivalence to the original subspace and its image. -/
def complexConjEquiv : S.Space ≃L[ℂ] S.complexConj.Space :=
  (StableAutomorphicFunctions.complexConj n).ofSubmodules _ _ rfl

@[simp] theorem complexConjEquiv_val (f : S.Space) :
    (S.complexConjEquiv f).val = StableAutomorphicFunctions.complexConj n f.val := rfl

@[simp] theorem complexConjEquiv_symm_val (f : S.complexConj.Space) :
    (S.complexConjEquiv.symm f).val = StableAutomorphicFunctions.complexConj n f.val := by
  change (StableAutomorphicFunctions.complexConj n).symm f.val = _
  rw [StableAutomorphicFunctions.complexConj_symm]

/-- The whole concrete operator algebra transforms by its actual CM automorphism. -/
theorem complexConjEquiv_operatorAction (a : automorphicOperatorAlgebra K n) (f : S.Space) :
    S.complexConj.representation a (S.complexConjEquiv f) =
      S.complexConjEquiv (S.representation (cmOperatorConjugation n a) f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.operatorAction_complexConj n a f.val

theorem complexConjEquiv_finite (d : FiniteAdelicGL K n) (f : S.Space) :
    S.complexConj.finiteRepresentation d (S.complexConjEquiv f) =
      S.complexConjEquiv (S.finiteRepresentation (CMConjugation.finiteConj K n d) f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.finiteAction_complexConj n d f.val

theorem complexConjEquiv_compact (k : standardInfiniteCompact K n) (f : S.Space) :
    S.complexConj.compactRepresentation k (S.complexConjEquiv f) =
      S.complexConjEquiv (S.compactRepresentation (CMConjugation.compactConj K n k) f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.compactAction_complexConj n k f.val

theorem complexConjEquiv_differential
    (a : ArchimedeanGL.EnvelopingAlgebra K n) (f : S.Space) :
    S.complexConj.envelopingAction a (S.complexConjEquiv f) =
      S.complexConjEquiv (S.envelopingAction
        (ArchimedeanLieTransport.envelopingEquiv n
          (NumberField.IsCMField.complexConj K).toRingEquiv a) f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.envelopingAction_complexConj n a f.val

@[simp] theorem formInclusion_complexConjEquiv (f : S.Space) :
    S.complexConj.formInclusion (S.complexConjEquiv f) =
      AutomorphicForms.complexConj n (S.formInclusion f) := rfl

@[simp] theorem toContinuous_complexConjEquiv (f : S.Space) :
    S.complexConj.toContinuous (S.complexConjEquiv f) =
      ContinuousRationalFunctions.complexConj n (S.toContinuous f) := rfl

@[simp] theorem evaluate_complexConjEquiv (f : S.Space) (g : AdelicGL K n) :
    evaluate K n (S.complexConj.toContinuous (S.complexConjEquiv f)) g =
      evaluate K n (S.toContinuous f) (CMConjugation.adelicConj K n g) :=
  ContinuousRationalFunctions.evaluate_complexConj n _ g

@[simp] theorem evaluate_complexConjEquiv_symm
    (f : S.complexConj.Space) (g : AdelicGL K n) :
    evaluate K n (S.toContinuous (S.complexConjEquiv.symm f)) g =
      evaluate K n (S.complexConj.toContinuous f) (CMConjugation.adelicConj K n g) := by
  change evaluate K n (S.complexConjEquiv.symm f).val.val.val g = _
  rw [complexConjEquiv_symm_val]
  exact StableAutomorphicFunctions.evaluate_complexConj n f.val g

/-- CM pullback identifies all invariant subspaces of the restricted actions. -/
def complexConjSubrepresentationOrderIso :
    Subrepresentation S.representation ≃o Subrepresentation S.complexConj.representation :=
  conjugatedSubrepresentationOrderIso S.representation S.complexConj.representation
    (cmOperatorConjugation n).toMulEquiv S.complexConjEquiv.toLinearEquiv
    S.complexConjEquiv_operatorAction

/-- Irreducibility for all three operator families is preserved and reflected. -/
theorem complexConj_isIrreducible_iff : S.complexConj.IsIrreducible ↔ S.IsIrreducible :=
  S.complexConjSubrepresentationOrderIso.isSimpleOrder_iff.symm

/-- Central characters are transported by actual idele-class argument conjugation. -/
theorem complexConj_hasCentralCharacter_iff (χ : HeckeCharacter K) :
    S.complexConj.HasCentralCharacter χ.complexConj ↔ S.HasCentralCharacter χ := by
  rw [hasCentralCharacter_iff, hasCentralCharacter_iff]
  constructor
  · intro ht f
    have hf := ht (S.complexConjEquiv f)
    rw [formInclusion_complexConjEquiv,
      AutomorphicForms.complexConj_mem_centralCharacter_iff] at hf
    exact hf
  · intro hs f
    obtain ⟨g, rfl⟩ := S.complexConjEquiv.surjective f
    rw [formInclusion_complexConjEquiv,
      AutomorphicForms.complexConj_mem_centralCharacter_iff]
    exact hs g

section Cuspidal

variable [CompactSpace (AdeleQuotient K)]

/-- The actual CM image has vanishing constant terms exactly when the source does. -/
theorem complexConj_isCuspidal_iff : S.complexConj.IsCuspidal ↔ S.IsCuspidal := by
  rw [isCuspidal_iff, isCuspidal_iff]
  constructor
  · intro ht f
    have hf := ht (S.complexConjEquiv f)
    rw [toContinuous_complexConjEquiv, isCuspidal_complexConj_iff] at hf
    exact hf
  · intro hs f
    obtain ⟨g, rfl⟩ := S.complexConjEquiv.surjective f
    rw [toContinuous_complexConjEquiv, isCuspidal_complexConj_iff]
    exact hs g

end Cuspidal
end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient K)] {r : ℕ}

/-- CM argument pullback of an actual irreducible cuspidal realization of rank r+1. -/
def complexConj (S : CuspidalOperatorRealization K r) : CuspidalOperatorRealization K r where
  realization := S.realization.complexConj
  irreducible := S.realization.complexConj_isIrreducible_iff.mpr S.irreducible
  cuspidal := S.realization.complexConj_isCuspidal_iff.mpr S.cuspidal

@[simp] theorem complexConj_complexConj (S : CuspidalOperatorRealization K r) :
    S.complexConj.complexConj = S := by
  cases S
  simp only [complexConj, OperatorRealization.complexConj_complexConj]

theorem complexConj_hasCentralCharacter_iff
    (S : CuspidalOperatorRealization K r) (χ : HeckeCharacter K) :
    S.complexConj.HasCentralCharacter χ.complexConj ↔ S.HasCentralCharacter χ :=
  S.realization.complexConj_hasCentralCharacter_iff χ

end CuspidalOperatorRealization
end Langlands.Automorphic

import Langlands.Automorphic.CMOperatorConjugation
import Langlands.Automorphic.AutomorphicCMTransport

/-! # Actual CM pullback on the stable automorphic operator core -/

noncomputable section
universe uK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {K : Type uK} [Field K] [NumberField K] [NumberField.IsCMField K] (n : ℕ)

local instance stableCMRationalGroup : AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance stableCMContinuousGroup : AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance stableCMFiniteSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance stableCMFormGroup : AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance stableCMStableGroup : AddCommGroup (StableAutomorphicFunctions K n) := Submodule.addCommGroup _

/-- Whole-algebra covariance and actual form preservation imply core preservation. -/
theorem mem_automorphicOperatorCore_complexConj
    {f : FiniteSmoothRationalFunctions K n} (hf : f ∈ automorphicOperatorCore K n) :
    finiteSmoothComplexConj n f ∈ automorphicOperatorCore K n := by
  intro a
  rw [operatorAction_complexConj]
  exact (finiteSmoothComplexConj_mem_automorphic_iff n _).mpr
    (hf (cmOperatorConjugation n a))

@[simp] theorem finiteSmoothComplexConj_mem_automorphicOperatorCore_iff
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothComplexConj n f ∈ automorphicOperatorCore K n ↔
      f ∈ automorphicOperatorCore K n := by
  constructor
  · intro hf
    have h := mem_automorphicOperatorCore_complexConj n hf
    rwa [finiteSmoothComplexConj_finiteSmoothComplexConj] at h
  · exact mem_automorphicOperatorCore_complexConj n

private theorem automorphicOperatorCore_map_complexConj :
    (automorphicOperatorCore K n).toSubmodule.map
        (finiteSmoothComplexConj n).toLinearMap =
      (automorphicOperatorCore K n).toSubmodule := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact mem_automorphicOperatorCore_complexConj n hg
  · intro hf
    obtain ⟨g, rfl⟩ := (finiteSmoothComplexConj n).surjective f
    exact ⟨g, (finiteSmoothComplexConj_mem_automorphicOperatorCore_iff n g).mp hf, rfl⟩

namespace StableAutomorphicFunctions

/-- Restrict the existing continuous CM argument pullback to the actual stable core. -/
def complexConj : StableAutomorphicFunctions K n ≃L[ℂ] StableAutomorphicFunctions K n :=
  (finiteSmoothComplexConj n).ofSubmodules _ _
    (automorphicOperatorCore_map_complexConj n)

@[simp] theorem complexConj_val (f : StableAutomorphicFunctions K n) :
    (complexConj n f).val = finiteSmoothComplexConj n f.val := rfl

@[simp] theorem complexConj_complexConj (f : StableAutomorphicFunctions K n) :
    complexConj n (complexConj n f) = f := by
  apply Subtype.ext
  exact finiteSmoothComplexConj_finiteSmoothComplexConj n f.val

@[simp] theorem complexConj_symm :
    (complexConj (K := K) n).symm = complexConj n := by
  apply ContinuousLinearEquiv.ext
  funext f
  apply (complexConj n).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, complexConj_complexConj]

/-- Every actual operator satisfies the CM covariance on the constructed core. -/
theorem operatorAction_complexConj (a : automorphicOperatorAlgebra K n)
    (f : StableAutomorphicFunctions K n) :
    stableAutomorphicAction K n a (complexConj n f) =
      complexConj n (stableAutomorphicAction K n (cmOperatorConjugation n a) f) := by
  apply Subtype.ext
  exact Langlands.Automorphic.operatorAction_complexConj n a f.val

theorem finiteAction_complexConj (d : FiniteAdelicGL K n)
    (f : StableAutomorphicFunctions K n) :
    stableAutomorphicFiniteAction K n d (complexConj n f) =
      complexConj n
        (stableAutomorphicFiniteAction K n (CMConjugation.finiteConj K n d) f) := by
  apply Subtype.ext
  exact (finiteSmoothComplexConj_finiteRightAction n d f.val).symm

theorem compactAction_complexConj (k : standardInfiniteCompact K n)
    (f : StableAutomorphicFunctions K n) :
    stableAutomorphicCompactAction K n k (complexConj n f) =
      complexConj n
        (stableAutomorphicCompactAction K n (CMConjugation.compactConj K n k) f) := by
  apply Subtype.ext
  exact (finiteSmoothComplexConj_compactRightAction n k f.val).symm

theorem envelopingAction_complexConj (a : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : StableAutomorphicFunctions K n) :
    stableAutomorphicEnvelopingAction K n a (complexConj n f) =
      complexConj n
        (stableAutomorphicEnvelopingAction K n
          (ArchimedeanLieTransport.envelopingEquiv n
            (NumberField.IsCMField.complexConj K).toRingEquiv a) f) := by
  apply Subtype.ext
  exact (finiteSmoothComplexConj_envelopingAction n a f.val).symm

@[simp] theorem inclusion_complexConj (f : StableAutomorphicFunctions K n) :
    stableAutomorphicInclusion K n (complexConj n f) =
      AutomorphicForms.complexConj n (stableAutomorphicInclusion K n f) := rfl

@[simp] theorem evaluate_complexConj (f : StableAutomorphicFunctions K n)
    (g : AdelicGL K n) :
    evaluate K n (complexConj n f).val.val g =
      evaluate K n f.val.val (CMConjugation.adelicConj K n g) :=
  ContinuousRationalFunctions.evaluate_complexConj n _ g

@[simp] theorem evaluate_complexConj_symm (f : StableAutomorphicFunctions K n)
    (g : AdelicGL K n) :
    evaluate K n ((complexConj n).symm f).val.val g =
      evaluate K n f.val.val (CMConjugation.adelicConj K n g) := by
  rw [complexConj_symm]
  exact evaluate_complexConj n f g

end StableAutomorphicFunctions
end Langlands.Automorphic

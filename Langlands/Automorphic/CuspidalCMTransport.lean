import Langlands.Automorphic.AutomorphicCMTransport
import Langlands.Automorphic.ConstantTermArithmeticTransport

/-! # Actual CM pullback on cuspidal automorphic forms -/

noncomputable section
universe uK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {K : Type uK} [Field K] [NumberField K] [NumberField.IsCMField K]
variable [CompactSpace (AdeleQuotient K)]

local instance cuspidalCMRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions K n) :=
  Submodule.addCommGroup _
local instance cuspidalCMContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance cuspidalCMFiniteSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance cuspidalCMFormGroup (n : ℕ) : AddCommGroup (AutomorphicForms K n) :=
  Submodule.addCommGroup _
local instance cuspidalCMCuspGroup (n : ℕ) : AddCommGroup (CuspidalAutomorphicForms K n) :=
  Submodule.addCommGroup _
local instance cuspidalCMCentralCharacterGroup (n : ℕ) (χ : HeckeCharacter K) :
    AddCommGroup (CentralCharacterCuspidalForms K n χ) := Submodule.addCommGroup _

namespace AutomorphicForms

/-- Actual CM pullback preserves and reflects the existing constant-term cusp condition. -/
@[simp] theorem complexConj_mem_cuspidal_iff (n : ℕ) (f : AutomorphicForms K n) :
    complexConj n f ∈ cuspidalAutomorphicSubrepresentation K n ↔
      f ∈ cuspidalAutomorphicSubrepresentation K n :=
  isCuspidal_complexConj_iff n (automorphicToContinuous K n f)

/-- The central character and cusp equations transform on the same actual form. -/
@[simp] theorem complexConj_mem_centralCharacterCuspidal_iff (n : ℕ)
    (χ : HeckeCharacter K) (f : AutomorphicForms K n) :
    complexConj n f ∈ centralCharacterCuspidalSubrepresentation K n χ.complexConj ↔
      f ∈ centralCharacterCuspidalSubrepresentation K n χ := by
  rw [mem_centralCharacterCuspidalSubrepresentation,
    mem_centralCharacterCuspidalSubrepresentation]
  exact and_congr (complexConj_mem_centralCharacter_iff n χ f)
    (isCuspidal_complexConj_iff n (automorphicToContinuous K n f))

end AutomorphicForms

private theorem cuspidalAutomorphicSubrepresentation_map_complexConj (n : ℕ) :
    (cuspidalAutomorphicSubrepresentation K n).toSubmodule.map
        (AutomorphicForms.complexConj n).toLinearMap =
      (cuspidalAutomorphicSubrepresentation K n).toSubmodule := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (AutomorphicForms.complexConj_mem_cuspidal_iff n g).mpr hg
  · intro hf
    obtain ⟨g, rfl⟩ := (AutomorphicForms.complexConj n).surjective f
    exact ⟨g, (AutomorphicForms.complexConj_mem_cuspidal_iff n g).mp hf, rfl⟩

namespace CuspidalAutomorphicForms

/-- Actual argument conjugation restricted to the existing cuspidal automorphic space. -/
def complexConj (n : ℕ) : CuspidalAutomorphicForms K n ≃L[ℂ] CuspidalAutomorphicForms K n :=
  (AutomorphicForms.complexConj (K := K) n).ofSubmodules _ _
    (cuspidalAutomorphicSubrepresentation_map_complexConj (K := K) n)

@[simp] theorem complexConj_val (n : ℕ) (f : CuspidalAutomorphicForms K n) :
    (complexConj (K := K) n f).val = AutomorphicForms.complexConj (K := K) n f.val := rfl

@[simp] theorem evaluate_complexConj (n : ℕ) (f : CuspidalAutomorphicForms K n)
    (x : AdelicGL K n) :
    evaluate K n (automorphicToContinuous K n (complexConj (K := K) n f).val) x =
      evaluate K n (automorphicToContinuous K n f.val) (CMConjugation.adelicConj K n x) :=
  AutomorphicForms.evaluate_complexConj (K := K) n f.val x

@[simp] theorem complexConj_complexConj (n : ℕ) (f : CuspidalAutomorphicForms K n) :
    complexConj (K := K) n (complexConj (K := K) n f) = f := by
  apply Subtype.ext
  exact AutomorphicForms.complexConj_complexConj (K := K) n f.val

@[simp] theorem complexConj_symm (n : ℕ) :
    (complexConj (K := K) n).symm = complexConj (K := K) n := by
  apply ContinuousLinearEquiv.ext
  funext f
  apply (complexConj (K := K) n).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, complexConj_complexConj]

/-- The restricted equivalence has the actual finite adelic covariance. -/
theorem complexConj_finiteRightAction (n : ℕ) (d : FiniteAdelicGL K n)
    (f : CuspidalAutomorphicForms K n) :
    complexConj (K := K) n
        (cuspidalAutomorphicFiniteRightAction K n (CMConjugation.finiteConj K n d) f) =
      cuspidalAutomorphicFiniteRightAction K n d (complexConj (K := K) n f) := by
  apply Subtype.ext
  exact AutomorphicForms.complexConj_finiteRightAction n d f.val

/-- The existing inclusion into all automorphic forms commutes with CM pullback. -/
theorem inclusion_complexConj (n : ℕ) (f : CuspidalAutomorphicForms K n) :
    restrictedAutomorphicInclusion K n (cuspidalSubrepresentation (K := K) (n := n))
        (complexConj (K := K) n f) =
      AutomorphicForms.complexConj (K := K) n
        (restrictedAutomorphicInclusion K n
          (cuspidalSubrepresentation (K := K) (n := n)) f) := rfl

end CuspidalAutomorphicForms

private theorem centralCharacterCuspidalSubrepresentation_map_complexConj
    (n : ℕ) (χ : HeckeCharacter K) :
    (centralCharacterCuspidalSubrepresentation K n χ).toSubmodule.map
        (AutomorphicForms.complexConj n).toLinearMap =
      (centralCharacterCuspidalSubrepresentation K n χ.complexConj).toSubmodule := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (AutomorphicForms.complexConj_mem_centralCharacterCuspidal_iff n χ g).mpr hg
  · intro hf
    obtain ⟨g, rfl⟩ := (AutomorphicForms.complexConj n).surjective f
    exact ⟨g, (AutomorphicForms.complexConj_mem_centralCharacterCuspidal_iff n χ g).mp hf,
      rfl⟩

namespace CentralCharacterCuspidalForms

/-- CM pullback between actual cusp spaces with corresponding central characters. -/
def complexConj (n : ℕ) (χ : HeckeCharacter K) :
    CentralCharacterCuspidalForms K n χ ≃L[ℂ]
      CentralCharacterCuspidalForms K n χ.complexConj :=
  (AutomorphicForms.complexConj n).ofSubmodules _ _
    (centralCharacterCuspidalSubrepresentation_map_complexConj n χ)

@[simp] theorem complexConj_val (n : ℕ) (χ : HeckeCharacter K)
    (f : CentralCharacterCuspidalForms K n χ) :
    (complexConj n χ f).val = AutomorphicForms.complexConj n f.val := rfl

@[simp] theorem complexConj_symm_val (n : ℕ) (χ : HeckeCharacter K)
    (f : CentralCharacterCuspidalForms K n χ.complexConj) :
    ((complexConj n χ).symm f).val = AutomorphicForms.complexConj n f.val := by
  change (AutomorphicForms.complexConj n).symm f.val = _
  rw [AutomorphicForms.complexConj_symm]

@[simp] theorem evaluate_complexConj (n : ℕ) (χ : HeckeCharacter K)
    (f : CentralCharacterCuspidalForms K n χ) (x : AdelicGL K n) :
    evaluate K n (automorphicToContinuous K n (complexConj n χ f).val) x =
      evaluate K n (automorphicToContinuous K n f.val) (CMConjugation.adelicConj K n x) :=
  AutomorphicForms.evaluate_complexConj n f.val x

@[simp] theorem evaluate_complexConj_symm (n : ℕ) (χ : HeckeCharacter K)
    (f : CentralCharacterCuspidalForms K n χ.complexConj) (x : AdelicGL K n) :
    evaluate K n (automorphicToContinuous K n ((complexConj n χ).symm f).val) x =
      evaluate K n (automorphicToContinuous K n f.val) (CMConjugation.adelicConj K n x) := by
  rw [complexConj_symm_val]
  exact AutomorphicForms.evaluate_complexConj n f.val x

theorem complexConj_finiteRightAction (n : ℕ) (χ : HeckeCharacter K)
    (d : FiniteAdelicGL K n) (f : CentralCharacterCuspidalForms K n χ) :
    complexConj n χ
        (centralCharacterCuspidalFiniteRightAction K n χ
          (CMConjugation.finiteConj K n d) f) =
      centralCharacterCuspidalFiniteRightAction K n χ.complexConj d
        (complexConj n χ f) := by
  apply Subtype.ext
  exact AutomorphicForms.complexConj_finiteRightAction n d f.val

/-- Inclusion into all automorphic forms retains the actual CM map. -/
theorem inclusion_complexConj (n : ℕ) (χ : HeckeCharacter K)
    (f : CentralCharacterCuspidalForms K n χ) :
    restrictedAutomorphicInclusion K n
        (centralCharacterSubrepresentation K n χ.complexConj ⊓
          cuspidalSubrepresentation (K := K) (n := n)) (complexConj n χ f) =
      AutomorphicForms.complexConj n
        (restrictedAutomorphicInclusion K n
          (centralCharacterSubrepresentation K n χ ⊓
            cuspidalSubrepresentation (K := K) (n := n)) f) := rfl

end CentralCharacterCuspidalForms
end Langlands.Automorphic

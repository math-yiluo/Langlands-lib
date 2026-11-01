import Langlands.Automorphic.CuspidalForms
import Langlands.Automorphic.SmoothArithmeticActions
import Langlands.Automorphic.CenterFiniteArithmeticTransport
import Langlands.Automorphic.GrowthArithmeticTransport

/-! # Actual CM pullback on automorphic forms -/

noncomputable section
universe uK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions AdelicGLTransport

variable {K : Type uK} [Field K] [NumberField K] [NumberField.IsCMField K]

local instance automorphicCMRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions K n) :=
  Submodule.addCommGroup _
local instance automorphicCMContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance automorphicCMFiniteSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance automorphicCMFormGroup (n : ℕ) : AddCommGroup (AutomorphicForms K n) :=
  Submodule.addCommGroup _
local instance automorphicCMCentralCharacterGroup (n : ℕ) (χ : HeckeCharacter K) :
    AddCommGroup (CentralCharacterAutomorphicForms K n χ) := Submodule.addCommGroup _

/-- All four automorphic conditions are preserved and reflected by actual CM pullback. -/
theorem isAutomorphicForm_smoothComplexConj_iff (n : ℕ) (f : SmoothRationalFunctions K n) :
    IsAutomorphicForm K n (smoothComplexConj n f) ↔ IsAutomorphicForm K n f := by
  unfold IsAutomorphicForm
  exact and_congr (hasFiniteLevel_smoothComplexConj_iff n f)
    (and_congr (isStandardInfiniteFinite_smoothComplexConj_iff n f)
      (and_congr
        (isCenterFinite_smoothEquiv_iff n
          (NumberField.IsCMField.complexConj K).toRingEquiv f)
        (arithmeticComap_hasPolynomialGrowth_iff n
          (NumberField.IsCMField.complexConj K).toRingEquiv f.val)))

@[simp]
theorem finiteSmoothComplexConj_mem_automorphic_iff (n : ℕ)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothComplexConj n f ∈ automorphicSubrepresentation K n ↔
      f ∈ automorphicSubrepresentation K n := by
  rw [mem_automorphicSubrepresentation, mem_automorphicSubrepresentation,
    ← smoothComplexConj_finiteSmoothInclusion]
  exact isAutomorphicForm_smoothComplexConj_iff n _

private theorem automorphicSubrepresentation_map_complexConj (n : ℕ) :
    (automorphicSubrepresentation K n).toSubmodule.map
        (finiteSmoothComplexConj n).toLinearMap =
      (automorphicSubrepresentation K n).toSubmodule := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (finiteSmoothComplexConj_mem_automorphic_iff n g).mpr hg
  · intro hf
    obtain ⟨g, rfl⟩ := (finiteSmoothComplexConj n).surjective f
    exact ⟨g, (finiteSmoothComplexConj_mem_automorphic_iff n g).mp hf, rfl⟩

namespace AutomorphicForms

/-- Direct CM conjugation of the argument on the existing actual automorphic space. -/
def complexConj (n : ℕ) : AutomorphicForms K n ≃L[ℂ] AutomorphicForms K n :=
  (finiteSmoothComplexConj n).ofSubmodules _ _
    (automorphicSubrepresentation_map_complexConj n)

@[simp] theorem complexConj_val (n : ℕ) (f : AutomorphicForms K n) :
    (complexConj n f).val = finiteSmoothComplexConj n f.val := rfl

@[simp] theorem toContinuous_complexConj (n : ℕ) (f : AutomorphicForms K n) :
    automorphicToContinuous K n (complexConj n f) =
      ContinuousRationalFunctions.complexConj n (automorphicToContinuous K n f) := rfl

@[simp] theorem evaluate_complexConj (n : ℕ) (f : AutomorphicForms K n)
    (x : AdelicGL K n) :
    evaluate K n (automorphicToContinuous K n (complexConj n f)) x =
      evaluate K n (automorphicToContinuous K n f) (CMConjugation.adelicConj K n x) :=
  ContinuousRationalFunctions.evaluate_complexConj n _ x

@[simp] theorem complexConj_complexConj (n : ℕ) (f : AutomorphicForms K n) :
    complexConj n (complexConj n f) = f := by
  apply Subtype.ext
  exact finiteSmoothComplexConj_finiteSmoothComplexConj n f.val

@[simp] theorem complexConj_symm (n : ℕ) :
    (complexConj (K := K) n).symm = complexConj n := by
  apply ContinuousLinearEquiv.ext
  funext f
  apply (complexConj n).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, complexConj_complexConj]

/-- The finite adelic action transforms by the actual arithmetic CM matrix map. -/
theorem complexConj_finiteRightAction (n : ℕ) (d : FiniteAdelicGL K n)
    (f : AutomorphicForms K n) :
    complexConj n (automorphicFiniteRightAction K n (CMConjugation.finiteConj K n d) f) =
      automorphicFiniteRightAction K n d (complexConj n f) := by
  apply Subtype.ext
  change finiteSmoothEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv
      (finiteSmoothRightAction K n
        (AdelicGL.ofFinite K n (CMConjugation.finiteConj K n d)) f.val) =
    finiteSmoothRightAction K n (AdelicGL.ofFinite K n d)
      (finiteSmoothEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv f.val)
  rw [← finiteEquiv_complexConj, ← adelicEquiv_ofFinite]
  exact finiteSmoothEquiv_rightAction n _ _ f.val

/-- The complete automorphic pullback retains the proved differential covariance
in its actual finite-smooth ambient realization. -/
theorem complexConj_envelopingAction (n : ℕ) (u : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : AutomorphicForms K n) :
    finiteSmoothComplexConj n
        (finiteSmoothEnvelopingAction K n
          (ArchimedeanLieTransport.envelopingEquiv n
            (NumberField.IsCMField.complexConj K).toRingEquiv u) f.val) =
      finiteSmoothEnvelopingAction K n u (complexConj n f).val :=
  finiteSmoothEquiv_envelopingAction n
    (NumberField.IsCMField.complexConj K).toRingEquiv u f.val

@[simp] theorem complexConj_mem_centralCharacter_iff (n : ℕ)
    (χ : HeckeCharacter K) (f : AutomorphicForms K n) :
    complexConj n f ∈ centralCharacterAutomorphicSubrepresentation K n χ.complexConj ↔
      f ∈ centralCharacterAutomorphicSubrepresentation K n χ :=
  ContinuousRationalFunctions.complexConj_mem_centralCharacter_iff n χ _

/-- A specified finite level is carried to its actual CM preimage level. -/
theorem complexConj_mem_level_iff (n : ℕ) (U : Subgroup (FiniteAdelicGL K n))
    (f : AutomorphicForms K n) :
    automorphicToContinuous K n (complexConj n f) ∈
        levelSubmodule K n (U.comap (CMConjugation.finiteConj K n).toMonoidHom) ↔
      automorphicToContinuous K n f ∈ levelSubmodule K n U := by
  have h := arithmeticComap_mem_level_iff n
    (NumberField.IsCMField.complexConj K).toRingEquiv U
    (automorphicToContinuous K n f)
  rwa [finiteEquiv_complexConj] at h

end AutomorphicForms

private theorem centralCharacterAutomorphicSubrepresentation_map_complexConj
    (n : ℕ) (χ : HeckeCharacter K) :
    (centralCharacterAutomorphicSubrepresentation K n χ).toSubmodule.map
        (AutomorphicForms.complexConj n).toLinearMap =
      (centralCharacterAutomorphicSubrepresentation K n χ.complexConj).toSubmodule := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (AutomorphicForms.complexConj_mem_centralCharacter_iff n χ g).mpr hg
  · intro hf
    obtain ⟨g, rfl⟩ := (AutomorphicForms.complexConj n).surjective f
    exact ⟨g, (AutomorphicForms.complexConj_mem_centralCharacter_iff n χ g).mp hf, rfl⟩

namespace CentralCharacterAutomorphicForms

/-- Actual CM pullback between the corresponding specified-character automorphic spaces. -/
def complexConj (n : ℕ) (χ : HeckeCharacter K) :
    CentralCharacterAutomorphicForms K n χ ≃L[ℂ]
      CentralCharacterAutomorphicForms K n χ.complexConj :=
  (AutomorphicForms.complexConj n).ofSubmodules _ _
    (centralCharacterAutomorphicSubrepresentation_map_complexConj n χ)

@[simp] theorem complexConj_val (n : ℕ) (χ : HeckeCharacter K)
    (f : CentralCharacterAutomorphicForms K n χ) :
    (complexConj n χ f).val = AutomorphicForms.complexConj n f.val := rfl

@[simp] theorem complexConj_symm_val (n : ℕ) (χ : HeckeCharacter K)
    (f : CentralCharacterAutomorphicForms K n χ.complexConj) :
    ((complexConj n χ).symm f).val = AutomorphicForms.complexConj n f.val := by
  change (AutomorphicForms.complexConj n).symm f.val = _
  rw [AutomorphicForms.complexConj_symm]

@[simp] theorem evaluate_complexConj (n : ℕ) (χ : HeckeCharacter K)
    (f : CentralCharacterAutomorphicForms K n χ) (x : AdelicGL K n) :
    evaluate K n (automorphicToContinuous K n (complexConj n χ f).val) x =
      evaluate K n (automorphicToContinuous K n f.val) (CMConjugation.adelicConj K n x) :=
  AutomorphicForms.evaluate_complexConj n _ x

@[simp] theorem evaluate_complexConj_symm (n : ℕ) (χ : HeckeCharacter K)
    (f : CentralCharacterAutomorphicForms K n χ.complexConj) (x : AdelicGL K n) :
    evaluate K n (automorphicToContinuous K n ((complexConj n χ).symm f).val) x =
      evaluate K n (automorphicToContinuous K n f.val) (CMConjugation.adelicConj K n x) := by
  rw [complexConj_symm_val]
  exact AutomorphicForms.evaluate_complexConj n _ x

theorem complexConj_finiteRightAction (n : ℕ) (χ : HeckeCharacter K)
    (d : FiniteAdelicGL K n) (f : CentralCharacterAutomorphicForms K n χ) :
    complexConj n χ
        (centralCharacterAutomorphicFiniteRightAction K n χ
          (CMConjugation.finiteConj K n d) f) =
      centralCharacterAutomorphicFiniteRightAction K n χ.complexConj d
        (complexConj n χ f) := by
  apply Subtype.ext
  exact AutomorphicForms.complexConj_finiteRightAction n d f.val

end CentralCharacterAutomorphicForms
end Langlands.Automorphic

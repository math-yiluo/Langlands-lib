import Langlands.Automorphic.CuspidalForms
import Langlands.Automorphic.CenterFiniteArithmeticTransport
import Langlands.Automorphic.GrowthArithmeticTransport
import Langlands.Automorphic.ConstantTermArithmeticTransport
import Langlands.Global.ArchimedeanCompactTransport

/-! # Arithmetic pullback on actual automorphic and cuspidal forms

For a number-field isomorphism `e : K ≃+* L`, pullback of functions along the entrywise
arithmetic map `GL_n(𝔸_K) ≃ GL_n(𝔸_L)` preserves and reflects all four conditions defining
automorphic forms, the central-character equation (with `χ ↦ χ ∘ e`) and cuspidality.
-/

noncomputable section
universe uK uL uM

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions AdelicGLTransport

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]

local instance automorphicArithmeticRationalGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance automorphicArithmeticContinuousGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance automorphicArithmeticFiniteSmoothGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance automorphicArithmeticFormGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _

/-- Finiteness under the standard compact subgroup is preserved and reflected, using the
arithmetic invariance of that subgroup. -/
theorem isStandardInfiniteFinite_arithmeticComap_iff (n : ℕ) (e : K ≃+* L)
    (f : ContinuousRationalFunctions L n) :
    IsInfiniteFinite K n (standardInfiniteCompact K n) (arithmeticComap n e f) ↔
      IsInfiniteFinite L n (standardInfiniteCompact L n) f := by
  have h := isInfiniteFinite_arithmeticComap_iff n e (standardInfiniteCompact L n) f
  rwa [ArchimedeanCompactTransport.comap_infiniteEquiv_standardInfiniteCompact] at h

/-- All four automorphic conditions are preserved and reflected by arithmetic pullback. -/
theorem isAutomorphicForm_smoothEquiv_iff (n : ℕ) (e : K ≃+* L)
    (f : SmoothRationalFunctions L n) :
    IsAutomorphicForm K n (ContinuousRationalFunctions.smoothEquiv n e f) ↔ IsAutomorphicForm L n f := by
  unfold IsAutomorphicForm
  exact and_congr (hasFiniteLevel_arithmeticComap_iff n e f.val)
    (and_congr (isStandardInfiniteFinite_arithmeticComap_iff n e f.val)
      (and_congr (isCenterFinite_smoothEquiv_iff n e f)
        (arithmeticComap_hasPolynomialGrowth_iff n e f.val)))

@[simp]
theorem finiteSmoothEquiv_mem_automorphic_iff (n : ℕ) (e : K ≃+* L)
    (f : FiniteSmoothRationalFunctions L n) :
    finiteSmoothEquiv n e f ∈ automorphicSubrepresentation K n ↔
      f ∈ automorphicSubrepresentation L n := by
  rw [mem_automorphicSubrepresentation, mem_automorphicSubrepresentation,
    ← smoothEquiv_finiteSmoothInclusion]
  exact isAutomorphicForm_smoothEquiv_iff n e _

private theorem automorphicSubrepresentation_map_finiteSmoothEquiv (n : ℕ) (e : K ≃+* L) :
    (automorphicSubrepresentation L n).toSubmodule.map (finiteSmoothEquiv n e).toLinearMap =
      (automorphicSubrepresentation K n).toSubmodule := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (finiteSmoothEquiv_mem_automorphic_iff n e g).mpr hg
  · intro hf
    obtain ⟨g, rfl⟩ := (finiteSmoothEquiv n e).surjective f
    exact ⟨g, (finiteSmoothEquiv_mem_automorphic_iff n e g).mp hf, rfl⟩

namespace AutomorphicForms

/-- Arithmetic pullback on the actual automorphic form spaces. -/
def arithmeticEquiv (n : ℕ) (e : K ≃+* L) : AutomorphicForms L n ≃L[ℂ] AutomorphicForms K n :=
  (finiteSmoothEquiv n e).ofSubmodules _ _
    (automorphicSubrepresentation_map_finiteSmoothEquiv n e)

@[simp] theorem arithmeticEquiv_val (n : ℕ) (e : K ≃+* L) (f : AutomorphicForms L n) :
    (arithmeticEquiv n e f).val = finiteSmoothEquiv n e f.val := rfl

@[simp] theorem toContinuous_arithmeticEquiv (n : ℕ) (e : K ≃+* L) (f : AutomorphicForms L n) :
    automorphicToContinuous K n (arithmeticEquiv n e f) =
      arithmeticComap n e (automorphicToContinuous L n f) := rfl

@[simp] theorem evaluate_arithmeticEquiv (n : ℕ) (e : K ≃+* L) (f : AutomorphicForms L n)
    (x : AdelicGL K n) :
    evaluate K n (automorphicToContinuous K n (arithmeticEquiv n e f)) x =
      evaluate L n (automorphicToContinuous L n f) (adelicEquiv n e x) := rfl

@[simp] theorem arithmeticEquiv_refl (n : ℕ) (f : AutomorphicForms K n) :
    arithmeticEquiv n (RingEquiv.refl K) f = f := by
  apply Subtype.ext
  exact finiteSmoothEquiv_refl n f.val

theorem arithmeticEquiv_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M) (f : AutomorphicForms M n) :
    arithmeticEquiv n (e.trans a) f = arithmeticEquiv n e (arithmeticEquiv n a f) := by
  apply Subtype.ext
  exact finiteSmoothEquiv_trans n e a f.val

@[simp] theorem arithmeticEquiv_symm (n : ℕ) (e : K ≃+* L) :
    (arithmeticEquiv n e).symm = arithmeticEquiv n e.symm := by
  apply ContinuousLinearEquiv.ext
  funext f
  apply Subtype.ext
  change (finiteSmoothEquiv n e).symm f.val = finiteSmoothEquiv n e.symm f.val
  rw [finiteSmoothEquiv_symm]

/-- The finite adelic action transforms by the arithmetic finite matrix map. -/
theorem arithmeticEquiv_finiteRightAction (n : ℕ) (e : K ≃+* L) (d : FiniteAdelicGL K n)
    (f : AutomorphicForms L n) :
    arithmeticEquiv n e (automorphicFiniteRightAction L n (finiteEquiv n e d) f) =
      automorphicFiniteRightAction K n d (arithmeticEquiv n e f) := by
  apply Subtype.ext
  change finiteSmoothEquiv n e
      (finiteSmoothRightAction L n (AdelicGL.ofFinite L n (finiteEquiv n e d)) f.val) =
    finiteSmoothRightAction K n (AdelicGL.ofFinite K n d) (finiteSmoothEquiv n e f.val)
  rw [← adelicEquiv_ofFinite]
  exact finiteSmoothEquiv_rightAction n e _ f.val

/-- Differential covariance in the actual finite-smooth ambient realization. -/
theorem arithmeticEquiv_envelopingAction (n : ℕ) (e : K ≃+* L)
    (u : ArchimedeanGL.EnvelopingAlgebra K n) (f : AutomorphicForms L n) :
    finiteSmoothEquiv n e
        (finiteSmoothEnvelopingAction L n (ArchimedeanLieTransport.envelopingEquiv n e u) f.val) =
      finiteSmoothEnvelopingAction K n u (arithmeticEquiv n e f).val :=
  finiteSmoothEquiv_envelopingAction n e u f.val

/-- The central character transforms by the Hecke-character comap. -/
@[simp] theorem arithmeticEquiv_mem_centralCharacter_iff (n : ℕ) (e : K ≃+* L)
    (χ : HeckeCharacter L) (f : AutomorphicForms L n) :
    arithmeticEquiv n e f ∈
        centralCharacterAutomorphicSubrepresentation K n (HeckeCharacter.comap e χ) ↔
      f ∈ centralCharacterAutomorphicSubrepresentation L n χ :=
  arithmeticComap_mem_centralCharacter_iff n e χ (automorphicToContinuous L n f)

/-- A specified finite level is carried to its arithmetic preimage level. -/
theorem arithmeticEquiv_mem_level_iff (n : ℕ) (e : K ≃+* L) (U : Subgroup (FiniteAdelicGL L n))
    (f : AutomorphicForms L n) :
    automorphicToContinuous K n (arithmeticEquiv n e f) ∈
        levelSubmodule K n (U.comap (finiteEquiv n e).toMonoidHom) ↔
      automorphicToContinuous L n f ∈ levelSubmodule L n U :=
  arithmeticComap_mem_level_iff n e U (automorphicToContinuous L n f)

section Cuspidal

variable [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]

/-- Arithmetic pullback preserves and reflects the constant-term cusp condition. -/
@[simp] theorem arithmeticEquiv_mem_cuspidal_iff (n : ℕ) (e : K ≃+* L)
    (f : AutomorphicForms L n) :
    arithmeticEquiv n e f ∈ cuspidalAutomorphicSubrepresentation K n ↔
      f ∈ cuspidalAutomorphicSubrepresentation L n :=
  isCuspidal_arithmeticComap_iff n e (automorphicToContinuous L n f)

@[simp] theorem arithmeticEquiv_mem_centralCharacterCuspidal_iff (n : ℕ) (e : K ≃+* L)
    (χ : HeckeCharacter L) (f : AutomorphicForms L n) :
    arithmeticEquiv n e f ∈
        centralCharacterCuspidalSubrepresentation K n (HeckeCharacter.comap e χ) ↔
      f ∈ centralCharacterCuspidalSubrepresentation L n χ := by
  rw [mem_centralCharacterCuspidalSubrepresentation,
    mem_centralCharacterCuspidalSubrepresentation]
  exact and_congr (arithmeticEquiv_mem_centralCharacter_iff n e χ f)
    (isCuspidal_arithmeticComap_iff n e (automorphicToContinuous L n f))

end Cuspidal
end AutomorphicForms

private theorem map_arithmeticEquiv_eq (n : ℕ) (e : K ≃+* L)
    (P : Submodule ℂ (AutomorphicForms L n)) (Q : Submodule ℂ (AutomorphicForms K n))
    (h : ∀ f, AutomorphicForms.arithmeticEquiv n e f ∈ Q ↔ f ∈ P) :
    P.map (AutomorphicForms.arithmeticEquiv n e).toLinearMap = Q := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (h g).mpr hg
  · intro hf
    obtain ⟨g, rfl⟩ := (AutomorphicForms.arithmeticEquiv n e).surjective f
    exact ⟨g, (h g).mp hf, rfl⟩

namespace CentralCharacterAutomorphicForms

/-- Arithmetic pullback between corresponding specified-character automorphic spaces. -/
def arithmeticEquiv (n : ℕ) (e : K ≃+* L) (χ : HeckeCharacter L) :
    CentralCharacterAutomorphicForms L n χ ≃L[ℂ]
      CentralCharacterAutomorphicForms K n (HeckeCharacter.comap e χ) :=
  (AutomorphicForms.arithmeticEquiv n e).ofSubmodules _ _
    (map_arithmeticEquiv_eq n e _ _ (AutomorphicForms.arithmeticEquiv_mem_centralCharacter_iff n e χ))

@[simp] theorem arithmeticEquiv_val (n : ℕ) (e : K ≃+* L) (χ : HeckeCharacter L)
    (f : CentralCharacterAutomorphicForms L n χ) :
    (arithmeticEquiv n e χ f).val = AutomorphicForms.arithmeticEquiv n e f.val := rfl

theorem arithmeticEquiv_finiteRightAction (n : ℕ) (e : K ≃+* L) (χ : HeckeCharacter L)
    (d : FiniteAdelicGL K n) (f : CentralCharacterAutomorphicForms L n χ) :
    arithmeticEquiv n e χ
        (centralCharacterAutomorphicFiniteRightAction L n χ (finiteEquiv n e d) f) =
      centralCharacterAutomorphicFiniteRightAction K n (HeckeCharacter.comap e χ) d
        (arithmeticEquiv n e χ f) := by
  apply Subtype.ext
  exact AutomorphicForms.arithmeticEquiv_finiteRightAction n e d f.val

end CentralCharacterAutomorphicForms

section Cuspidal

variable [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]

local instance automorphicArithmeticCuspGroup {F : Type*} [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] (n : ℕ) : AddCommGroup (CuspidalAutomorphicForms F n) :=
  Submodule.addCommGroup _

namespace CuspidalAutomorphicForms

/-- Arithmetic pullback restricted to the actual cuspidal automorphic spaces. -/
def arithmeticEquiv (n : ℕ) (e : K ≃+* L) :
    CuspidalAutomorphicForms L n ≃L[ℂ] CuspidalAutomorphicForms K n :=
  (AutomorphicForms.arithmeticEquiv n e).ofSubmodules _ _
    (map_arithmeticEquiv_eq n e _ _ (AutomorphicForms.arithmeticEquiv_mem_cuspidal_iff n e))

@[simp] theorem arithmeticEquiv_val (n : ℕ) (e : K ≃+* L) (f : CuspidalAutomorphicForms L n) :
    (arithmeticEquiv n e f).val = AutomorphicForms.arithmeticEquiv n e f.val := rfl

@[simp] theorem evaluate_arithmeticEquiv (n : ℕ) (e : K ≃+* L) (f : CuspidalAutomorphicForms L n)
    (x : AdelicGL K n) :
    evaluate K n (automorphicToContinuous K n (arithmeticEquiv n e f).val) x =
      evaluate L n (automorphicToContinuous L n f.val) (adelicEquiv n e x) := rfl

theorem arithmeticEquiv_finiteRightAction (n : ℕ) (e : K ≃+* L) (d : FiniteAdelicGL K n)
    (f : CuspidalAutomorphicForms L n) :
    arithmeticEquiv n e (cuspidalAutomorphicFiniteRightAction L n (finiteEquiv n e d) f) =
      cuspidalAutomorphicFiniteRightAction K n d (arithmeticEquiv n e f) := by
  apply Subtype.ext
  exact AutomorphicForms.arithmeticEquiv_finiteRightAction n e d f.val

end CuspidalAutomorphicForms

namespace CentralCharacterCuspidalForms

/-- Arithmetic pullback between cusp spaces with corresponding central characters. -/
def arithmeticEquiv (n : ℕ) (e : K ≃+* L) (χ : HeckeCharacter L) :
    CentralCharacterCuspidalForms L n χ ≃L[ℂ]
      CentralCharacterCuspidalForms K n (HeckeCharacter.comap e χ) :=
  (AutomorphicForms.arithmeticEquiv n e).ofSubmodules _ _
    (map_arithmeticEquiv_eq n e _ _
      (AutomorphicForms.arithmeticEquiv_mem_centralCharacterCuspidal_iff n e χ))

@[simp] theorem arithmeticEquiv_val (n : ℕ) (e : K ≃+* L) (χ : HeckeCharacter L)
    (f : CentralCharacterCuspidalForms L n χ) :
    (arithmeticEquiv n e χ f).val = AutomorphicForms.arithmeticEquiv n e f.val := rfl

theorem arithmeticEquiv_finiteRightAction (n : ℕ) (e : K ≃+* L) (χ : HeckeCharacter L)
    (d : FiniteAdelicGL K n) (f : CentralCharacterCuspidalForms L n χ) :
    arithmeticEquiv n e χ
        (centralCharacterCuspidalFiniteRightAction L n χ (finiteEquiv n e d) f) =
      centralCharacterCuspidalFiniteRightAction K n (HeckeCharacter.comap e χ) d
        (arithmeticEquiv n e χ f) := by
  apply Subtype.ext
  exact AutomorphicForms.arithmeticEquiv_finiteRightAction n e d f.val

end CentralCharacterCuspidalForms
end Cuspidal
end Langlands.Automorphic

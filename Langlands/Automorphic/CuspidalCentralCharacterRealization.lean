import Langlands.Automorphic.CuspidalEnvelopingPreservation
import Langlands.Global.HeckeCharacter

/-! # The actual cuspidal operator space at a prescribed central character -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL ContinuousRationalFunctions

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local instance cuspidalCharacterContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance cuspidalCharacterSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance cuspidalCharacterStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance cuspidalCharacterFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _

private abbrev finiteSmoothCentralCharacterSubmodule (χ : HeckeCharacter F) :
    Submodule ℂ (FiniteSmoothRationalFunctions F n) :=
  (centralCharacterSubrepresentation F n χ).toSubmodule.comap
    (finiteSmoothRationalSubrepresentation F n).toSubmodule.subtype

private theorem centralCharacter_envelopingAction (χ : HeckeCharacter F) (a : EnvelopingAlgebra F n) :
    ∀ f : FiniteSmoothRationalFunctions F n, f ∈ finiteSmoothCentralCharacterSubmodule F n χ →
      finiteSmoothEnvelopingAction F n a f ∈ finiteSmoothCentralCharacterSubmodule F n χ := by
  intro f hf z x
  let g := AdelicGL.scalar F n z
  have hmul (b : InfiniteAdelicGL F n) (d : FiniteAdelicGL F n) :
      g * AdelicGL.pair F n b d =
        AdelicGL.pair F n (AdelicGL.infinite F n g * b) (AdelicGL.finite F n g * d) := by
    conv_lhs => rw [← AdelicGL.pair_projections F n g]
    exact AdelicGL.pair_mul F n _ _ _ _
  have hcov (d : FiniteAdelicGL F n) :
      smoothLeftTranslation F n (AdelicGL.infinite F n g)
        (finiteSmoothSlice F n (AdelicGL.finite F n g * d) f) =
        (centralIdeleCharacter F χ z : ℂ) • finiteSmoothSlice F n d f := by
    apply Subtype.ext
    funext b
    rw [smoothLeftTranslation_apply, finiteSmoothSlice_apply]
    change evaluate F n f.val _ =
      (centralIdeleCharacter F χ z : ℂ) * evaluate F n f.val (AdelicGL.pair F n b d)
    rw [← hmul]
    exact hf z (AdelicGL.pair F n b d)
  change evaluate F n (finiteSmoothEnvelopingAction F n a f).val (g * x) =
    (centralIdeleCharacter F χ z : ℂ) * evaluate F n (finiteSmoothEnvelopingAction F n a f).val x
  rw [← AdelicGL.pair_projections F n x, hmul, evaluate_finiteSmoothEnvelopingAction,
    evaluate_finiteSmoothEnvelopingAction, ← envelopingAction_leftTranslation_eval, hcov, map_smul]
  rfl

variable [CompactSpace (AdeleQuotient F)]

/-- All actual cuspidal forms with the given central character, with the three operator actions. -/
def centralCharacterCuspidalOperatorRealization (χ : HeckeCharacter F) : OperatorRealization F n where
  toSubmodule := (finiteSmoothCentralCharacterSubmodule F n χ).comap
    (automorphicOperatorCore F n).toSubmodule.subtype ⊓
      (cuspidalOperatorRealization F n).toSubmodule
  apply_mem_toSubmodule a {f} hf := by
    have hχ := (operator_invariant_iff F n (finiteSmoothCentralCharacterSubmodule F n χ)).mpr
      ⟨fun d _ h => (centralCharacterSubrepresentation F n χ).apply_mem_toSubmodule
          (AdelicGL.ofFinite F n d) h,
        fun k _ h => (centralCharacterSubrepresentation F n χ).apply_mem_toSubmodule
          (AdelicGL.ofInfinite F n k.val) h,
        centralCharacter_envelopingAction F n χ⟩
    exact ⟨hχ a f.val hf.1, (cuspidalOperatorRealization F n).apply_mem_toSubmodule a hf.2⟩

@[simp]
theorem mem_centralCharacterCuspidalOperatorRealization (χ : HeckeCharacter F)
    (f : StableAutomorphicFunctions F n) :
    f ∈ centralCharacterCuspidalOperatorRealization F n χ ↔
      f.val.val ∈ centralCharacterSubrepresentation F n χ ∧ IsCuspidal F n f.val.val :=
  Iff.rfl

@[simp]
theorem mem_fullFormImage_centralCharacterCuspidalOperatorRealization (χ : HeckeCharacter F)
    (f : AutomorphicForms F n) :
    f ∈ (centralCharacterCuspidalOperatorRealization F n χ).fullFormImage ↔
      f ∈ centralCharacterCuspidalSubrepresentation F n χ := by
  rw [OperatorRealization.mem_fullFormImage_iff, mem_centralCharacterCuspidalOperatorRealization,
    stableAutomorphicEquiv_symm_val]
  rfl

theorem centralCharacterCuspidalOperatorRealization_isCuspidal (χ : HeckeCharacter F) :
    (centralCharacterCuspidalOperatorRealization F n χ).IsCuspidal :=
  (OperatorRealization.isCuspidal_iff _).mpr fun f =>
    ((mem_centralCharacterCuspidalOperatorRealization F n χ f.val).mp f.property).2

theorem centralCharacterCuspidalOperatorRealization_hasCentralCharacter (χ : HeckeCharacter F) :
    (centralCharacterCuspidalOperatorRealization F n χ).HasCentralCharacter χ :=
  (OperatorRealization.hasCentralCharacter_iff _ χ).mpr fun f =>
    ((mem_centralCharacterCuspidalOperatorRealization F n χ f.val).mp f.property).1

end Langlands.Automorphic

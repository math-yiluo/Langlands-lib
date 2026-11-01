import Langlands.Automorphic.AmbientArithmeticTransport
import Langlands.Automorphic.Smooth
import Langlands.Global.ArchimedeanGLTransport

/-! # Arithmetic pullback on the actual smooth adelic function spaces -/

noncomputable section
universe uK uL uM

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.ContinuousRationalFunctions

open Langlands.Global AdelicGLTransport

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]

/-- The infinite slice is pulled back by the actual infinite arithmetic map. -/
theorem infiniteSlice_arithmeticComap (n : ℕ) (e : K ≃+* L)
    (b : FiniteAdelicGL K n) (f : ContinuousRationalFunctions L n)
    (a : InfiniteAdelicGL K n) :
    infiniteSlice K n b (arithmeticComap n e f) a =
      infiniteSlice L n (finiteEquiv n e b) f (infiniteEquiv n e a) := by
  change evaluate L n f (adelicEquiv n e (AdelicGL.pair K n a b)) = _
  rw [adelicEquiv_pair]
  rfl

/-- Smooth arithmetic composition proves infinite smoothness on every slice. -/
theorem arithmeticComap_mem_infiniteSmooth (n : ℕ) (e : K ≃+* L)
    {f : ContinuousRationalFunctions L n}
    (hf : f ∈ (infiniteSmoothSubrepresentation L n).toSubmodule) :
    arithmeticComap n e f ∈ (infiniteSmoothSubrepresentation K n).toSubmodule := by
  change f ∈ (⨅ b : FiniteAdelicGL L n,
    (ArchimedeanGL.smoothFunctions L n).comap (infiniteSlice L n b)) at hf
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hf
  change arithmeticComap n e f ∈ (⨅ b : FiniteAdelicGL K n,
    (ArchimedeanGL.smoothFunctions K n).comap (infiniteSlice K n b))
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro b
  let s : ArchimedeanGL.SmoothFunctions L n :=
    ⟨infiniteSlice L n (finiteEquiv n e b) f, hf _⟩
  have hs := (ArchimedeanGLTransport.smoothComap n e s).property
  have heq : infiniteSlice K n b (arithmeticComap n e f) =
      (ArchimedeanGLTransport.smoothComap n e s).val := by
    funext a
    exact infiniteSlice_arithmeticComap n e b f a
  rw [heq]
  exact hs

/-- Slice-wise infinite smoothness is preserved and reflected. -/
theorem arithmeticComap_mem_infiniteSmooth_iff (n : ℕ) (e : K ≃+* L)
    (f : ContinuousRationalFunctions L n) :
    arithmeticComap n e f ∈ (infiniteSmoothSubrepresentation K n).toSubmodule ↔
      f ∈ (infiniteSmoothSubrepresentation L n).toSubmodule := by
  constructor
  · intro hf
    simpa only [arithmeticComap_symm_apply] using
      arithmeticComap_mem_infiniteSmooth n e.symm hf
  · exact arithmeticComap_mem_infiniteSmooth n e

/-- Continuous arithmetic substitution preserves local constancy in each finite slice. -/
theorem arithmeticComap_mem_finiteLocallyConstant (n : ℕ) (e : K ≃+* L)
    {f : ContinuousRationalFunctions L n}
    (hf : f ∈ (finiteLocallyConstantSubrepresentation L n).toSubmodule) :
    arithmeticComap n e f ∈ (finiteLocallyConstantSubrepresentation K n).toSubmodule := by
  intro a
  have hc : Continuous (fun b : FiniteAdelicGL K n => finiteEquiv n e b) :=
    (finiteEquiv n e).continuous
  have h := (hf (infiniteEquiv n e a)).comp_continuous hc
  simpa only [Function.comp_def, evaluate_arithmeticComap, adelicEquiv_pair] using h

/-- Local constancy in every finite slice is preserved and reflected. -/
theorem arithmeticComap_mem_finiteLocallyConstant_iff (n : ℕ) (e : K ≃+* L)
    (f : ContinuousRationalFunctions L n) :
    arithmeticComap n e f ∈ (finiteLocallyConstantSubrepresentation K n).toSubmodule ↔
      f ∈ (finiteLocallyConstantSubrepresentation L n).toSubmodule := by
  constructor
  · intro hf
    simpa only [arithmeticComap_symm_apply] using
      arithmeticComap_mem_finiteLocallyConstant n e.symm hf
  · exact arithmeticComap_mem_finiteLocallyConstant n e

/-- A common open stabilizer pulls back to its actual arithmetic preimage. -/
theorem arithmeticComap_mem_finiteSmooth (n : ℕ) (e : K ≃+* L)
    {f : ContinuousRationalFunctions L n}
    (hf : f ∈ (finiteSmoothSubrepresentation L n).toSubmodule) :
    arithmeticComap n e f ∈ (finiteSmoothSubrepresentation K n).toSubmodule := by
  obtain ⟨U, hU⟩ := hf
  refine ⟨U.comap (finiteEquiv n e).toMonoidHom (finiteEquiv n e).continuous, ?_⟩
  exact (arithmeticComap_mem_level_iff n e U.toSubgroup f).mpr hU

/-- Existence of a common open finite stabilizer is preserved and reflected. -/
theorem arithmeticComap_mem_finiteSmooth_iff (n : ℕ) (e : K ≃+* L)
    (f : ContinuousRationalFunctions L n) :
    arithmeticComap n e f ∈ (finiteSmoothSubrepresentation K n).toSubmodule ↔
      f ∈ (finiteSmoothSubrepresentation L n).toSubmodule := by
  constructor
  · intro hf
    simpa only [arithmeticComap_symm_apply] using
      arithmeticComap_mem_finiteSmooth n e.symm hf
  · exact arithmeticComap_mem_finiteSmooth n e

/-- Both defining slice-wise smoothness conditions are preserved and reflected. -/
theorem arithmeticComap_mem_smooth_iff (n : ℕ) (e : K ≃+* L)
    (f : ContinuousRationalFunctions L n) :
    arithmeticComap n e f ∈ (smoothSubrepresentation K n).toSubmodule ↔
      f ∈ (smoothSubrepresentation L n).toSubmodule := by
  change
    (arithmeticComap n e f ∈ (infiniteSmoothSubrepresentation K n).toSubmodule ∧
      arithmeticComap n e f ∈ (finiteLocallyConstantSubrepresentation K n).toSubmodule) ↔
    (f ∈ (infiniteSmoothSubrepresentation L n).toSubmodule ∧
      f ∈ (finiteLocallyConstantSubrepresentation L n).toSubmodule)
  rw [arithmeticComap_mem_infiniteSmooth_iff, arithmeticComap_mem_finiteLocallyConstant_iff]

/-- Infinite smoothness together with a common finite stabilizer is reflected. -/
theorem arithmeticComap_mem_finiteSmoothRational_iff (n : ℕ) (e : K ≃+* L)
    (f : ContinuousRationalFunctions L n) :
    arithmeticComap n e f ∈ (finiteSmoothRationalSubrepresentation K n).toSubmodule ↔
      f ∈ (finiteSmoothRationalSubrepresentation L n).toSubmodule := by
  change
    (arithmeticComap n e f ∈ (infiniteSmoothSubrepresentation K n).toSubmodule ∧
      arithmeticComap n e f ∈ (finiteSmoothSubrepresentation K n).toSubmodule) ↔
    (f ∈ (infiniteSmoothSubrepresentation L n).toSubmodule ∧
      f ∈ (finiteSmoothSubrepresentation L n).toSubmodule)
  rw [arithmeticComap_mem_infiniteSmooth_iff, arithmeticComap_mem_finiteSmooth_iff]

private theorem arithmeticComap_submodule_map (n : ℕ) (e : K ≃+* L)
    (P : Submodule ℂ (ContinuousRationalFunctions L n))
    (Q : Submodule ℂ (ContinuousRationalFunctions K n))
    (h : ∀ f, arithmeticComap n e f ∈ Q ↔ f ∈ P) :
    P.map (arithmeticComap n e) = Q := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (h g).mpr hg
  · intro hf
    obtain ⟨g, rfl⟩ := (arithmeticEquiv n e).surjective f
    exact ⟨g, (h g).mp hf, rfl⟩

/-- Actual continuous arithmetic pullback on the existing slice-wise smooth space. -/
def smoothEquiv (n : ℕ) (e : K ≃+* L) :
    SmoothRationalFunctions L n ≃L[ℂ] SmoothRationalFunctions K n :=
  (arithmeticEquiv n e).ofSubmodules _ _
    (arithmeticComap_submodule_map n e _ _ (arithmeticComap_mem_smooth_iff n e))

@[simp] theorem evaluate_smoothEquiv (n : ℕ) (e : K ≃+* L)
    (f : SmoothRationalFunctions L n) (x : AdelicGL K n) :
    evaluate K n (smoothEquiv n e f).val x =
      evaluate L n f.val (adelicEquiv n e x) := rfl

@[simp] theorem evaluate_smoothEquiv_symm (n : ℕ) (e : K ≃+* L)
    (f : SmoothRationalFunctions K n) (x : AdelicGL L n) :
    evaluate L n ((smoothEquiv n e).symm f).val x =
      evaluate K n f.val (adelicEquiv n e.symm x) := rfl

@[simp] theorem smoothEquiv_refl (n : ℕ) (f : SmoothRationalFunctions K n) :
    smoothEquiv n (RingEquiv.refl K) f = f := by
  apply Subtype.ext
  exact arithmeticComap_refl n f.val

theorem smoothEquiv_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M)
    (f : SmoothRationalFunctions M n) :
    smoothEquiv n (e.trans a) f = smoothEquiv n e (smoothEquiv n a f) := by
  apply Subtype.ext
  exact arithmeticComap_trans n e a f.val

@[simp] theorem smoothEquiv_symm (n : ℕ) (e : K ≃+* L) :
    (smoothEquiv n e).symm = smoothEquiv n e.symm := by
  apply ContinuousLinearEquiv.ext
  funext f
  apply Subtype.ext
  rfl

theorem smoothEquiv_rightAction (n : ℕ) (e : K ≃+* L)
    (g : AdelicGL K n) (f : SmoothRationalFunctions L n) :
    smoothEquiv n e (smoothRightAction L n (adelicEquiv n e g) f) =
      smoothRightAction K n g (smoothEquiv n e f) := by
  apply Subtype.ext
  exact arithmeticComap_rightAction n e g f.val

/-- Actual pullback on real-smooth functions with a common open finite stabilizer. -/
def finiteSmoothEquiv (n : ℕ) (e : K ≃+* L) :
    FiniteSmoothRationalFunctions L n ≃L[ℂ] FiniteSmoothRationalFunctions K n :=
  (arithmeticEquiv n e).ofSubmodules _ _
    (arithmeticComap_submodule_map n e _ _
      (arithmeticComap_mem_finiteSmoothRational_iff n e))

@[simp] theorem evaluate_finiteSmoothEquiv (n : ℕ) (e : K ≃+* L)
    (f : FiniteSmoothRationalFunctions L n) (x : AdelicGL K n) :
    evaluate K n (finiteSmoothEquiv n e f).val x =
      evaluate L n f.val (adelicEquiv n e x) := rfl

@[simp] theorem evaluate_finiteSmoothEquiv_symm (n : ℕ) (e : K ≃+* L)
    (f : FiniteSmoothRationalFunctions K n) (x : AdelicGL L n) :
    evaluate L n ((finiteSmoothEquiv n e).symm f).val x =
      evaluate K n f.val (adelicEquiv n e.symm x) := rfl

@[simp] theorem finiteSmoothEquiv_refl (n : ℕ) (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothEquiv n (RingEquiv.refl K) f = f := by
  apply Subtype.ext
  exact arithmeticComap_refl n f.val

theorem finiteSmoothEquiv_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M)
    (f : FiniteSmoothRationalFunctions M n) :
    finiteSmoothEquiv n (e.trans a) f =
      finiteSmoothEquiv n e (finiteSmoothEquiv n a f) := by
  apply Subtype.ext
  exact arithmeticComap_trans n e a f.val

@[simp] theorem finiteSmoothEquiv_symm (n : ℕ) (e : K ≃+* L) :
    (finiteSmoothEquiv n e).symm = finiteSmoothEquiv n e.symm := by
  apply ContinuousLinearEquiv.ext
  funext f
  apply Subtype.ext
  rfl

theorem finiteSmoothEquiv_rightAction (n : ℕ) (e : K ≃+* L)
    (g : AdelicGL K n) (f : FiniteSmoothRationalFunctions L n) :
    finiteSmoothEquiv n e (finiteSmoothRightAction L n (adelicEquiv n e g) f) =
      finiteSmoothRightAction K n g (finiteSmoothEquiv n e f) := by
  apply Subtype.ext
  exact arithmeticComap_rightAction n e g f.val

/-- Pullback commutes with the actual inclusion from common stabilizers to smooth slices. -/
theorem smoothEquiv_finiteSmoothInclusion (n : ℕ) (e : K ≃+* L)
    (f : FiniteSmoothRationalFunctions L n) :
    smoothEquiv n e (finiteSmoothInclusion L n f) =
      finiteSmoothInclusion K n (finiteSmoothEquiv n e f) := by
  apply Subtype.ext
  rfl

/-- The specified central character transforms by the actual Hecke-character comap. -/
def smoothCentralCharacterEquiv (n : ℕ) (e : K ≃+* L) (χ : HeckeCharacter L) :
    (smoothCentralCharacterSubrepresentation L n χ).toSubmodule ≃L[ℂ]
      (smoothCentralCharacterSubrepresentation K n (HeckeCharacter.comap e χ)).toSubmodule :=
  (arithmeticEquiv n e).ofSubmodules _ _
    (arithmeticComap_submodule_map n e _ _ (fun f => by
      change
        (arithmeticComap n e f ∈ (smoothSubrepresentation K n).toSubmodule ∧
          arithmeticComap n e f ∈
            (centralCharacterSubrepresentation K n (HeckeCharacter.comap e χ)).toSubmodule) ↔
        (f ∈ (smoothSubrepresentation L n).toSubmodule ∧
          f ∈ (centralCharacterSubrepresentation L n χ).toSubmodule)
      rw [arithmeticComap_mem_smooth_iff, arithmeticComap_mem_centralCharacter_iff]))

@[simp] theorem evaluate_smoothCentralCharacterEquiv (n : ℕ) (e : K ≃+* L)
    (χ : HeckeCharacter L) (f : (smoothCentralCharacterSubrepresentation L n χ).toSubmodule)
    (x : AdelicGL K n) :
    evaluate K n (smoothCentralCharacterEquiv n e χ f).val x =
      evaluate L n f.val (adelicEquiv n e x) := rfl

@[simp] theorem evaluate_smoothCentralCharacterEquiv_symm (n : ℕ) (e : K ≃+* L)
    (χ : HeckeCharacter L)
    (f : (smoothCentralCharacterSubrepresentation K n (HeckeCharacter.comap e χ)).toSubmodule)
    (x : AdelicGL L n) :
    evaluate L n ((smoothCentralCharacterEquiv n e χ).symm f).val x =
      evaluate K n f.val (adelicEquiv n e.symm x) := rfl

theorem smoothCentralCharacterEquiv_rightAction (n : ℕ) (e : K ≃+* L)
    (χ : HeckeCharacter L) (g : AdelicGL K n)
    (f : (smoothCentralCharacterSubrepresentation L n χ).toSubmodule) :
    smoothCentralCharacterEquiv n e χ
        ((smoothCentralCharacterSubrepresentation L n χ).toRepresentation (adelicEquiv n e g) f) =
      (smoothCentralCharacterSubrepresentation K n (HeckeCharacter.comap e χ)).toRepresentation g
        (smoothCentralCharacterEquiv n e χ f) := by
  apply Subtype.ext
  exact arithmeticComap_rightAction n e g f.val

end Langlands.Automorphic.ContinuousRationalFunctions

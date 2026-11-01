import Langlands.Global.AdeleQuotientTransport
import Langlands.Automorphic.ConstantTerm
import Langlands.Automorphic.AmbientArithmeticTransport
import Langlands.Automorphic.CuspidalDeterminantMultiplier
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Arithmetic covariance of actual normalized constant terms -/

noncomputable section
universe uK uL uM

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory

namespace Langlands.Global.AdeleQuotientTransport

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]

/-- Entrywise arithmetic transport on matrices over the actual additive adele quotient. -/
def matrixEquiv (a b : ℕ) (e : K ≃+* L) :
    Matrix (Fin a) (Fin b) (AdeleQuotient K) ≃ₜ+
      Matrix (Fin a) (Fin b) (AdeleQuotient L) where
  toFun X := X.map (quotientEquiv e)
  invFun X := X.map (quotientEquiv e).symm
  left_inv X := by
    apply Matrix.ext
    intro i j
    exact (quotientEquiv e).symm_apply_apply (X i j)
  right_inv X := by
    apply Matrix.ext
    intro i j
    exact (quotientEquiv e).apply_symm_apply (X i j)
  map_add' X Y := by
    apply Matrix.ext
    intro i j
    exact map_add (quotientEquiv e) (X i j) (Y i j)
  continuous_toFun := continuous_pi fun i =>
    continuous_pi fun j => (quotientEquiv e).continuous.comp
      ((continuous_apply j).comp (continuous_apply i))
  continuous_invFun := continuous_pi fun i =>
    continuous_pi fun j => (quotientEquiv e).symm.continuous.comp
      ((continuous_apply j).comp (continuous_apply i))

@[simp] theorem matrixEquiv_apply (a b : ℕ) (e : K ≃+* L)
    (X : Matrix (Fin a) (Fin b) (AdeleQuotient K)) (i : Fin a) (j : Fin b) :
    matrixEquiv a b e X i j = quotientEquiv e (X i j) := rfl

@[simp] theorem matrixEquiv_symm_apply (a b : ℕ) (e : K ≃+* L)
    (X : Matrix (Fin a) (Fin b) (AdeleQuotient L)) (i : Fin a) (j : Fin b) :
    (matrixEquiv a b e).symm X i j = (quotientEquiv e).symm (X i j) := rfl

@[simp] theorem matrixEquiv_mk (a b : ℕ) (e : K ≃+* L)
    (X : Matrix (Fin a) (Fin b) (Adeles K)) :
    matrixEquiv a b e (matrixQuotientMap X) =
      matrixQuotientMap (X.map (AdelicFunctoriality.adeleEquiv e)) := rfl

@[simp] theorem matrixEquiv_refl (a b : ℕ) :
    matrixEquiv a b (RingEquiv.refl K) =
      ContinuousAddEquiv.refl (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := by
  apply ContinuousAddEquiv.ext
  intro X
  apply Matrix.ext
  intro i j
  simp only [matrixEquiv_apply, quotientEquiv_refl, ContinuousAddEquiv.refl_apply]

theorem matrixEquiv_trans (a b : ℕ) (e : K ≃+* L) (c : L ≃+* M) :
    matrixEquiv a b (e.trans c) = (matrixEquiv a b e).trans (matrixEquiv a b c) := by
  apply ContinuousAddEquiv.ext
  intro X
  apply Matrix.ext
  intro i j
  simp only [matrixEquiv_apply, quotientEquiv_trans, ContinuousAddEquiv.trans_apply]

@[simp] theorem matrixEquiv_symm (a b : ℕ) (e : K ≃+* L) :
    (matrixEquiv a b e).symm = matrixEquiv a b e.symm := by
  apply ContinuousAddEquiv.ext
  intro X
  apply Matrix.ext
  intro i j
  simp only [matrixEquiv_symm_apply, matrixEquiv_apply, quotientEquiv_symm]

section Haar

local instance (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace (AdeleQuotient F) := borel _
local instance (F : Type*) [Field F] [NumberField F] :
    BorelSpace (AdeleQuotient F) := ⟨rfl⟩
local instance (F : Type*) [Field F] [NumberField F] (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) (AdeleQuotient F)) := borel _
local instance (F : Type*) [Field F] [NumberField F] (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) (AdeleQuotient F)) := ⟨rfl⟩

variable [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]

/-- Actual quotient transport preserves the probability normalization of Haar measure. -/
theorem map_adeleQuotientHaar (e : K ≃+* L) :
    Measure.map (quotientEquiv e) (adeleQuotientHaar K) = adeleQuotientHaar L := by
  let := adeleQuotientHaar_isAddHaarMeasure K
  let := adeleQuotientHaar_isAddHaarMeasure L
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- The normalized measure on the entire block-unipotent quotient is preserved. -/
theorem map_matrixQuotientHaar (a b : ℕ) (e : K ≃+* L) :
    Measure.map (matrixEquiv a b e) (matrixQuotientHaar K a b) =
      matrixQuotientHaar L a b := by
  let := matrixQuotientHaar_isAddHaarMeasure K a b
  let := matrixQuotientHaar_isAddHaarMeasure L a b
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- Change of variables for complex integrals on the actual matrix quotient. -/
theorem integral_matrixEquiv (a b : ℕ) (e : K ≃+* L)
    (f : Matrix (Fin a) (Fin b) (AdeleQuotient L) → ℂ) :
    (∫ X, f (matrixEquiv a b e X) ∂matrixQuotientHaar K a b) =
      ∫ X, f X ∂matrixQuotientHaar L a b := by
  have h := integral_map_equiv (μ := matrixQuotientHaar K a b)
    (matrixEquiv a b e).toHomeomorph.toMeasurableEquiv f
  rw [show Measure.map (matrixEquiv a b e).toHomeomorph.toMeasurableEquiv
      (matrixQuotientHaar K a b) = matrixQuotientHaar L a b from
    map_matrixQuotientHaar a b e] at h
  exact h.symm

end Haar
end Langlands.Global.AdeleQuotientTransport

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear ContinuousRationalFunctions
open AdelicGLTransport AdeleQuotientTransport

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]

/-- Actual adelic arithmetic transport commutes with the fixed block embedding. -/
theorem adelicEquiv_blockUnipotent (n : ℕ) (e : K ≃+* L)
    {a b : ℕ} (h : a + b = n) (X : Matrix (Fin a) (Fin b) (Adeles K)) :
    adelicEquiv n e (blockUnipotent h X) =
      blockUnipotent h (X.map (AdelicFunctoriality.adeleEquiv e)) :=
  map_blockUnipotent (AdelicFunctoriality.adeleEquiv e).toRingHom h X

/-- The lift-independent integrand transforms through the actual quotient map. -/
theorem constantTermIntegrand_arithmeticComap (n : ℕ) (e : K ≃+* L)
    {a b : ℕ} (h : a + b = n) (f : ContinuousRationalFunctions L n)
    (g : AdelicGL K n) (X : Matrix (Fin a) (Fin b) (AdeleQuotient K)) :
    constantTermIntegrand K n h (arithmeticComap n e f) g X =
      constantTermIntegrand L n h f (adelicEquiv n e g) (matrixEquiv a b e X) := by
  have hX := matrixQuotientMap_matrixLift X
  rw [← hX, matrixEquiv_mk, constantTermIntegrand_mk, constantTermIntegrand_mk,
    evaluate_arithmeticComap, map_mul, adelicEquiv_blockUnipotent]

variable [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]

/-- Constant terms commute with arithmetic pullback, with the same normalized measure. -/
theorem constantTerm_arithmeticComap (n : ℕ) (e : K ≃+* L)
    {a b : ℕ} (h : a + b = n) (f : ContinuousRationalFunctions L n)
    (g : AdelicGL K n) :
    constantTerm K n h (arithmeticComap n e f) g =
      constantTerm L n h f (adelicEquiv n e g) := by
  unfold constantTerm
  simp_rw [constantTermIntegrand_arithmeticComap]
  exact integral_matrixEquiv a b e _

/-- Cuspidality is preserved and reflected for the actual constant-term condition. -/
theorem isCuspidal_arithmeticComap_iff (n : ℕ) (e : K ≃+* L)
    (f : ContinuousRationalFunctions L n) :
    IsCuspidal K n (arithmeticComap n e f) ↔ IsCuspidal L n f := by
  constructor
  · intro hf a b h ha hb g
    obtain ⟨x, rfl⟩ := (adelicEquiv n e).surjective g
    rw [← constantTerm_arithmeticComap]
    exact hf a b h ha hb x
  · intro hf a b h ha hb g
    rw [constantTerm_arithmeticComap]
    exact hf a b h ha hb _

private theorem cuspidalSubrepresentation_map_arithmeticComap (n : ℕ) (e : K ≃+* L) :
    (cuspidalSubrepresentation (K := L) (n := n)).toSubmodule.map
        (arithmeticComap n e) =
      (cuspidalSubrepresentation (K := K) (n := n)).toSubmodule := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (isCuspidal_arithmeticComap_iff n e g).mpr hg
  · intro hf
    obtain ⟨g, rfl⟩ := (ContinuousRationalFunctions.arithmeticEquiv n e).surjective f
    exact ⟨g, (isCuspidal_arithmeticComap_iff n e g).mp hf, rfl⟩

namespace CuspidalContinuousFunctions

/-- Arithmetic pullback on the existing actual continuous cuspidal function spaces. -/
def arithmeticEquiv (n : ℕ) (e : K ≃+* L) :
    CuspidalContinuousFunctions (F := L) n ≃L[ℂ]
      CuspidalContinuousFunctions (F := K) n :=
  (ContinuousRationalFunctions.arithmeticEquiv n e).ofSubmodules _ _
    (cuspidalSubrepresentation_map_arithmeticComap n e)

@[simp] theorem evaluate_arithmeticEquiv (n : ℕ) (e : K ≃+* L)
    (f : CuspidalContinuousFunctions (F := L) n) (x : AdelicGL K n) :
    evaluate K n (arithmeticEquiv n e f).val x =
      evaluate L n f.val (adelicEquiv n e x) := rfl

@[simp] theorem evaluate_arithmeticEquiv_symm (n : ℕ) (e : K ≃+* L)
    (f : CuspidalContinuousFunctions (F := K) n) (x : AdelicGL L n) :
    evaluate L n ((arithmeticEquiv n e).symm f).val x =
      evaluate K n f.val (adelicEquiv n e.symm x) := rfl

@[simp] theorem arithmeticEquiv_refl (n : ℕ) :
    arithmeticEquiv n (RingEquiv.refl K) =
      ContinuousLinearEquiv.refl ℂ (CuspidalContinuousFunctions (F := K) n) := by
  apply ContinuousLinearEquiv.ext
  funext f
  apply Subtype.ext
  exact arithmeticComap_refl n f.val

variable [CompactSpace (AdeleQuotient M)]

/-- Function transport is contravariant in the field isomorphism. -/
theorem arithmeticEquiv_trans (n : ℕ) (e : K ≃+* L) (c : L ≃+* M) :
    arithmeticEquiv n (e.trans c) =
      (arithmeticEquiv n c).trans (arithmeticEquiv n e) := by
  apply ContinuousLinearEquiv.ext
  funext f
  apply Subtype.ext
  exact arithmeticComap_trans n e c f.val

@[simp] theorem arithmeticEquiv_symm (n : ℕ) (e : K ≃+* L) :
    (arithmeticEquiv n e).symm = arithmeticEquiv n e.symm := by
  apply ContinuousLinearEquiv.ext
  funext f
  apply Subtype.ext
  rfl

/-- Full right translation is intertwined through the actual adelic arithmetic map. -/
theorem arithmeticEquiv_rightAction (n : ℕ) (e : K ≃+* L) (g : AdelicGL K n)
    (f : CuspidalContinuousFunctions (F := L) n) :
    arithmeticEquiv n e
        ((cuspidalSubrepresentation (K := L) (n := n)).toRepresentation
          (adelicEquiv n e g) f) =
      (cuspidalSubrepresentation (K := K) (n := n)).toRepresentation g
        (arithmeticEquiv n e f) := by
  apply Subtype.ext
  exact arithmeticComap_rightAction n e g f.val

end CuspidalContinuousFunctions

section CM
variable [NumberField.IsCMField K]

/-- The actual CM pullback preserves and reflects the vanishing of constant terms. -/
theorem isCuspidal_complexConj_iff (n : ℕ) (f : ContinuousRationalFunctions K n) :
    IsCuspidal K n (ContinuousRationalFunctions.complexConj n f) ↔ IsCuspidal K n f :=
  isCuspidal_arithmeticComap_iff n (NumberField.IsCMField.complexConj K).toRingEquiv f

end CM
end Langlands.Automorphic

import Langlands.Automorphic.AssociatedAdditiveInputs
import Langlands.Automorphic.CuspidalWhittaker.MixedTraceFormula
import Langlands.Global.Factors.CuspidalPairFiniteLayer

/-! # Standard additive inputs for the ordinary pair integrals -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open NumberField

namespace Langlands.Global.HeckeFunctionalEquation

open Automorphic.CuspidalWhittaker
open Langlands.LocalFactor.Archimedean

variable (F : Type u) [Field F] [NumberField F]

/-- The global trace character has the standard real character at each real place. -/
theorem standardGlobalAdditiveCharacter_isRealComponent
    (v : InfinitePlace F) (hv : v.IsReal) :
    IsRealAdditiveComponent (standardGlobalAdditiveCharacter F) v hv 1 := by
  classical
  intro x
  let vr : {w : InfinitePlace F // w.IsReal} := ⟨v, hv⟩
  let xR := InfinitePlace.Completion.ringEquivRealOfIsReal hv x
  have hcoords : InfiniteAdeleRing.ringEquiv_mixedSpace F (Pi.single v x) = (Pi.single vr xR, 0) := by
    rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    congr 1
    · funext w
      by_cases hw : w = vr
      · subst w
        simp [vr, xR]
      · have hval : w.1 ≠ v := fun h => hw (Subtype.ext h)
        simp [Pi.single_eq_of_ne hval, Pi.single_eq_of_ne hw]
    · funext w
      have hval : w.1 ≠ v := fun h =>
        (InfinitePlace.not_isReal_iff_isComplex.mpr w.2) (h.symm ▸ hv)
      simp [Pi.single_eq_of_ne hval]
  rw [standardGlobalAdditiveCharacter_apply, adelicCharacter_of_integral F _ (zero_mem _),
    infiniteTrace_apply, hcoords, mixedTrace_single_real, realScaledCharacter_apply,
    Units.val_one, one_mul]
  rfl

/-- The global trace character has the standard complex trace character at each complex place. -/
theorem standardGlobalAdditiveCharacter_isComplexComponent
    (v : InfinitePlace F) (hv : v.IsComplex) :
    IsComplexAdditiveComponent (standardGlobalAdditiveCharacter F) v hv 1 := by
  classical
  intro x
  let vc : {w : InfinitePlace F // w.IsComplex} := ⟨v, hv⟩
  let xC := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv x
  have hcoords : InfiniteAdeleRing.ringEquiv_mixedSpace F (Pi.single v x) = (0, Pi.single vc xC) := by
    rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    congr 1
    · funext w
      have hval : w.1 ≠ v := fun h =>
        (InfinitePlace.not_isReal_iff_isComplex.mpr hv) (h ▸ w.2)
      simp [Pi.single_eq_of_ne hval]
    · funext w
      by_cases hw : w = vc
      · subst w
        simp [vc, xC]
      · have hval : w.1 ≠ v := fun h => hw (Subtype.ext h)
        simp [Pi.single_eq_of_ne hval, Pi.single_eq_of_ne hw]
  rw [standardGlobalAdditiveCharacter_apply, adelicCharacter_of_integral F _ (zero_mem _),
    infiniteTrace_apply, hcoords, mixedTrace_single_complex, complexScaledCharacter_apply,
    Units.val_one, one_mul, Algebra.trace_complex_apply]
  rfl

/-- A finite set containing the conductor support of the standard global trace character. -/
def standardGlobalAdditiveSupport : Finset (FinitePlace F) :=
  (CuspidalPairFunctionalEquation.exists_finiteAdditiveSupport (standardGlobalAdditiveCharacter F)
    (standardGlobalAdditiveCharacter_diagonal F)).choose

/-- Any enlargement of the chosen support is valid for the partial integrals. -/
theorem standardGlobalAdditiveSupport_spec {S : Finset (FinitePlace F)}
    (hS : standardGlobalAdditiveSupport F ⊆ S) :
    FunctionalEquationComparison.FiniteAdditiveSupport (standardGlobalAdditiveCharacter F) S :=
  CuspidalPairFunctionalEquation.finiteAdditiveSupport_mono
    (CuspidalPairFunctionalEquation.exists_finiteAdditiveSupport (standardGlobalAdditiveCharacter F)
      (standardGlobalAdditiveCharacter_diagonal F)).choose_spec hS

end Langlands.Global.HeckeFunctionalEquation

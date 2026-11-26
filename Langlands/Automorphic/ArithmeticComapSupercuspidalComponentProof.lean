import Langlands.Automorphic.CuspidalArithmeticTransportStatement
import Langlands.Automorphic.CuspidalArithmeticSpectralTransportProof
import Langlands.Automorphic.Unramified.CyclicInductionSupercuspidalReduction
import Langlands.VirtualRepresentation.Supercuspidal.FieldTransport

/-!
# Arithmetic pullback of a supercuspidal local component

For a ring isomorphism `e : K ≃+* L` of number fields, the pulled-back
presentation `CuspidalSpectralPresentation.arithmeticComap` has, at a finite
place `v` of `K`, the local factor of the original presentation at
`finitePlaceEquiv e.symm v`, pulled back along the entrywise isomorphism of
general linear groups over the completions. Comparing both local components
with their local factors and using the entrywise field transport of
supercuspidality gives `ArithmeticComapSupercuspidalComponentStatement`.
-/

noncomputable section

universe uK uL uV

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.AdelicGLTransport

local instance arithmeticSupercuspidalRationalGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance arithmeticSupercuspidalContinuousGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance arithmeticSupercuspidalSmoothGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance arithmeticSupercuspidalFormsGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance arithmeticSupercuspidalSpaceGroup {F : Type*} [Field F] [NumberField F]
    {n : ℕ} {v : FinitePlace F} (S : LocalRealization F n v) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]

namespace CuspidalSpectralPresentation

variable [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
variable {r : ℕ} {S : CuspidalOperatorRealization L r}

/-- The local component of the pulled-back presentation at a finite place `v`
of `K` is supercuspidal exactly when the local component of the original
presentation at the corresponding place `finitePlaceEquiv e.symm v` of `L` is. -/
theorem arithmeticComap_localComponent_isSupercuspidal_iff
    (P : CuspidalSpectralPresentation.{uL, uV} S) (e : K ≃+* L) (v : FinitePlace K) :
    ((P.arithmeticComap e).localComponent v).IsSupercuspidal ↔
      (P.localComponent (finitePlaceEquiv e.symm v)).IsSupercuspidal := by
  let σ := (finiteCompletionEquiv e.symm v).symm
  have hσ : Continuous σ := continuous_finiteCompletionEquiv_symm e.symm v
  have hσs : Continuous σ.symm := continuous_finiteCompletionEquiv e.symm v
  -- The original local component and its local factor.
  have α : (P.localFactor (finitePlaceEquiv e.symm v)).representation.Equiv
      (P.localComponent (finitePlaceEquiv e.symm v)).representation :=
    P.presentation.localComponentEquiv P.finiteSlice.nonzero (finitePlaceEquiv e.symm v)
  -- The pulled-back local component at `v` and its local factor.
  have β : ((P.arithmeticComap e).localFactor v).representation.Equiv
      ((P.arithmeticComap e).localComponent v).representation :=
    (P.arithmeticComap e).presentation.localComponentEquiv
      (P.arithmeticComap e).finiteSlice.nonzero v
  -- The pulled-back local factor is the entrywise field pullback.
  have hfac : ((P.arithmeticComap e).localFactor v).representation =
      (P.localFactor (finitePlaceEquiv e.symm v)).representation.comp
        (GeneralLinear.fieldEquiv (r + 1) σ hσ hσs).toMonoidHom := rfl
  have hirr :
      Representation.IsIrreducible ((P.arithmeticComap e).localFactor v).representation ↔
        Representation.IsIrreducible (P.localFactor (finitePlaceEquiv e.symm v)).representation :=
    isIrreducible_comp_continuousMulEquiv_iff _ (localEquiv (r + 1) e.symm v).symm
  have hsc :
      GeneralLinear.IsSupercuspidal ((P.arithmeticComap e).localFactor v).representation ↔
        GeneralLinear.IsSupercuspidal
          (P.localFactor (finitePlaceEquiv e.symm v)).representation := by
    rw [hfac]
    exact GeneralLinear.isSupercuspidal_comp_fieldEquiv_iff (r + 1) σ hσ hσs _
  rw [LocalRealization.isSupercuspidal_iff_representation,
    LocalRealization.isSupercuspidal_iff_representation]
  constructor
  · rintro ⟨hI, hS⟩
    have hI' := hirr.mp ((Langlands.isIrreducible_iff_of_equiv β).mpr hI)
    have hS' := hsc.mp (GeneralLinear.isSupercuspidal_of_equiv β.symm hS)
    exact ⟨(Langlands.isIrreducible_iff_of_equiv α).mp hI',
      GeneralLinear.isSupercuspidal_of_equiv α hS'⟩
  · rintro ⟨hI, hS⟩
    have hI' := hirr.mpr ((Langlands.isIrreducible_iff_of_equiv α).mpr hI)
    have hS' := hsc.mpr (GeneralLinear.isSupercuspidal_of_equiv α.symm hS)
    exact ⟨(Langlands.isIrreducible_iff_of_equiv β).mp hI',
      GeneralLinear.isSupercuspidal_of_equiv β hS'⟩

/-- At the place `finitePlaceEquiv e w` of `K`, the pulled-back presentation has
a supercuspidal local component whenever the original presentation has one at
the place `w` of `L`. -/
theorem arithmeticComap_localComponent_isSupercuspidal
    (P : CuspidalSpectralPresentation.{uL, uV} S) (e : K ≃+* L) (w : FinitePlace L)
    (hP : (P.localComponent w).IsSupercuspidal) :
    ((P.arithmeticComap e).localComponent (finitePlaceEquiv e w)).IsSupercuspidal := by
  rw [arithmeticComap_localComponent_isSupercuspidal_iff, arithmeticPlace_inverse,
    Equiv.symm_apply_apply]
  exact hP

end CuspidalSpectralPresentation

/-- Arithmetic pullback along a ring isomorphism `e : K ≃+* L` carries a
supercuspidal component at a finite place `w` of `L` to a supercuspidal
component at `finitePlaceEquiv e w`, with the same carrier universe. -/
theorem arithmeticComapSupercuspidalComponent :
    ArithmeticComapSupercuspidalComponentStatement.{uK, uL, uV} := by
  intro K L _ _ _ _ _ _ e r c w hc
  obtain ⟨S, P, rfl, hP⟩ := hc
  exact ⟨S.arithmeticComap e, P.arithmeticComap e, rfl,
    P.arithmeticComap_localComponent_isSupercuspidal e w hP⟩

end Langlands.Automorphic

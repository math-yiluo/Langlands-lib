import Langlands.Automorphic.ComplexPlaceParameterArithmeticTransport
import Langlands.Automorphic.WeakAutomorphicInductionArithmeticTransport
import Langlands.Global.Arithmetic.HarrisProposition48MackeyTransportStatement

/-! # Transport of a Mackey child and its induced complex-place parameters -/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField NumberField.InfinitePlace Langlands.Automorphic Langlands.Automorphic.Unramified
open Langlands.LocalFactor.Archimedean AdelicFunctoriality
open Langlands.Automorphic.ComplexPlaceArithmeticTransport
open Langlands.Global.ArchimedeanCompactTransport (complexPlace)

/-- **Transport of the actual Mackey child.** The pullback to `D` of a cuspidal realization
over a child's field `R.E` is a Mackey constituent when the realization weakly induces the
child's character, and it has, at every complex place of `D`, the complex-place parameter of
the representation induced from the Mackey character when the realization has the induced
complex-place parameters of the child. -/
theorem proposition48MackeyChildTransport :
    Proposition48MackeyChildTransportStatement.{uF, uV} := by
  intro Q D a R e e' hcomp hξ
  let : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
  let : Algebra D (Q.mackeyField D a) :=
    (IntermediateField.inclusion (show D ≤ Q.mackeyField D a from le_sup_left)).toAlgebra
  intro r S
  have he : ∀ x : R.E, e' (algebraMap R.E R.E' x) = algebraMap D (Q.mackeyField D a) (e x) :=
    fun x => Subtype.ext (hcomp x)
  have hsymm : ∀ x : D, e'.symm (algebraMap D (Q.mackeyField D a) x) =
      algebraMap R.E R.E' (e.symm x) := by
    intro x
    apply e'.injective
    rw [e'.apply_symm_apply, he, e.apply_symm_apply]
  have hχ : HeckeCharacter.comap e'.symm R.ξ = Q.mackeyCharacter D a := by
    rw [hξ]
    exact HeckeCharacter.comap_symm_comap e' _
  refine ⟨fun hS => ?_, fun hS => ?_⟩
  · have h := hS.arithmeticComap e.symm e'.symm hsymm
    rw [hχ] at h
    exact h
  · intro u
    obtain ⟨v, rfl⟩ : ∃ v, complexPlace e.symm v = u := by
      refine ⟨complexPlace e u, Subtype.ext ?_⟩
      ext x
      change u.1 (e (e.symm x)) = u.1 x
      rw [e.apply_symm_apply]
    obtain ⟨ds, hds, d, en, dξ, hdξ, hperm⟩ := hS v
    let β := placesAboveEquiv e e' he v
    refine ⟨parameterList e.symm v ds,
      cuspidal_hasComplexPlaceParameter_arithmeticComap e.symm S hds, d, en.trans β,
      fun w => parameter e'.symm (complexPlaceAbove v (β.symm w)) (dξ (β.symm w)), ?_, ?_⟩
    · intro w
      have h := hasComplexPlaceParameter_comap e'.symm (hdξ (β.symm w))
      rw [hχ] at h
      have h0 : (β (β.symm w)).1 = w.1 := congrArg Subtype.val (β.apply_symm_apply w)
      have hp : complexPlace e'.symm (complexPlaceAbove v (β.symm w)) =
          complexPlaceAbove (complexPlace e.symm v) w :=
        Subtype.ext h0
      rw [hp] at h
      exact h
    · rw [← parameterList_complexPlaceLanglandsSum e e' he v en dξ]
      exact perm_parameterList hperm

end Langlands.Global.Harris

import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerParameterAuxiliaryStatement
import Langlands.Automorphic.ComplexPlaceParameterHeckeTwist
import Langlands.Automorphic.Unramified.ComplexPlaceParameterNorm

/-!
# Untwisting complex-place parameters in Proposition 4.8

Proof of `Proposition48ExactStabilizerParameterUntwistStatement`: if `T` is the determinant
multiple of `S` by `ν` and has the complex-place parameters induced from the corrected
character `ξ · (ν ∘ N)`, then `S` has those induced from `ξ`. At a complex place `v` the
parameter of `S` is that of `T` with every block multiplied by the parameter of `ν⁻¹` at `v`,
and at a place `w` above `v` the parameter of `ξ` is that of the corrected character times
the parameter of `ν⁻¹ ∘ N` at `w`.
-/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic Langlands.Automorphic.Unramified
open Langlands.Automorphic.ComplexPlaceHeckeTwist Langlands.LocalFactor.Archimedean
open Langlands.Global.AdelicFunctoriality

/-- The corrected character times `ν⁻¹ ∘ N` is the original character. -/
theorem Proposition48Problem.correctedCharacter_mul_inv_comp (Q : Proposition48Problem.{uF})
    (ν : HeckeCharacter Q.E) :
    Q.correctedCharacter ν * ν⁻¹.comp (ideleClassNorm (K := Q.E) (L := Q.E')) = Q.ξ := by
  refine ContinuousMonoidHom.ext fun x => ?_
  change (Q.ξ x * ν (ideleClassNorm (K := Q.E) (L := Q.E') x)) *
      (ν (ideleClassNorm (K := Q.E) (L := Q.E') x))⁻¹ = Q.ξ x
  rw [mul_assoc, mul_inv_cancel, mul_one]

/-- The parameter-untwist input of the exact-stabilizer induction for Harris (1998),
Proposition 4.8: untwisting a parity-normalized solution keeps the induced complex-place
parameters. -/
theorem proposition48ExactStabilizerParameterUntwist :
    Proposition48ExactStabilizerParameterUntwistStatement.{uF, uV} := by
  intro Q b ν χs _ _ r S T hU hT v
  change ∀ v : {v : NumberField.InfinitePlace Q.E // v.IsComplex}, ∃ ds : List ComplexCharacterData,
    T.isoClass.HasComplexPlaceParameter v ds ∧ ∃ (d : ℕ) (e : Fin d ≃ InfinitePlacesAbove Q.E' v.1)
      (dξ : InfinitePlacesAbove Q.E' v.1 → ComplexCharacterData),
      (∀ w, (Q.correctedCharacter ν).HasComplexPlaceParameter (complexPlaceAbove v w) (dξ w)) ∧
        ds.Perm (complexPlaceLanglandsSum v e fun w => [dξ w]) at hT
  obtain ⟨ds, hds, d, en, dξ, hdξ, hperm⟩ := hT v
  obtain ⟨e, he⟩ := exists_hasComplexPlaceParameter ν⁻¹ v
  have hDM := hU.2.2.2.2.2.2.2
  refine ⟨ds.map fun c => c.mul e,
    (CuspidalOperatorRealization.isoClass_hasComplexPlaceParameter S v _).mpr
      (OperatorRealization.IsDeterminantMultiple.hasComplexPlaceParameter hDM hds he),
    d, en, fun w => (dξ w).mul (normParameter v w e), fun w => ?_, ?_⟩
  · have h := HasComplexPlaceParameter.mul (hdξ w)
      (hasComplexPlaceParameter_comp_ideleClassNorm (L := Q.E') he w)
    rw [Q.correctedCharacter_mul_inv_comp ν] at h
    exact h
  · have h2 := complexPlaceLanglandsSum_map_mul v en dξ e
    exact (hperm.map (fun c => c.mul e)).trans (List.Perm.of_eq h2)

end Langlands.Global.Harris

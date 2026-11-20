import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerParameterAuxiliaryStatement
import Langlands.Automorphic.RankOneHeckeRestriction

/-!
# The rank-one start of Proposition 4.8 with complex-place parameters

Proof of `Proposition48ExactStabilizerAuxiliaryRankOneStatement`: when `[E' : E] = 1`, the
`GL(1)` realization of the restriction `ξ ∘ ι` of `ξ` along the idele-class inclusion
`ι : C_E → C_{E'}` is a solution with the complex-place parameters induced from `ξ`.
-/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic Langlands.Automorphic.Unramified
open Langlands.Automorphic.RankOneHecke Langlands.LocalFactor.Archimedean
open Langlands.Global.AdelicFunctoriality

/-- The rank-one start of the exact-stabilizer induction for Harris (1998), Proposition 4.8,
with complex-place parameters: in degree one the automorphic `GL(1)` realization of the
restriction of `ξ` is a solution with the parameters induced from `ξ`. -/
theorem proposition48ExactStabilizerAuxiliaryRankOne :
    Proposition48ExactStabilizerAuxiliaryRankOneStatement.{uF, uV} := by
  intro Q hQ h1
  obtain ⟨-, -, -, -, -, -, -, -, -, hAlg, -, hCI, -⟩ := hQ
  rw [h1, Nat.sub_self] at hAlg
  obtain ⟨t, ht⟩ := hAlg
  have ht' : ∀ x, (Q.ξ.atInfinity x : ℂ) = (InfinityType.toCharacter t x : ℂ) := fun x => by
    have hx := ht x
    simpa only [pow_zero, Finset.prod_const_one, mul_one] using hx
  let χ : HeckeCharacter Q.E := restriction (K := Q.E) Q.ξ
  let dξ : ∀ v : {v : NumberField.InfinitePlace Q.E // v.IsComplex},
      InfinitePlacesAbove Q.E' v.1 → ComplexCharacterData := fun _ w =>
    exponentData (t w.1.embedding) (t (ComplexEmbedding.conjugate w.1.embedding))
  have hpar : ∀ (v : {v : NumberField.InfinitePlace Q.E // v.IsComplex})
      (w : InfinitePlacesAbove Q.E' v.1),
      Q.ξ.HasComplexPlaceParameter (complexPlaceAbove v w) (dξ v w) :=
    fun v w => hasComplexPlaceParameter_of_atInfinity t ht' (complexPlaceAbove v w)
  have hcard : ∀ v : {v : NumberField.InfinitePlace Q.E // v.IsComplex},
      Fintype.card (InfinitePlacesAbove Q.E' v.1) = 1 :=
    fun v => card_infinitePlacesAbove h1 v.1 v.2
  have hexp : ∀ v : {v : NumberField.InfinitePlace Q.E // v.IsComplex},
      ∃ a b : ℤ, χ.HasComplexPlaceParameter v (exponentData a b) := by
    intro v
    obtain ⟨w⟩ : Nonempty (InfinitePlacesAbove Q.E' v.1) :=
      Fintype.card_pos_iff.mp (by rw [hcard v]; exact Nat.one_pos)
    have h := restriction_hasComplexPlaceParameter h1 v w (hpar v w)
    unfold normParameter at h
    split_ifs at h
    · exact ⟨_, _, h⟩
    · rw [exponentData_conj] at h
      exact ⟨_, _, h⟩
  choose a b hab using hexp
  refine ⟨0, (cuspidal χ).isoClass, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact cuspidal_restriction_isWeakAutomorphicInductionOf.{0, uV} h1 Q.ξ
  · exact cuspidal_isRegularAlgebraic_of_exponentData a b hab
  · exact cuspidal_isConjugateSelfDual χ (restriction_ideleClassComplexConj hCI)
  · exact cuspidal_hasSupercuspidalComponent.{0, uV} χ Q.Ps.v
  · intro v
    let e : Fin 1 ≃ InfinitePlacesAbove Q.E' v.1 := (Fintype.equivFinOfCardEq (hcard v)).symm
    exact ⟨[normParameter v (e 0) (dξ v (e 0))],
      cuspidal_hasComplexPlaceParameter
        (restriction_hasComplexPlaceParameter h1 v (e 0) (hpar v (e 0))),
      1, e, dξ v, hpar v, List.Perm.of_eq (complexPlaceLanglandsSum_fin_one v e (dξ v)).symm⟩

end Langlands.Global.Harris

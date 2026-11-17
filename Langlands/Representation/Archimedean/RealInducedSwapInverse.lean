import Langlands.Representation.Archimedean.RealInducedSwapShifted
import Langlands.Representation.Archimedean.RealBlockMultiplierOperators

/-!
# Explicit inverses for shifted four-crossing maps

The reverse four-crossing word is the inverse word after interchanging the
disjoint middle factors. All endpoint exponents remain fixed.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
namespace RealInducedSwapInverse

open Langlands.LocalFactor.Archimedean
open RealBlockMultiplier RealBlockFrobeniusMap RealCharacterPair
open RealCharacterPairReducible RealInducedSwapGeneric RealInducedSwapShifted
open RealCharacterInducedSwap RealCharacterInducedPushforward RealStandardFiltration

variable {d e : ComplexCharacterData} {ζ η : ℂ}

/-- The four-crossing map before imposing the two induction windows. -/
def fullMap (h : FourCrossings d e ζ) :
    KF 4 (expanded d e) →ₗ[ℂ] KF 4 (expanded e d) :=
  blockFrobMap (dataAD d e h) ∘ₗ blockFrobMap (dataBD d e h) ∘ₗ
    blockFrobMap (dataAC d e h) ∘ₗ blockFrobMap (dataBC d e h)

/-- The reverse sequences multiply the corresponding forward sequences to one
on their actual parity classes. -/
def AreInverse (h : FourCrossings d e ζ) (k : FourCrossings e d η) : Prop :=
  (∀ j : ℤ, Even (j - pairParity (chA e) (chB d)) → k.ad.μ j * h.bc.μ j = 1) ∧
  (∀ j : ℤ, Even (j - pairParity (chA e) (chA d)) → k.ac.μ j * h.ac.μ j = 1) ∧
  (∀ j : ℤ, Even (j - pairParity (chB e) (chB d)) → k.bd.μ j * h.bd.μ j = 1) ∧
  (∀ j : ℤ, Even (j - pairParity (chB e) (chA d)) → k.bc.μ j * h.ad.μ j = 1)

theorem AreInverse.symm {h : FourCrossings d e ζ} {k : FourCrossings e d η}
    (hprod : AreInverse h k) : AreInverse k h := by
  rcases hprod with ⟨hbc, hac, hbd, had⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [mul_comm]
    exact had j (by simpa only [pairParity_comm (chA d) (chB e)] using hj)
  · intro j hj
    rw [mul_comm]
    exact hac j (by simpa only [pairParity_comm (chA d) (chA e)] using hj)
  · intro j hj
    rw [mul_comm]
    exact hbd j (by simpa only [pairParity_comm (chB d) (chB e)] using hj)
  · intro j hj
    rw [mul_comm]
    exact hbc j (by simpa only [pairParity_comm (chB d) (chA e)] using hj)

/-- The disjoint middle square converts the reverse word into the inverse word. -/
theorem fullMap_leftInverse (h : FourCrossings d e ζ) (k : FourCrossings e d η)
    (hprod : AreInverse h k) :
    Function.LeftInverse (fullMap k) (fullMap h) := by
  rcases hprod with ⟨hbc, hac, hbd, had⟩
  have hAD : Function.LeftInverse
      (blockFrobMap (dataBC e d k)) (blockFrobMap (dataAD d e h)) := by
    have kr := dataBC e d k
    rw [pairParity_comm (chA d) (chB e)] at kr
    exact blockFrobMap_leftInverse (dataAD d e h) kr had
  have hAC : Function.LeftInverse
      (blockFrobMap (dataAC e d k)) (blockFrobMap (dataAC' d e h)) := by
    have kr := dataAC e d k
    rw [pairParity_comm (chA d) (chA e)] at kr
    exact blockFrobMap_leftInverse (dataAC' d e h) kr hac
  have hBD : Function.LeftInverse
      (blockFrobMap (dataBD e d k)) (blockFrobMap (dataBD' d e h)) := by
    have kr := dataBD e d k
    rw [pairParity_comm (chB d) (chB e)] at kr
    exact blockFrobMap_leftInverse (dataBD' d e h) kr hbd
  have hBC : Function.LeftInverse
      (blockFrobMap (dataAD e d k)) (blockFrobMap (dataBC d e h)) := by
    have kr := dataAD e d k
    rw [pairParity_comm (chB d) (chA e)] at kr
    exact blockFrobMap_leftInverse (dataBC d e h) kr hbc
  intro f
  change blockFrobMap (dataAD e d k)
    (blockFrobMap (dataBD e d k)
      (blockFrobMap (dataAC e d k)
        (blockFrobMap (dataBC e d k)
          (blockFrobMap (dataAD d e h)
            (blockFrobMap (dataBD d e h)
              (blockFrobMap (dataAC d e h)
                (blockFrobMap (dataBC d e h) f))))))) = f
  rw [hAD, RealInducedSwapShifted.middle_square d e h, hAC, hBD, hBC]

/-- The same inverse identity holds after corestriction to the two-block spaces. -/
theorem shiftedMap_leftInverse (h : FourCrossings d e ζ) (k : FourCrossings e d η)
    (hprod : AreInverse h k) :
    Function.LeftInverse (shiftedMap e d k) (shiftedMap d e h) := by
  intro f
  apply Subtype.ext
  exact congrArg
    (fun v : KF 4 (expanded d e) => (v : Langlands.GeneralLinear 4 ℝ → ℂ))
    (fullMap_leftInverse h k hprod (Submodule.inclusion (source_le_expanded d e) f))

/-- Opposite four-crossing maps give an explicit equivalence of the actual spaces. -/
def shiftedEquiv (h : FourCrossings d e ζ) (k : FourCrossings e d η)
    (hprod : AreInverse h k) :
    KF 4 (source d e) ≃ₗ[ℂ] KF 4 (target d e) :=
  { shiftedMap d e h with
    invFun := shiftedMap e d k
    left_inv := shiftedMap_leftInverse h k hprod
    right_inv := shiftedMap_leftInverse k h hprod.symm }

/-- All four constituent parameters shifted by the same scalar are generic. -/
def IsGenericShift (d e : ComplexCharacterData) (ζ : ℂ) : Prop :=
  IsGenericParameter ((chB d).exponent - (chA e).exponent + ζ)
    (pairParity (chA e) (chB d)) ∧
  IsGenericParameter ((chA d).exponent - (chA e).exponent + ζ)
    (pairParity (chA e) (chA d)) ∧
  IsGenericParameter ((chB d).exponent - (chB e).exponent + ζ)
    (pairParity (chB e) (chB d)) ∧
  IsGenericParameter ((chA d).exponent - (chB e).exponent + ζ)
    (pairParity (chB e) (chA d))

theorem reverse_parameter (x y : RealCharacterData) (ζ : ℂ) :
    y.exponent - x.exponent + -ζ = -(x.exponent - y.exponent + ζ) := by ring

theorem reverse_generic {x y : RealCharacterData}
    (hg : IsGenericParameter (x.exponent - y.exponent + ζ) (pairParity y x)) :
    IsGenericParameter (y.exponent - x.exponent + -ζ) (pairParity x y) := by
  rw [reverse_parameter, pairParity_comm x y]
  exact hg.neg

theorem IsGenericShift.reverse (hg : IsGenericShift d e ζ) :
    IsGenericShift e d (-ζ) :=
  ⟨reverse_generic hg.2.2.2, reverse_generic hg.2.1,
    reverse_generic hg.2.2.1, reverse_generic hg.1⟩

/-- A generic shifted multiplier supplies the required recurrence and symmetry. -/
def genericCrossing (x y : RealCharacterData) (ζ : ℂ)
    (hg : IsGenericParameter (x.exponent - y.exponent + ζ) (pairParity y x)) :
    Crossing x y ζ where
  μ := genericMultiplier (x.exponent - y.exponent + ζ) (pairParity y x)
  symm := isSymmetric_genericMultiplier _ (pairParity_eq y x)
  recurrent := by
    convert isRecurrent_genericMultiplier_of_ne (pairParity_eq y x) hg.2 using 1
    ring

/-- The explicit generic parameter family at the fixed endpoint exponents. -/
def genericFourCrossings (hg : IsGenericShift d e ζ) : FourCrossings d e ζ where
  bc := genericCrossing (chB d) (chA e) ζ hg.1
  ac := genericCrossing (chA d) (chA e) ζ hg.2.1
  bd := genericCrossing (chB d) (chB e) ζ hg.2.2.1
  ad := genericCrossing (chA d) (chB e) ζ hg.2.2.2

theorem generic_reverse_product {x y : RealCharacterData}
    (hg : IsGenericParameter (x.exponent - y.exponent + ζ) (pairParity y x))
    (j : ℤ) :
    genericMultiplier (y.exponent - x.exponent + -ζ) (pairParity x y) j *
      genericMultiplier (x.exponent - y.exponent + ζ) (pairParity y x) j = 1 := by
  rw [reverse_parameter, pairParity_comm x y, mul_comm, genericMultiplier_mul_neg hg]

theorem genericFourCrossings_areInverse (hg : IsGenericShift d e ζ) :
    AreInverse (genericFourCrossings hg) (genericFourCrossings hg.reverse) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j _
    exact generic_reverse_product hg.1 j
  · intro j _
    exact generic_reverse_product hg.2.1 j
  · intro j _
    exact generic_reverse_product hg.2.2.1 j
  · intro j _
    exact generic_reverse_product hg.2.2.2 j

/-- A generic four-crossing equivalence with the opposite-shift family as inverse. -/
def genericShiftEquiv (hg : IsGenericShift d e ζ) :
    KF 4 (source d e) ≃ₗ[ℂ] KF 4 (target d e) :=
  shiftedEquiv (genericFourCrossings hg) (genericFourCrossings hg.reverse)
    (genericFourCrossings_areInverse hg)

end RealInducedSwapInverse
end Langlands.Archimedean

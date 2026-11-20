import Langlands.Automorphic.Unramified.WeakInduction
import Langlands.Galois.AlgebraicHeckeLambdaAdicRealizationStatement
import Langlands.Galois.ClosureRestriction
import Langlands.Weil.Representation.Induction
import Langlands.Weil.Representation.Twist

/-! # Induction of actual rank-one Galois realizations -/

noncomputable section

universe uK uE uL uV

set_option autoImplicit false

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic.Unramified.WeakInduction Polynomial

variable {K : Type uK} {E : Type uE} {L : Type uL}
variable [Field K] [Field E] [Field L] [NumberField L] [Algebra K E]

/-- An actual continuous `λ`-adic object is induced from `ψ` if its action is
linearly equivalent to the finite-index induction from the rank-one action
of `ψ` on the image of the specified absolute Galois restriction map. -/
def IsGaloisInductionOfCharacter (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    (lam : FinitePlace L) (ψ : LambdaAdicCharacter E L lam)
    (R : LambdaAdic.{uK, uL, uV} K L lam) : Prop :=
  let j := (restrictionAlongClosure e).toMonoidHom
  ∃ hIndex : j.range.FiniteIndex,
    letI : j.range.FiniteIndex := hIndex
    ∃ φ : j.range →* (FiniteCompletion L lam)ˣ,
      φ.comp j.rangeRestrict = ψ.toMonoidHom ∧
      Nonempty (FiniteRepresentation.Equiv
        (FiniteRepresentation.induce j.range
          (FiniteRepresentation.twist φ
            (FiniteRepresentation.of
              (1 : Representation (FiniteCompletion L lam) j.range (FiniteCompletion L lam)))))
        R.val)

variable [NumberField K] [NumberField E]

/-- The supplied complex polynomials agree almost everywhere with the
unramified Euler denominators induced from the Hecke character. -/
def MatchesHeckeInductionEulerPolynomials (χ : HeckeCharacter E)
    (P : FinitePlace K → ℂ[X]) : Prop :=
  ∀ᶠ v : FinitePlace K in Filter.cofinite,
    IsUnramifiedAbove χ v ∧
      ∀ ϖ : ∀ w : FinitePlacesAbove E v, (FiniteCompletion E w.1)ˣ,
        IsUniformizerFamily v ϖ → P v = inducedEulerPolynomial χ v ϖ

/-- Inducing a compatible rank-one family gives a compatible family with the
actual induced unramified Euler denominators. -/
def HeckeCharacterGaloisInductionStatement : Prop :=
  ∀ (K : Type uK) (E : Type uE) (L : Type uL) [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L] [Algebra K E]
    (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure E) (ι : L →+* ℂ)
    (χ : HeckeCharacter E) (ψ : (lam : FinitePlace L) → LambdaAdicCharacter E L lam),
    IsCompatibleLambdaAdicRealization ι χ ψ →
    ∃ (R : Collection.{uK, uL, max uK uL} K L ∅) (S : Finset (FinitePlace K))
      (P : FinitePlace K → L[X]),
        (∀ lam, IsGaloisInductionOfCharacter e lam.val (ψ lam.val) (R lam)) ∧
        HasRank ∅ R (Module.finrank K E) ∧ MatchesOutside ∅ R S P ∧
        MatchesHeckeInductionEulerPolynomials (K := K) χ (fun v => (P v).map ι)

end Langlands.GaloisRepresentation

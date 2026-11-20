import Langlands.Galois.HeckeCharacterGaloisInductionStatement
import Langlands.Galois.UnitaryNormalization
import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryData
import Langlands.Global.HeckeNormPower
import Langlands.Weil.Representation.CyclicExtensionTwistStatement

/-! # Singleton restriction of the monomial Galois family -/

noncomputable section

universe uF

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.GaloisRepresentation Langlands.FiniteRepresentation

/-- In the singleton case the Galois induction of the algebraic norm twist of
`ξ` restricts to the monomial representation of the actual Mackey inducing
field and norm character. Its raw polynomials over the step field have the
parent weight, and normalization recovers the original Hecke inductions. -/
def Proposition48SingletonMonomialRestrictionStatement : Prop :=
  AlgebraicHeckeLambdaAdicRealizationStatement.{0, 0} →
  HeckeCharacterGaloisInductionStatement.{0, 0, 0} →
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
    Q.IsAuxiliaryValid → Q.IsPrimeCyclicStep D → Nat.card (Q.MackeyIndex D) = 1 →
    let M := Q.mackeyField D 1
    let j : Q.E' →+* M :=
      (IntermediateField.inclusion (show Q.conjugateField 1 ≤ M from le_sup_right)).toRingHom.comp
        (Q.conjugateEmbedding 1).equivFieldRange.toRingEquiv.toRingHom
    letI : Algebra Q.E' M := j.toAlgebra
    letI : Algebra D M :=
      (IntermediateField.inclusion (show D ≤ M from le_sup_left)).toAlgebra
    let e : AlgebraicClosure Q.E →ₐ[Q.E] AlgebraicClosure Q.E' := IsAlgClosed.lift
    let eD : AlgebraicClosure Q.E →ₐ[Q.E] AlgebraicClosure D := IsAlgClosed.lift
    let eM : AlgebraicClosure D →ₐ[D] AlgebraicClosure M := IsAlgClosed.lift
    let ej : AlgebraicClosure Q.E' →ₐ[Q.E'] AlgebraicClosure M := IsAlgClosed.lift
    let b := Module.finrank Q.E Q.E' - 1
    let ξalg := Q.ξ * HeckeCharacter.normPower Q.E' ((b : ℂ) / 2)
    ∃ (L : Type) (fieldL : Field L),
      letI : Field L := fieldL
      ∃ (numberFieldL : NumberField L),
        letI : NumberField L := numberFieldL
        ∃ (ι : L →+* ℂ) (ψ : (lam : FinitePlace L) → LambdaAdicCharacter Q.E' L lam)
          (R : Collection.{0, 0, 0} Q.E L ∅) (S : Finset (FinitePlace Q.E))
          (P : FinitePlace Q.E → Polynomial L) (SD : Finset (FinitePlace D))
          (PD : FinitePlace D → Polynomial L),
          let RD : Collection.{0, 0, 0} D L ∅ := fun lam => pullbackAlongClosure eD (R lam)
          IsCompatibleLambdaAdicRealization ι ξalg ψ ∧
          (∀ lam, IsGaloisInductionOfCharacter e lam.val (ψ lam.val) (R lam)) ∧
          HasRank ∅ R (Module.finrank Q.E Q.E') ∧ MatchesOutside ∅ R S P ∧
          MatchesHeckeInductionEulerPolynomials (K := Q.E) Q.ξ
            (fun v => unitaryEulerPolynomial ((P v).map ι)) ∧
          (∀ lam, IsGaloisInductionOfCharacter eM lam.val
              ((ψ lam.val).comp (restrictionAlongClosure ej)) (RD lam) ∧
            (RD lam).val.representation.IsIrreducible ∧ HasScalarEndomorphisms (RD lam).val) ∧
          MatchesOutside ∅ RD SD PD ∧
          MatchesHeckeInductionEulerPolynomials (K := D) (Q.mackeyCharacter D 1)
            (fun w => unitaryEulerPolynomial ((PD w).map ι)) ∧
          ∀ᶠ w : FinitePlace D in Filter.cofinite,
            (PD w).coeff 0 = 1 ∧
            Cohomology.Weights.HasComplexRootsOfWeight (residueCardinality w) (-(b : ℤ))
              ((PD w).reverse.map ι)

end Langlands.Global.Harris

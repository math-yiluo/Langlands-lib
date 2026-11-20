import Langlands.Galois.CompatibleFamily
import Langlands.Galois.QuadraticPatchingStatement
import Langlands.Global.AdelicFunctoriality.Norm

/-! # Quadratic patching from common geometric Frobenius polynomials -/

noncomputable section

universe uF uC uV

namespace Langlands.GaloisRepresentation

open Polynomial Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Global.AdelicFunctoriality.FiniteExtension
open scoped NumberField

/-- Raise each root of a split monic polynomial to the given power, preserving
multiplicity, and form the resulting monic polynomial. -/
def frobeniusRootPower {C : Type uC} [Field C] (f : ℕ) (P : C[X]) : C[X] :=
  (P.roots.map (fun x => X - Polynomial.C (x ^ f))).prod

/-- A common geometric Frobenius polynomial formula on the auxiliary fields
supplies invariance and agreement on composita for quadratic patching. The
patched representation recovers the prescribed polynomial at a split place
where an auxiliary representation has it. -/
def QuadraticFrobeniusPatchingStatement : Prop :=
  QuadraticPatchingStatement.{uF, uC, uV} →
  ∀ (F : Type uF) [Field F] [NumberField F]
    (C : Type uC) [Field C] [CharZero C] [IsAlgClosed C]
    [TopologicalSpace C] [IsTopologicalRing C] [T2Space C]
    (n : ℕ) (S : Finset (FinitePlace F))
    (I : Set (FiniteGaloisIntermediateField F (AlgebraicClosure F)))
    (R : (N : I) → Objects.{uF, uC, uV} N.val C) (P : FinitePlace F → C[X]),
    (∀ N : I, Module.finrank F N.val = 2) →
    (∀ (v : FinitePlace F), v ∉ S →
      ∀ M : FiniteGaloisIntermediateField F (AlgebraicClosure F),
        ∃ N : I, N.val ⊓ M = ⊥ ∧
          letI : NumberField N.val := NumberField.of_module_finite F N.val
          SplitsCompletelyAt (N := N.val) v) →
    (∀ N : I, (R N).val.rank = n ∧
      Representation.IsSemisimpleRepresentation (R N).val.representation) →
    (∀ v, (P v).Monic ∧ (P v).natDegree = n) →
    (∀ N : I,
      letI : NumberField N.val := NumberField.of_module_finite F N.val
      ∀ᶠ v : FinitePlace F in Filter.cofinite, ∀ w : FinitePlacesAbove N.val v,
        HasEulerPolynomialAt (R N) w.val
          (frobeniusRootPower (w.val.asIdeal.inertiaDeg (𝓞 F)) (P v)).reverse) →
    ∃ A : Objects.{uF, uC, uV} F C,
      A.val.rank = n ∧ Representation.IsSemisimpleRepresentation A.val.representation ∧
      (∀ N : I, Nonempty (FiniteRepresentation.Equiv
        (pullback (algebraMap F N.val) A).val (R N).val)) ∧
      ∀ N : I,
        letI : NumberField N.val := NumberField.of_module_finite F N.val
        ∀ (v : FinitePlace F) (w : FinitePlacesAbove N.val v),
          SplitsCompletelyAt (N := N.val) v →
          HasEulerPolynomialAt (R N) w.val (P v).reverse →
          HasEulerPolynomialAt A v (P v).reverse

end Langlands.GaloisRepresentation

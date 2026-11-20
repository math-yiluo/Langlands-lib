import Langlands.Galois.CoefficientRepresentation
import Langlands.Global.AdelicFunctoriality.Extension
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RepresentationTheory.Semisimple

/-! # Patching semisimple Galois representations from quadratic extensions -/

noncomputable section

universe uF uC uV

namespace Langlands.Global.AdelicFunctoriality.FiniteExtension

open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

/-- Complete splitting at a finite place expressed using the degree of each actual
extension of completions. -/
def SplitsCompletelyAt {F N : Type*} [Field F] [NumberField F] [Field N]
    [NumberField N] [Algebra F N] (v : Global.FinitePlace F) : Prop :=
  ∀ (w : Global.FinitePlace N), ∀ (_ : w.asIdeal.LiesOver v.asIdeal),
    Module.finrank (Global.FiniteCompletion F v) (Global.FiniteCompletion N w) = 1

end Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.Global.AdelicFunctoriality.FiniteExtension

/-- Sørensen's patching lemma in degree two. The auxiliary fields and their composita
are taken in one algebraic closure. The representations agree up to linear
intertwining after restriction, and the patched semisimple representation is unique
up to linear intertwining. -/
def QuadraticPatchingStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F]
    (C : Type uC) [Field C] [CharZero C] [IsAlgClosed C]
    [TopologicalSpace C] [IsTopologicalRing C] [T2Space C]
    (n : ℕ) (S : Finset (FinitePlace F))
    (I : Set (FiniteGaloisIntermediateField F (AlgebraicClosure F)))
    (R : (N : I) → Objects.{uF, uC, uV} N.val C),
    (∀ N : I, Module.finrank F N.val = 2) →
    (∀ (v : FinitePlace F), v ∉ S →
      ∀ M : FiniteGaloisIntermediateField F (AlgebraicClosure F),
        ∃ N : I, N.val ⊓ M = ⊥ ∧
          letI : NumberField N.val := NumberField.of_module_finite F N.val
          SplitsCompletelyAt (N := N.val) v) →
    (∀ N : I, (R N).val.rank = n ∧
      Representation.IsSemisimpleRepresentation (R N).val.representation) →
    (∀ (N : I) (σ : N.val ≃ₐ[F] N.val),
      Nonempty (FiniteRepresentation.Equiv
        (pullback σ.toRingEquiv.toRingHom (R N)).val (R N).val)) →
    (∀ N M : I,
      Nonempty (FiniteRepresentation.Equiv
        (pullback (IntermediateField.inclusion
          (le_sup_left (a := N.val.toIntermediateField) (b := M.val.toIntermediateField))).toRingHom
          (R N)).val
        (pullback (IntermediateField.inclusion
          (le_sup_right (a := N.val.toIntermediateField) (b := M.val.toIntermediateField))).toRingHom
          (R M)).val)) →
    let IsPatch := fun A : Objects.{uF, uC, uV} F C =>
      A.val.rank = n ∧ Representation.IsSemisimpleRepresentation A.val.representation ∧
        ∀ N : I, Nonempty (FiniteRepresentation.Equiv
          (pullback (algebraMap F N.val) A).val (R N).val)
    ∃ A, IsPatch A ∧ ∀ B, IsPatch B → Nonempty (FiniteRepresentation.Equiv A.val B.val)

end Langlands.GaloisRepresentation

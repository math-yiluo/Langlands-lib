import Langlands.AlgebraicGeometry.Picard.Rosati
import Langlands.GroupScheme.SmoothConnectedZeroDimensional

/-! # Actual Rosati positivity in relative dimension zero -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

/-- Both actual integral and rational homomorphisms out of `A` vanish. -/
def HasTrivialOutgoingHom {S : Scheme.{u}} (A : AbelianScheme S) : Prop :=
  ∀ B : AbelianScheme S,
    (∀ f : A ⟶ B, f = 0) ∧ ∀ f : Hom0 A B, f = 0

variable {k : Type u} [Field k] {A B : AbelianScheme (Spec (.of k))}

/-- A zero-dimensional abelian scheme over a field has no nonzero integral
homomorphism to another abelian scheme. -/
theorem hom_eq_zero_of_relativeDimension_zero (hA : A.HasRelativeDimension 0)
    (f : A ⟶ B) : f = 0 := by
  have : ConnectedSpace A.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.X.hom
  have h := GroupScheme.eq_zero_of_smoothOfRelativeDimension_zero_over_field
    (groupHom f) hA
  exact congrArg Additive.ofMul h

/-- Rationalization preserves triviality of the actual outgoing Hom groups. -/
theorem hom0_eq_zero_of_relativeDimension_zero (hA : A.HasRelativeDimension 0)
    (f : Hom0 A B) : f = 0 := by
  induction f using TensorProduct.inductionOn with
  | tmul q g =>
      rw [hom_eq_zero_of_relativeDimension_zero hA g, TensorProduct.tmul_zero]
  | add f g hf hg => rw [hf, hg, add_zero]

/-- Every actual outgoing Hom group, before and after rationalization, is
trivial for an abelian scheme of relative dimension zero over any field. -/
theorem hasTrivialOutgoingHom_of_relativeDimension_zero
    (hA : A.HasRelativeDimension 0) : HasTrivialOutgoingHom A := by
  intro B
  exact ⟨hom_eq_zero_of_relativeDimension_zero hA,
    hom0_eq_zero_of_relativeDimension_zero hA⟩

/-- The actual rational endomorphism algebra is a subsingleton in dimension zero. -/
theorem subsingleton_end0_of_relativeDimension_zero (hA : A.HasRelativeDimension 0) :
    Subsingleton (End0 A) :=
  ⟨fun a b => (hom0_eq_zero_of_relativeDimension_zero hA a).trans
    (hom0_eq_zero_of_relativeDimension_zero hA b).symm⟩

namespace Rosati

/-- The exact local Rosati positivity conjunction holds in relative dimension
zero. Strict positivity is vacuous because every actual rational endomorphism
vanishes. -/
theorem positivity_of_relativeDimension_zero (P : Prerequisites.{u})
    (W : DualData A) (hadd : W.Additivity P) (lam : A ⟶ W.dual P)
    [hinv : HasRationalInverse P W lam] (hA : A.HasRelativeDimension 0) :
    (∀ a b : End0 A,
      @traceForm P k _ A W hadd lam hinv a b = @traceForm P k _ A W hadd lam hinv b a) ∧
      (∀ a : End0 A, 0 ≤ @traceForm P k _ A W hadd lam hinv a a) ∧
      ∀ a : End0 A, a ≠ 0 →
        0 < geometricEndomorphismTrace A (a * involution P W hadd lam a) := by
  let := subsingleton_end0_of_relativeDimension_zero hA
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    have h : a = b := Subsingleton.elim _ _
    subst b
    rfl
  · intro a
    rw [Subsingleton.elim a (0 : End0 A)]
    simp
  · intro a ha
    exact (ha (Subsingleton.elim a 0)).elim

end Rosati

end Langlands.AbelianScheme

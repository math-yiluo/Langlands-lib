import Langlands.AbelianScheme.KernelCharacterIndependence
import Langlands.AbelianScheme.IsogenySpecialization

/-! # Descent and Picard-zero prerequisites for field kernel duality -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Faithfully flat descent classifies actual trivial-pullback line bundles
by the existing normalized intrinsic character, on every test scheme. -/
def FieldTrivialPullbackCharacterBijectiveStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (A B : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (f : A ⟶ B), IsIsogeny f →
    ∀ (T : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))),
      Function.Bijective
        (trivialHomPullbackClassCharacter f (T := T) (universalGlobalFunctions A))

/-- A rigidified family with trivial isogeny pullback has translation-invariant
geometric fibres, for every parameter scheme over the field. -/
def FieldTrivialPullbackPicardZeroStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (A B : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (f : A ⟶ B), IsIsogeny f →
    ∀ (T : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
      (L : RigidifiedFamily B T),
      HasTrivialHomPullback f T ((RigidifiedLineBundle.forget _).obj L) →
        IsPicardZeroFamily B L

/-- The two separate geometric obligations used to compare the actual dual
kernel with all trivial-pullback bundle classes. -/
def FieldIsogenyKernelDescentStatements : Prop :=
  FieldTrivialPullbackCharacterBijectiveStatement.{u} ∧
    FieldTrivialPullbackPicardZeroStatement.{u}

end Langlands.AbelianScheme

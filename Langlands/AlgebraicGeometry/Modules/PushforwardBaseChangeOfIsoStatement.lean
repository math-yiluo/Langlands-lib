import Langlands.AlgebraicGeometry.Modules.PushforwardBaseChangeOf

/-!
# Invertibility of the base-change comparison of a map over spectra

Statement only: over a commutative square whose bases are spectra, if both direct images are
quasi-coherent and the scalar sections comparison of `a : P ⟶ g_* N` is invertible, then the
sheaf comparison `pushforwardBaseChangeOf f (Spec.map φ) f' g w a` is invertible.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- For a commutative square `g ≫ f = f' ≫ Spec.map φ` and `a : P ⟶ g_* N`, if `f_* P` and
`f'_* N` are quasi-coherent and `scalarSectionsBaseChangeMapOf φ f f' g w a` is an isomorphism,
then `pushforwardBaseChangeOf f (Spec.map φ) f' g w a` is an isomorphism. -/
def PushforwardBaseChangeOfIsoStatement : Prop :=
  ∀ (X X' : Scheme.{u}) (R T : CommRingCat.{u}) (φ : R ⟶ T) (f : X ⟶ Spec R)
    (f' : X' ⟶ Spec T) (g : X' ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)
    (P : X.Modules) (N : X'.Modules) (a : P ⟶ (Scheme.Modules.pushforward g).obj N),
    ((Scheme.Modules.pushforward f).obj P).IsQuasicoherent →
    ((Scheme.Modules.pushforward f').obj N).IsQuasicoherent →
    IsIso (scalarSectionsBaseChangeMapOf φ f f' g w a) →
    IsIso (pushforwardBaseChangeOf f (Spec.map φ) f' g w a)

end Langlands.AlgebraicGeometry.Modules.DerivedSections

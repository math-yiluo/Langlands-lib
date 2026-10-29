import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.AtPrime.Basic

universe u v w x y z

open scoped TensorProduct

namespace Langlands.Algebra

attribute [local instance] _root_.Algebra.TensorProduct.rightAlgebra

/-- Internal tensor-localization transition principle for the construction in Stacks 00QV. -/
def TensorPrimeLocalizationStatement : Prop :=
  ∀
    {A : Type u} {B : Type v} {Q : Type w} {Q' : Type x}
    {L : Type y} {C : Type z}
    [CommRing A] [CommRing B] [CommRing Q] [CommRing Q'] [CommRing L] [CommRing C]
    [IsLocalRing C]
    [Algebra A B] [Algebra A Q] [Algebra A Q'] [Algebra Q Q'] [Algebra B Q']
    [IsScalarTower A Q Q'] [IsScalarTower A B Q']
    [_root_.Algebra.IsPushout A Q B Q']
    [Algebra A L] [Algebra Q L] [IsScalarTower A Q L] [Algebra Q' C]
    (M : Submonoid Q) (N : Submonoid Q') [IsLocalization M L] [IsLocalization N C]
    (ψ : Q' →ₐ[B] (L ⊗[A] B))
    (_hψ : ψ.toRingHom.comp (algebraMap Q Q') =
      (_root_.Algebra.TensorProduct.includeLeftRingHom (R := A) (B := B)).comp
        (algebraMap Q L))
    (f : L ⊗[A] B →+* C) (_hf : f.comp ψ.toRingHom = algebraMap Q' C),
    letI := f.toAlgebra
    IsLocalization.AtPrime C ((IsLocalRing.maximalIdeal C).comap f)

end Langlands.Algebra

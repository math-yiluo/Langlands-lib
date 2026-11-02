import Mathlib
import Langlands.Algebra.EssFinitePresentation

/-! # Formal etaleness descended from a localized base change -/

universe u v w x y

namespace Langlands.CommutativeAlgebra

/-- Local algebra interface for descent of the etale locus in a flat cartesian
square. The ring `C` is a localization of the pushout `D`. -/
def EtaleLocalizedBaseChangeDescentStatement : Prop :=
  ∀ (A : Type u) (T : Type v) (B : Type w) (D : Type x) (C : Type y)
    [CommRing A] [CommRing T] [CommRing B] [CommRing D] [CommRing C]
    [Algebra A T] [Algebra A B] [Algebra A D] [Algebra T D] [Algebra B D]
    [IsScalarTower A T D] [IsScalarTower A B D] [Algebra.IsPushout A T B D]
    [Algebra A C] [Algebra T C] [Algebra B C] [Algebra D C]
    [IsScalarTower A T C] [IsScalarTower A B C]
    [IsScalarTower T D C] [IsScalarTower B D C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    (M : Submonoid D) [IsLocalization M C]
    [Module.Flat A C] [Module.FaithfullyFlat B C]
    [Algebra.FormallyUnramified T C],
    Langlands.Algebra.EssFinitePresentation A B → Algebra.FormallyEtale A B

end Langlands.CommutativeAlgebra

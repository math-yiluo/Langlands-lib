import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.LinearAlgebra.Dimension.Localization

/-! # Native finite flat rank and affine fraction-field degree -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Two affine comparisons for the native rank of an actual finite flat map.
The fraction-field algebra is the canonical extension of the given ring map. -/
def NativeFiniteFlatRankComparisonStatement : Prop :=
  (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      [IsAffine Y] [IsIntegral Y] [IsFinite f] [Flat f],
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    ∀ y : Y, f.finrank y = Module.finrank Γ(Y, ⊤) Γ(X, ⊤)) ∧
  (∀ (R S : Type u) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
      [Algebra R S] [FaithfulSMul R S] [Module.Finite R S] [Module.Flat R S],
    letI : Algebra (FractionRing R) (FractionRing S) :=
      FractionRing.liftAlgebra R (FractionRing S)
    ∀ p : PrimeSpectrum R,
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).finrank p =
        Module.finrank (FractionRing R) (FractionRing S))

end Langlands.AlgebraicGeometry

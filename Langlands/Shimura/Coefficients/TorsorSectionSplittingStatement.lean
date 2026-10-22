import Langlands.Shimura.Coefficients.Etale

/-! # Geometric torsor splitting of sections of arbitrary module sheaves -/

universe u v w

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

/-- Restriction along the graphs of the deck transformations identifies sections
over the product with a family of sections indexed by the group. -/
def TorsorSectionSplitting
    {C : Type w} [Category.{v} C] [HasBinaryProducts C]
    (J : GrothendieckTopology C) {R : Type u} [CommRing R]
    {G : Type u} [Group G] (Y : Action C G) : Prop :=
  ∀ (F : Sheaf J (ModuleCat.{u} R)) (U : Over Y.V),
    Function.Bijective
      (fun (s : F.obj.obj (op (Y.V ⨯ U.left))) (g : G) =>
        F.obj.map (prod.lift (U.hom ≫ Y.ρ g) (𝟙 U.left)).op s)

/-- The finite geometric torsor condition implies section splitting for every
module sheaf on the small etale site. This is a target, not a proved theorem. -/
def EtaleTorsorSectionSplittingStatement : Prop :=
  ∀ (X : Scheme.{u}) (G : Type u) [Group G]
    (Y : Action X.Etale G), IsFiniteGeometricTorsor X Y →
    ∀ (R : Type u) [CommRing R],
      TorsorSectionSplitting (R := R) (Scheme.smallEtaleTopology X) Y

end Langlands.Shimura.Coefficients

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Closed loci detected on affine charts glue -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Let `P` be a property of morphisms into a scheme `X` that is stable under
precomposition and is detected on the preimages of the affine opens of `X`. If, for every
affine open `U` of `X`, the morphisms `g : Y ⟶ U` with `P (g ≫ U.ι)` are exactly those
factoring through a closed immersion `Z_U ⟶ U`, then the morphisms into `X` satisfying `P`
are exactly those factoring through one closed immersion `Z ⟶ X`. -/
def ClosedLocusFromAffineChartsStatement : Prop :=
  ∀ (X : Scheme.{u}) (P : ∀ ⦃Y : Scheme.{u}⦄, (Y ⟶ X) → Prop),
    (∀ ⦃Y Y' : Scheme.{u}⦄ (f : Y' ⟶ Y) (g : Y ⟶ X), P g → P (f ≫ g)) →
    (∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ X),
      (∀ V : X.affineOpens, P ((g ⁻¹ᵁ (V : X.Opens)).ι ≫ g)) → P g) →
    (∀ U : X.affineOpens, ∃ (Z : Scheme.{u}) (ι : Z ⟶ (U : X.Opens).toScheme),
      IsClosedImmersion ι ∧
        ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ (U : X.Opens).toScheme),
          (∃ k : Y ⟶ Z, k ≫ ι = g) ↔ P (g ≫ (U : X.Opens).ι)) →
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ X), IsClosedImmersion ι ∧
      ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ X), (∃ k : Y ⟶ Z, k ≫ ι = g) ↔ P g

end Langlands.AlgebraicGeometry

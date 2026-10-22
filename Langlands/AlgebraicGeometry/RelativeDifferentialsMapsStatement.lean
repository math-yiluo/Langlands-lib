import Langlands.AlgebraicGeometry.RelativeDifferentialsMaps

/-! # Characterization and coherence of relative differential maps -/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

namespace Langlands.Scheme

/-- The cotangent map is characterized by the universal derivation and obeys the
identity and composition laws with the actual pullback coherence isomorphisms. -/
def RelativeDifferentialsMapLawsStatement : Prop :=
  (∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    {fX : X ⟶ S} {fY : Y ⟶ S} (w : g ≫ fY = fX),
    ∀ (α : (pullback g).obj (relativeDifferentials fY) ⟶ relativeDifferentials fX),
      (RelativeDerivation.postcomp (relativeDifferentialsDerivation fY)
        ((pullbackPushforwardAdjunction g).homEquiv _ _ α) =
          RelativeDerivation.precompOver g w (relativeDifferentialsDerivation fX)) ↔
      α = relativeDifferentialsMap g w) ∧
  (∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
    relativeDifferentialsMap (𝟙 X) (Category.id_comp f) =
      (pullbackId X).hom.app (relativeDifferentials f)) ∧
  (∀ {X Y Z S : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    {fX : X ⟶ S} {fY : Y ⟶ S} {fZ : Z ⟶ S}
    (wg : g ≫ fY = fX) (wh : h ≫ fZ = fY),
    (pullbackComp g h).inv.app (relativeDifferentials fZ) ≫
        (pullback g).map (relativeDifferentialsMap h wh) ≫
        relativeDifferentialsMap g wg =
      relativeDifferentialsMap (g ≫ h) (by rw [Category.assoc, wh, wg]))

end Langlands.Scheme

import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Langlands.GroupScheme.Dilatation.CoordinateAlgebra

/-! # Blow-ups with a chart at a global section of the centre -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Existence of blow-ups of locally noetherian schemes along an ideal sheaf containing a
global section `t`, together with their `t`-charts: a proper morphism `g : X' ⟶ X` which is an
isomorphism over the complement of the centre, and for every affine open `U` of `X` an open
immersion of the spectrum of the dilatation algebra `Γ(X, U)[I(U)/t]` into `X'` over `U`. -/
def BlowupChartStatement : Prop :=
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] (t : Γ(X, ⊤)) (I : X.IdealSheafData),
    (∀ U : X.affineOpens, X.presheaf.map (homOfLE le_top).op t ∈ I.ideal U) →
    ∃ (X' : Scheme.{u}) (g : X' ⟶ X), IsProper g ∧ IsIso (g ∣_ I.support.compl) ∧
      ∀ U : X.affineOpens,
        ∃ j : Spec (CommRingCat.of (GroupScheme.Dilatation.coordinateAlgebra
            (X.presheaf.map (homOfLE le_top).op t) (I.ideal U))) ⟶ X',
          IsOpenImmersion j ∧
            j ≫ g = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) _)) ≫ U.2.fromSpec

end Langlands.AlgebraicGeometry

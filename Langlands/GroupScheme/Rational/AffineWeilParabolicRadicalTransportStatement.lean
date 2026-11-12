import Langlands.GroupScheme.AffineWeilRestrictionMaps
import Langlands.GroupScheme.Rational.LeviSubgroup
import Mathlib.FieldTheory.Separable

/-! # Parabolic and radical diagrams under finite separable Weil restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Finite separable Weil restriction preserves parabolic-radical diagrams, and
every such diagram in the restricted group comes from one over the extension,
up to actual isomorphisms commuting with both inclusions. -/
def AffineWeilParabolicRadicalTransportStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsSeparable k K] (G : GroupScheme (Spec (CommRingCat.of K)))
    (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    (∀ (P U : GroupScheme (Spec (CommRingCat.of K)))
      [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
      [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom]
      (p : P ⟶ G) (r : U ⟶ P),
      IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
        IsParabolicSubgroup (AffineWeil.map k K p) ∧
          LeviSubgroup.IsGeometricUnipotentRadical (AffineWeil.map k K r)) ∧
    (∀ (P U : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ AffineWeil.groupScheme k K G)
      (r : U ⟶ P),
      IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
        ∃ (P' U' : GroupScheme (Spec (CommRingCat.of K)))
          (aP : IsAffine P'.X.left) (lP : LocallyOfFiniteType P'.X.hom)
          (aU : IsAffine U'.X.left) (lU : LocallyOfFiniteType U'.X.hom),
          haveI := aP
          haveI := lP
          haveI := aU
          haveI := lU
          ∃ (p' : P' ⟶ G) (r' : U' ⟶ P'),
            IsParabolicSubgroup p' ∧ LeviSubgroup.IsGeometricUnipotentRadical r' ∧
              ∃ (eP : P ≅ AffineWeil.groupScheme k K P')
                (eU : U ≅ AffineWeil.groupScheme k K U'),
                eP.hom ≫ AffineWeil.map k K p' = p ∧
                  eU.hom ≫ AffineWeil.map k K r' = r ≫ eP.hom)

end Langlands.GroupScheme

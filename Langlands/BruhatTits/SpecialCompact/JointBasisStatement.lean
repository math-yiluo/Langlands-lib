import Langlands.BruhatTits.SpecialCompact.Properties
import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty
import Langlands.BruhatTits.Iwasawa.PointProducts
import Langlands.GroupScheme.Reductive.Basic
import Langlands.Representation.Plancherel.RenardSpecialCompactComparison
import Langlands.Representation.Plancherel.RenardSameCompactLeviComparison

/-! # A common geometric witness for the special compact and simultaneous basis -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.Cartan

namespace Langlands.BruhatTits.SpecialCompact

/-- General existence target at one geometric special vertex: the special
compact properties, standard-Levi inheritance, actual Iwasawa products,
Cartan comparison and simultaneous normal compact-open basis all use the
same `D`, `x`, `i` and `ν`. The actual centralizer and its character comparison
are also constructed in the conclusion and shared by the Levi Cartan clauses.
This is a conclusion to construct, not a property asserted for every weak
`KPApartmentData`. Sufficient corrected validity remains separate. -/
def JointSpecialCompactBasisExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice S),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∃ (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
        (Z : GroupScheme (Spec (CommRingCat.of F))) (j : Z ⟶ G)
        (s : S.toGrp ⟶ Z),
        IsClosedSubgroup j ∧
          (torusCentralizer i).IsRepresentedBy j ∧
          s ≫ j = i ∧
          ∃ h : Function.Bijective (restrictionEvaluation s),
            D.IsSpecialApartmentVertex x ∧
              SpecialCompactProperties F i ν (D.specialCompactSubgroup x) ∧
              SpecialLeviInheritance F hi ν D x ∧
              Iwasawa.ParabolicPointProductFamily i ν (D.specialCompactSubgroup x) ∧
              Langlands.Plancherel.RenardCartan.SpecialCompactRenardComparison
                D x ν j s h ∧
              (∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
                haveI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
                  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
                Iwasawa.ParabolicPointProductFamily
                  (Standard.leviTorusHom i ν J) ν
                  (D.specialCompactLeviSubgroup ν J x)) ∧
              Langlands.Plancherel.RenardCartan.SpecialCompactStandardLeviCompatibility
                D x ν s h j ∧
              SimultaneousStandardBasisAt i ν (D.specialCompactSubgroup x)

end Langlands.BruhatTits.SpecialCompact

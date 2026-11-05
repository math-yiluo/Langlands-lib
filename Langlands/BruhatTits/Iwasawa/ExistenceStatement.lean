import Langlands.BruhatTits.Iwasawa.PointProducts
import Langlands.BruhatTits.SpecialCompact.Properties
import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-!
# Iwasawa decomposition with the same available special compact witnesses

The general-group target concludes existence of full corrected available data,
the sibling special compact package, and both Iwasawa orders at the same points
and compact subgroups. It assumes neither building existence nor Iwasawa.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.BruhatTits.Iwasawa

/-- General connected reductive local-field Iwasawa target, with the same
assignment, apartment, special vertex and compact subgroup as the special-compact
existence package, including its standard-Levi restrictions.

The `HEq` point witnesses identify the actual parahoric chart with the named
apartment point; the explicit compact-subgroup equality fixes its compact factor.
The whole-building clause also covers every special reduced-building vertex.
Both products hold for the inherited compact subgroup of each actual standard Levi. -/
def IwasawaExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∃ (𝔅 : KPBuildingAssignment.{u}) (D : KPApartmentData i (localFieldOrder F)),
        𝔅.IsAvailableFor F G hG ∧
          (𝔅.datum F G hG).base.S = S ∧ HEq (𝔅.datum F G hG).base.i i ∧
          HEq (𝔅.datum F G hG).base.apartment D ∧
          ∃ x : D.Apartment,
            D.IsSpecialApartmentVertex x ∧
              SpecialCompactProperties F i ν (D.specialCompactSubgroup x) ∧
              (∃ xB : (𝔅.datum F G hG).base.Apartment,
                HEq xB x ∧
                  (𝔅.datum F G hG).base.apartment.specialCompactSubgroup xB =
                    D.specialCompactSubgroup x ∧
                  ParabolicPointProductFamily i ν ((𝔅.datum F G hG).base.parahoricAt xB) ∧
                  (𝔅.datum F G hG).base.parahoricAt xB ≤ D.specialCompactSubgroup x) ∧
              ParabolicPointProductFamily i ν (D.specialCompactSubgroup x) ∧
              (∀ y : (𝔅.datum F G hG).base.ReducedBuilding,
                (𝔅.datum F G hG).base.IsSpecialPoint y →
                  (𝔅.datum F G hG).base.IsVertex y →
                  ∀ Q : Subgroup (rationalPoints G), (𝔅.datum F G hG).base.IsParahoricAt y Q →
                    ParabolicPointProductFamily i ν Q ∧
                      Q ≤ (𝔅.datum F G hG).base.compactStabilizer y ∧
                      ParabolicPointProductFamily i ν
                        ((𝔅.datum F G hG).base.compactStabilizer y) ∧
                      IsCompactOpenMaximal F ((𝔅.datum F G hG).base.compactStabilizer y)) ∧
              ∀ J ⊆ simpleRelativeRoots i ν,
                haveI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
                  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
                haveI : Mono (Standard.leviTorusHom i ν J).hom.hom.left :=
                  (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi).isSplitSubtorus.mono
                ∃ (hM : IsConnectedReductive (Standard.leviScheme i ν J))
                  (DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F)),
                  𝔅.IsAvailableFor F (Standard.leviScheme i ν J) hM ∧
                    (𝔅.datum F (Standard.leviScheme i ν J) hM).base.S = S ∧
                    HEq (𝔅.datum F (Standard.leviScheme i ν J) hM).base.i
                      (Standard.leviTorusHom i ν J) ∧
                    HEq (𝔅.datum F (Standard.leviScheme i ν J) hM).base.apartment DM ∧
                    ∃ xM : DM.Apartment,
                      SpecialLeviRestriction F ν D x J DM xM ∧
                        (∃ xBM : (𝔅.datum F (Standard.leviScheme i ν J) hM).base.Apartment,
                          HEq xBM xM ∧
                            (𝔅.datum F (Standard.leviScheme i ν J) hM).base.apartment.specialCompactSubgroup
                                xBM = DM.specialCompactSubgroup xM ∧
                            ParabolicPointProductFamily (Standard.leviTorusHom i ν J) ν
                              ((𝔅.datum F (Standard.leviScheme i ν J) hM).base.parahoricAt xBM) ∧
                            (𝔅.datum F (Standard.leviScheme i ν J) hM).base.parahoricAt xBM ≤
                              DM.specialCompactSubgroup xM) ∧
                        ParabolicPointProductFamily (Standard.leviTorusHom i ν J) ν
                          (DM.specialCompactSubgroup xM)

end Langlands.BruhatTits.Iwasawa

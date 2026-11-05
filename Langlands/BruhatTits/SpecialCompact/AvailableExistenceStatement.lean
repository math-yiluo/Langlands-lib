import Langlands.BruhatTits.SpecialCompact.Properties
import Langlands.Geometry.Building.FullValidity.Assignment

/-!
# Existence of a special maximal compact subgroup for available Bruhat–Tits data

The general existence target for every connected reductive group over a nonarchimedean local
field (KP Theorem 4.2.15(1) at a special vertex; Renard, Théorème V.5.1(2), (3), (5)) in which
Bruhat–Tits theory is available in the sense of the corrected KP Definition 4.1.26
(`KPBuildingAssignment.IsAvailableFor`) for `G` and for every actual standard Levi subgroup, and
`K_0` is the compact stabilizer of a special vertex of the apartment of the same data.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.SpecialCompact

/-- For every nonarchimedean local field `F`, connected reductive `G` over `F`, maximal split
torus `i : S → G` and generic cocharacter `ν` of `S` (fixing the minimal parabolic), there are
an assignment `𝔅` of Bruhat–Tits data to all connected reductive groups over all nonarchimedean
local fields in universe `u`, and apartment data `D` for `(G, S)`, such that

* Bruhat–Tits theory is available for `G` in `𝔅` (corrected KP Definition 4.1.26), and the
  data of `𝔅` for `G` have the torus `i : S → G` and the apartment `A(S) = D`;
* there is a special vertex `x` of the apartment whose
  `K_0 = G(F)^1 ∩ G(F)_x = D.specialCompactSubgroup x` is open, bounded and compact, maximal
  among bounded and among compact subgroups, contains representatives of the relative Weyl
  group, and satisfies `K_0 ∩ P_J = (K_0 ∩ M_J)(K_0 ∩ U_J)` for every standard parabolic;
* for every set `J` of simple relative roots, the actual standard Levi `M_J` is connected
  reductive, Bruhat–Tits theory is available for `M_J` in the same `𝔅`, the data of `𝔅` for
  `M_J` have the torus `S → M_J` and an apartment `DM`, and some `xM` is related to `x` by
  `SpecialLeviRestriction`. -/
def AvailableSpecialMaximalCompactExistence : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
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
                    ∃ xM : DM.Apartment, SpecialLeviRestriction F ν D x J DM xM

end Langlands.BruhatTits.SpecialCompact

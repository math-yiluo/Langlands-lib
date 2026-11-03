import Langlands.BruhatTits.SpecialCompact.Properties
import Langlands.Geometry.Building.KPApartmentAxioms
import Langlands.GroupScheme.Reductive.Basic

/-!
# Existence of a special maximal compact subgroup adapted to a maximal split torus

The general existence target for every connected reductive group over a nonarchimedean local
field (KP Theorem 4.2.15(1) at a special vertex; Renard, Théorème V.5.1(2), (3), (5)), with
apartment data satisfying the Kaletha–Prasad axioms `SatisfiesApartmentAxioms` and Axiom 4.1.2,
for `G` and for every actual standard Levi subgroup.

This target is supplementary: the data are not required to satisfy the full corrected KP
Definition 4.1.26, nor Axiom 4.1.4 for all maximal split tori.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.SpecialCompact

/-- For every nonarchimedean local field `F`, connected reductive `G` over `F`, maximal split
torus `i : S → G` and generic cocharacter `ν` of `S` (fixing the minimal parabolic), there are
a centralizer datum `C` and apartment data `D` for `(G, S)` satisfying the axioms V 6 on `Z(F)`,
V 7 and AS 2–AS 5 (`SatisfiesApartmentAxioms`) and Axiom 4.1.2 (`HasBoundedOpenStabilizers`),
and a special vertex `x` of the reduced apartment, such that the actual
`K_0 = G(F)^1 ∩ G(F)_x` is open, bounded and compact, maximal among bounded and among compact
subgroups, contains representatives of the relative Weyl group, and satisfies
`K_0 ∩ P_J = (K_0 ∩ M_J)(K_0 ∩ U_J)` for every standard parabolic. Moreover, for every set `J`
of simple relative roots the actual standard Levi `M_J` carries a centralizer datum `CM` and
apartment data `DM` satisfying the same axioms, with a point `xM` related to `x` by
`SpecialLeviRestriction`. -/
def SpecialMaximalCompactExistence : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∃ (C : CentralizerDatum i) (D : KPApartmentData i (localFieldOrder F)),
        D.SatisfiesApartmentAxioms C ∧ D.HasBoundedOpenStabilizers ∧
          ∃ x : D.Apartment,
            D.IsSpecialApartmentVertex x ∧
              SpecialCompactProperties F i ν (D.specialCompactSubgroup x) ∧
              ∀ J ⊆ simpleRelativeRoots i ν,
                haveI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
                  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
                haveI : Mono (Standard.leviTorusHom i ν J).hom.hom.left :=
                  (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi).isSplitSubtorus.mono
                ∃ (CM : CentralizerDatum (Standard.leviTorusHom i ν J))
                  (DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F)),
                  DM.SatisfiesApartmentAxioms CM ∧ DM.HasBoundedOpenStabilizers ∧
                    ∃ xM : DM.Apartment, SpecialLeviRestriction F ν D x J DM xM

end Langlands.BruhatTits.SpecialCompact

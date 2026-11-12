import Langlands.BruhatTits.SpecialCompact.Properties
import Langlands.Geometry.Building.KPApartmentAxioms

/-! # The apartment axioms pass to the restriction to a standard Levi subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Geometry.Building

/-- V 6, V 7 and AS 2–AS 5 pass from an apartment class of `(G, S)` to its restriction to a
standard Levi subgroup `M_J` at the same torus (KP §6.7, over a nonarchimedean local field). Let
`D` be apartment data of `(G, S)` and `DM` apartment data of `(M_J, S)` such that some point of
`DM` is the restriction of some point of `D` (`IsLeviRestriction`), and let `C`, `CM` be
centralizer data of `S` in `G` and in `M_J`. If `D` satisfies V 6 on `Z_G(S)(F)`, V 7 and AS 2–AS 5
for `C`, then `DM` satisfies V 6 on `Z_{M_J}(S)(F)`, V 7 and AS 2–AS 5 for `CM`. -/
def LeviApartmentAxiomsInheritanceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∀ J ⊆ simpleRelativeRoots i ν,
        haveI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
          (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
        haveI : Mono (Standard.leviTorusHom i ν J).hom.hom.left :=
          (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi).isSplitSubtorus.mono
        ∀ (C : CentralizerDatum i) (CM : CentralizerDatum (Standard.leviTorusHom i ν J))
          (D : KPApartmentData i (localFieldOrder F))
          (DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F)),
          (∃ (x : D.Apartment) (xM : DM.Apartment),
            IsLeviRestriction (Standard.leviHom i ν J) x xM) →
          D.SatisfiesApartmentAxioms C → DM.SatisfiesApartmentAxioms CM

end Langlands.Geometry.Building

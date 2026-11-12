import Langlands.BruhatTits.SpecialCompact.Properties

/-! # Restriction of apartment valuations to a standard Levi subgroup (KP Lemma 6.7.1) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Geometry.Building

/-- Kaletha–Prasad Lemma 6.7.1 (1)–(4) for the actual standard Levi `M_J` of a nonarchimedean
local field `F` at the same maximal split torus `S`. For every apartment data `D` of `(G, S)`
there are apartment data `DM` of `(M_J, S)` such that

* every point `x` of `D` has a restriction `xM` in `DM` (`IsLeviRestriction`: `xM_a = x_a` on
  `M_J(F)` for the relative roots `a` of `(M_J, S)`);
* every point of `DM` is such a restriction, so `DM` is the class `A(M_J, S) = {φ_M}`;
* two points of `D` have the same restriction exactly when they differ by a vector of `V(S)`
  on which every relative root of `(M_J, S)` vanishes.

Being `KPApartmentData`, `DM` is an equipollence class of valuations of the root datum of
`(M_J, S)`, compatible with `ω` on `S(F)` and stable under the normalizer points of `S` in
`M_J`. -/
def LeviApartmentRestrictionStatement : Prop :=
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
        ∀ D : KPApartmentData i (localFieldOrder F),
          ∃ DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F),
            (∀ x : D.Apartment, ∃ xM : DM.Apartment,
              IsLeviRestriction (Standard.leviHom i ν J) x xM) ∧
            (∀ xM : DM.Apartment, ∃ x : D.Apartment,
              IsLeviRestriction (Standard.leviHom i ν J) x xM) ∧
            ∀ (x x' : D.Apartment) (xM xM' : DM.Apartment),
              IsLeviRestriction (Standard.leviHom i ν J) x xM →
              IsLeviRestriction (Standard.leviHom i ν J) x' xM' →
                (xM = xM' ↔ ∃ v : V S, x'.val = v +ᵥ x.val ∧
                  ∀ a ∈ relativeRoots (Standard.leviTorusHom i ν J), eval S a v = 0)

end Langlands.Geometry.Building

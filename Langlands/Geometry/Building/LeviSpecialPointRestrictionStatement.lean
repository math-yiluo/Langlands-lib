import Langlands.BruhatTits.SpecialCompact.Properties

/-! # Affine roots and special points under restriction to a standard Levi (KP §6.7.2) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Geometry.Building

/-- Kaletha–Prasad §6.7.2 for the actual standard Levi `M_J` of a nonarchimedean local field
`F` at the same maximal split torus `S`. Let `D` and `DM` be apartment data of `(G, S)` and
`(M_J, S)`, and suppose some point of `DM` is the restriction (`IsLeviRestriction`) of a point
of `D`. Then

* every affine root `ψM ∈ Ψ(M_J, S)` of `DM` is the pullback of an affine root
  `ψ ∈ Ψ(G, S)` of `D` along the restriction: `ψ x = ψM xM` whenever `xM` is the restriction
  of `x`; the same holds for `Ψ′(M_J, S)` and `Ψ′(G, S)`;
* if `xM` is the restriction of a special point `x` of `D`, then `xM` is a special point of
  `DM` and a vertex of its affine root system. -/
def LeviSpecialPointRestrictionStatement : Prop :=
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
        ∀ (D : KPApartmentData i (localFieldOrder F))
          (DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F)),
          (∃ (x : D.Apartment) (xM : DM.Apartment),
            IsLeviRestriction (Standard.leviHom i ν J) x xM) →
            (∀ ψM ∈ DM.affineRoots, ∃ ψ ∈ D.affineRoots,
              ∀ (x : D.Apartment) (xM : DM.Apartment),
                IsLeviRestriction (Standard.leviHom i ν J) x xM → ψ x = ψM xM) ∧
            (∀ ψM ∈ DM.extendedAffineRoots, ∃ ψ ∈ D.extendedAffineRoots,
              ∀ (x : D.Apartment) (xM : DM.Apartment),
                IsLeviRestriction (Standard.leviHom i ν J) x xM → ψ x = ψM xM) ∧
            ∀ (x : D.Apartment) (xM : DM.Apartment),
              IsLeviRestriction (Standard.leviHom i ν J) x xM →
                AffineRootSystem.IsSpecialPoint D.affineRoots x →
                  AffineRootSystem.IsSpecialPoint DM.affineRoots xM ∧
                    AffineRootSystem.IsVertex DM.affineRoots xM

end Langlands.Geometry.Building

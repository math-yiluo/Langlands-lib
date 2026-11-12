import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Geometry.Building.SpecialCompactLevi

/-!
# The Levi intersection of a special compact subgroup is special compact in the Levi

Renard, Théorème V.5.1(5), for valid corrected Bruhat–Tits assignments: at a special vertex
of the apartment of the data for `G`, the preimage of `K_0` in each actual standard Levi
`M_J(F)` is the special compact subgroup at a special vertex of available data for `M_J`
based at the same torus. This is a statement target conditional on validity.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.SpecialCompact

/-- Let `𝔅` be valid, `B` the data of `𝔅` for `G`, `ν` a generic cocharacter of `B.S` and `x`
a special vertex of the apartment of `B`. For every set `J` of simple relative roots, the
actual standard Levi `M_J` is connected reductive and there are an assignment `𝔅M` for which
Bruhat–Tits theory is available for `M_J`, whose data for `M_J` have the torus `B.S` with
inclusion `Standard.leviTorusHom B.i ν J`, and a special vertex `xM` of their apartment whose
special compact subgroup is the preimage `B.apartment.specialCompactLeviSubgroup ν J x` of
`K_0` in `M_J(F)`. -/
def AvailableSpecialLeviCompactStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsValid →
      let B := (𝔅.datum F G hG).base
      ∀ ν : cocharacterLattice B.S, IsGenericCocharacter B.i ν →
        ∀ x : B.Apartment, B.apartment.IsSpecialApartmentVertex x →
          ∀ J ⊆ simpleRelativeRoots B.i ν,
            haveI : IsAffineHom (Standard.leviScheme B.i ν J).X.hom :=
              (Standard.isClosedSubgroup_leviHom B.i ν J).isAffineHom
            ∃ (hM : IsConnectedReductive (Standard.leviScheme B.i ν J))
              (𝔅M : KPBuildingAssignment.{u}),
              𝔅M.IsAvailableFor F (Standard.leviScheme B.i ν J) hM ∧
                (𝔅M.datum F (Standard.leviScheme B.i ν J) hM).base.S = B.S ∧
                HEq (𝔅M.datum F (Standard.leviScheme B.i ν J) hM).base.i
                  (Standard.leviTorusHom B.i ν J) ∧
                ∃ xM : (𝔅M.datum F (Standard.leviScheme B.i ν J) hM).base.Apartment,
                  (𝔅M.datum F (Standard.leviScheme B.i ν J) hM).base.apartment.IsSpecialApartmentVertex
                      xM ∧
                    (𝔅M.datum F (Standard.leviScheme B.i ν J) hM).base.apartment.specialCompactSubgroup
                        xM =
                      B.apartment.specialCompactLeviSubgroup ν J x

end Langlands.BruhatTits.SpecialCompact

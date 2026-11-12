import Langlands.Geometry.Building.FullValidity.Assignment

/-!
# Rebasing a valid corrected Bruhat–Tits assignment at a prescribed maximal split torus

The data of a `KPBuildingAssignment` for one group fix a maximal split torus. This target says
that a valid assignment can be replaced by a valid assignment whose data for a given group are
based at any prescribed maximal split torus. It is a conditional statement target, not an
existence assertion for valid assignments.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.SpecialCompact

/-- If `𝔅` is a valid corrected KP assignment (Definition 4.1.26 for every connected
reductive group over every nonarchimedean local field in universe `u`), then for every
nonarchimedean local field `F`, connected reductive `G` over `F` and maximal split torus
`i : S → G` there is a valid assignment `𝔅'` whose data for `G` have the torus `S` and the
inclusion `i`. -/
def ValidAssignmentTorusRebasingStatement : Prop :=
  ∀ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsValid →
    ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
      (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
        haveI : IsAffineHom G.X.hom := hG.isAffineHom
        ∃ 𝔅' : KPBuildingAssignment.{u}, 𝔅'.IsValid ∧
          (𝔅'.datum F G hG).base.S = S ∧ HEq (𝔅'.datum F G hG).base.i i

end Langlands.BruhatTits.SpecialCompact

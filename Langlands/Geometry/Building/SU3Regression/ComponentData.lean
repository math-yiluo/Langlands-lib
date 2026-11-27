import Langlands.GroupScheme.Examples.HermitianRootReductive
import Langlands.GroupScheme.Examples.HermitianRootSimplyConnected
import Langlands.Geometry.Building.DepthZero.Definitions
import Langlands.Geometry.Building.IwahoriWeyl

/-!
# The quasi-split `SU_3`: no component and no length-zero data

A regression example for Kaletha–Prasad building data of the simply connected quasi-split
special unitary group `G = SU_3` of a separable quadratic extension `E/F` of a nonarchimedean
local field `F`, for the Library's model `HermitianRoot.SchemeModel.groupScheme F E H w hw`
with middle index `Unit`.

`SU3ComponentDataStatement`: `G(F)^0 = G(F)^1 = G(F)` (KP Definition 2.6.23); for every facet
of the reduced building the parahoric `D.parahoric x` is both the pointwise fixer and the
setwise stabilizer of the facet; and `Z(F)^0` is normal in `N(F)`, the stabilizer `W̃^0_C`
of every chamber `C` of the apartment is trivial and the Iwahori–Weyl group is its affine part
(KP §7.8).

This is a statement; nothing here proves it.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

/-- **No component or length-zero data for `SU_3`.** For every separable quadratic extension
`E/F` of a nonarchimedean local field, every weight `w` and every KP building datum `D` of
`G = HermitianRoot.SchemeModel.groupScheme F E H w hw` satisfying the group axioms, with
`P = D.base`:

* `G(F)^0 = G(F)` and `G(F)^1 = G(F)`;
* for every facet `x` of the reduced building, the parahoric `D.parahoric x` (the integral
  points of the neutral model of `x`) equals the subgroup of `G(F)` fixing `x` pointwise and the
  subgroup of `G(F)` preserving `x`;
* `Z(F)^0` is normal in `N(F)`, the Iwahori–Weyl group `W̃^0 = N(F)/Z(F)^0` equals its affine
  part `(N(F) ∩ G(F)^0)/Z(F)^0`, and the stabilizer `W̃^0_C` of every chamber `C` of the
  apartment is trivial. -/
def SU3ComponentDataStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E : Type u) [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    [Algebra.IsSeparable F E]
    (H : HermitianRoot.DiagonalForm (SU3Root.fieldInvolution F E) Unit) (w : Unit → Eˣ)
    (hw : ∀ i, (w i : E) = H.weight i)
    (D : KPBuildingDatum (HermitianRoot.SchemeModel.groupScheme F E H w hw)),
    D.SatisfiesGroupAxioms →
      D.base.zeroSubgroup = ⊤ ∧
        Plancherel.rationalCommonNormKernel (HermitianRoot.SchemeModel.groupScheme F E H w hw) =
          ⊤ ∧
        (∀ x : BuildingFacet D.base.toValuationBuildingData,
          D.parahoric x = D.base.pointwiseFixer x.val ∧
            D.parahoric x = MulAction.stabilizer
              (rationalPoints (HermitianRoot.SchemeModel.groupScheme F E H w hw)) x.val) ∧
        ∃ _ : D.base.normalizerZero.Normal,
          D.base.affinePart = ⊤ ∧
            ∀ C : Set D.base.Apartment, AffineRootSystem.IsChamber D.base.affineRoots C →
              D.base.chamberStabilizer C = ⊥

end Langlands.Geometry.Building

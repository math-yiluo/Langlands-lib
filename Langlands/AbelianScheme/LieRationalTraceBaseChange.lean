import Langlands.AbelianScheme.LieRationalBaseChange
import Langlands.AbelianScheme.LieRationalTrace
import Langlands.AlgebraicGeometry.LocalTraceTransport
import Langlands.Shimura.PEL.LieDeterminantBaseChange

/-! # Actual rational Lie trace pullback from canonical integral naturality -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

namespace Langlands.AbelianScheme

variable {S T : Scheme.{u}} {R : CommRingCat.{u}} [Algebra ℚ R]
    (p : S ⟶ Spec R) (b : T ⟶ S) (B : AbelianScheme S)
    {O : Type v} [Ring O] (α : O →+* End0 B)

/-- The rational Lie trace agrees on every common smaller chart open. -/
theorem lieRationalSectionTrace_overlap
    {U U' W : S.Opens} {I J : Type u} [Fintype I] [Fintype J]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (e' : SheafOfModules.free (R := S.ringCatSheaf.over U') J ≅ B.Lie.over U')
    (a : O) (i : W ⟶ U) (j : W ⟶ U') :
    lieRationalSectionTrace p B α e a (Over.mk i) =
      lieRationalSectionTrace p B α e' a (Over.mk j) :=
  localSectionTrace_overlap e e' (lieRationalOrderAction p B α a) i j

/-- Canonical integral naturality gives pullback of the actual rational Lie trace. -/
theorem lieRationalSectionTrace_baseChange_of_naturality
    (naturality : LieBaseChangeNaturalityStatement S)
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : O) (V : Over U) :
    b.app V.left (lieRationalSectionTrace p B α e a V) =
      lieRationalSectionTrace (b ≫ p) ((baseChange b).obj B)
        (baseChangeRationalOrderAction b B α) (lieBaseChangeChart b B e) a
        (Over.mk ((TopologicalSpace.Opens.map b.base).map V.hom)) := by
  apply localSectionTrace_pullback_transport
  exact localHomPullback_over_intertwine b (lieBaseChangeIso b B)
    (lieRationalOrderAction p B α a)
    (lieRationalOrderAction (b ≫ p) ((baseChange b).obj B)
      (baseChangeRationalOrderAction b B α) a)
    (lieRationalOrderAction_baseChange_of_naturality p b naturality B α a) U

end Langlands.AbelianScheme

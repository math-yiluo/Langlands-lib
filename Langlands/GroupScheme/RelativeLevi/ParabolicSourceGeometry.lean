import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.SmoothConnectedGeometryProof

/-! # Geometry of sources of relative parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- A relative parabolic in a reductive group has geometrically connected fibres. -/
theorem IsRelativeParabolicSubgroup.geometricallyConnected
    {S : Scheme.{u}} {G P : GroupScheme S} {i : P ⟶ G}
    (hi : IsRelativeParabolicSubgroup i) (hG : IsReductive G) :
    GeometricallyConnected P.X.hom := by
  apply (GeometricallyConnected.iff_geometricallyConnected_fiber P.X.hom).mpr
  intro s
  let b := S.fromSpecResidueField s
  let Gk := (GroupScheme.baseChange b).obj G
  let Pk := (GroupScheme.baseChange b).obj P
  let ik := (GroupScheme.baseChange b).map i
  have hGk : IsConnectedReductive Gk := hG.isConnectedReductive_residueFiber s
  have hik : IsParabolicSubgroup ik := hi.residueFiber s
  let : Smooth Gk.X.hom := hGk.smooth
  let : IsAffineHom Gk.X.hom := hGk.isAffineHom
  let : IsClosedImmersion ik.hom.hom.left := hik.isClosedSubgroup
  let : Mono ik.hom.hom := Over.mono_of_mono_left _
  let : Smooth P.X.hom := hi.smooth
  let : IsAffineHom P.X.hom := hi.isAffineHom
  have hsm : Smooth Pk.X.hom :=
    inferInstanceAs (Smooth (Limits.pullback.snd P.X.hom b))
  have haff : IsAffineHom Pk.X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd P.X.hom b))
  obtain ⟨χ, hχ⟩ :=
    ParabolicDynamicProof.exists_dynamicPresentation_of_isParabolicSubgroup hGk ik hik
  have hconn : ConnectedSpace Pk.X.left :=
    ((dynamicConnected (S.residueField s) Gk χ Pk ik).2 hGk.connectedSpace).1
      ⟨inferInstance, hχ⟩
  let : GeometricallyIntegral Pk.X.hom :=
    smoothConnectedAffineGeometry.1 (S.residueField s) Pk hsm haff hconn
  change GeometricallyConnected Pk.X.hom
  refine ⟨?_⟩
  intro K _ y Z fst snd hp
  let : IsIntegral Z :=
    GeometricallyIntegral.geometrically_isIntegral (f := Pk.X.hom) y fst snd hp
  infer_instance

/-- Retain the actual source together with the geometry needed by the local
smooth-group arguments. -/
def relativeParabolicSourceGeometry
    {S : Scheme.{u}} {G P : GroupScheme S}
    (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i) (hG : IsReductive G) :
    {H : GroupScheme S // Smooth H.X.hom ∧ IsAffineHom H.X.hom ∧
      GeometricallyConnected H.X.hom} :=
  ⟨P, hi.smooth, hi.isAffineHom, hi.geometricallyConnected hG⟩

@[simp] theorem relativeParabolicSourceGeometry_val
    {S : Scheme.{u}} {G P : GroupScheme S}
    (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i) (hG : IsReductive G) :
    (relativeParabolicSourceGeometry i hi hG).val = P := rfl

end Langlands.GroupScheme

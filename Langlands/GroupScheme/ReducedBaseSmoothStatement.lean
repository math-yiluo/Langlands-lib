import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Group schemes with smooth connected fibres over a reduced base are smooth

SGA 3, Exposé VI_B, Corollaire 4.4: over a reduced base, a group scheme whose fibres are
smooth of locally constant dimension has a smooth relative identity component. This module
states the case of a locally Noetherian base and connected fibres, where the relative
identity component is the whole group.
-/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- SGA 3, Exposé VI_B, Corollaire 4.4, for a locally Noetherian base and connected fibres:
let `H` be a group scheme locally of finite type over a reduced locally Noetherian scheme `S`.
If every fibre `H_s` is smooth over the residue field `κ(s)` and connected, and the fibre
dimension `s ↦ dim H_s` is locally constant on `S`, then `H` is smooth over `S`. -/
def ReducedBaseConnectedFibreSmoothStatement : Prop :=
  ∀ (S : Scheme.{u}) (H : GroupScheme S), IsReduced S → IsLocallyNoetherian S →
    LocallyOfFiniteType H.X.hom →
    (∀ s : S, Smooth (H.X.hom.fiberToSpecResidueField s)) →
    (∀ s : S, ConnectedSpace (H.X.hom.fiber s)) →
    IsLocallyConstant (fun s : S => topologicalKrullDim (H.X.hom.fiber s)) →
      Smooth H.X.hom

end Langlands.GroupScheme

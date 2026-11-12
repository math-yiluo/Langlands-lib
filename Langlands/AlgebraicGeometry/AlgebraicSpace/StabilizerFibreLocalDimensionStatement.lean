import Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitQuotientStatement
import Langlands.AlgebraicGeometry.SchemeLocalFiberDimension

/-!
# Stabilizer fibres are equidimensional

Let a group scheme `G` locally of finite type over a scheme `S` act on a scheme `V` over
`S`. The fibre of the stabilizer scheme over a point `v` of `V` is a group scheme locally
of finite type over the residue field `κ(v)`, so it is equidimensional (Stacks Project,
Lemma 39.8.1, Tag 045X): its dimension at every point equals its dimension. This is the
input to the semicontinuity argument for the orbit-dimension strata in Conrad's
Example 5.5.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open Langlands (GroupScheme)
open Langlands.GroupScheme (SchemeAction)
open Langlands.AlgebraicGeometry.SchemeFiberGeometry (relativeTopologicalKrullDimAt)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Stabilizer fibres are equidimensional: let `G` be a group scheme locally of finite type
over a scheme `S`, acting by `a` on a scheme `V` over `S`, and let `σ` be the projection to
`V` of the stabilizer scheme, the base change of the action graph `(g, v) ↦ (g.v, v)` along
the diagonal of `V`. Then at every point `x` of the stabilizer scheme, the dimension at `x`
of the fibre of `σ` through `x` equals the dimension of that fibre. -/
def StabilizerFibreLocalDimensionStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) (V : Over S) (a : SchemeAction G V),
    LocallyOfFiniteType G.X.hom →
      let σ := pullback.snd (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V))
      ∀ x : (Limits.pullback (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V))).left,
        relativeTopologicalKrullDimAt σ.left x = topologicalKrullDim (σ.left.fiber (σ.left x))

end Langlands.AlgebraicGeometry.AlgebraicSpace

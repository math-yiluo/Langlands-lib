import Langlands.GroupScheme.ConnectedKernelGeometryStatement
import Langlands.GroupScheme.KernelPair
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientReduction
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective

/-! # Geometric connectedness from the actual kernel -/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G Q : GroupScheme S}

/-- A scheme-surjective homomorphism with geometrically connected kernel is
geometrically connected. -/
theorem geometricallyConnected_of_geometricallyConnected_kernel (q : G ⟶ Q)
    [Surjective q.hom.hom.left] [GeometricallyConnected (kernel q).X.hom] :
    GeometricallyConnected q.hom.hom.left := by
  have hp : GeometricallyConnected (fst G.X (kernel q).X).left := by
    change GeometricallyConnected (pullback.fst G.X.hom (kernel q).X.hom)
    infer_instance
  have : MorphismProperty.DescendsAlong
      (@GeometricallyConnected : MorphismProperty Scheme.{u}) @Surjective :=
    GeometricallyConnected.descendsAlong_surjective
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @GeometricallyConnected) (Q := @Surjective)
    (KernelPair.isPullback_scheme q) (inferInstance : Surjective q.hom.hom.left) hp

/-- The exact arbitrary-base proposition target. -/
theorem connectedKernelHomGeometry : ConnectedKernelHomGeometryStatement.{u} := by
  intro S G Q q hq hk
  have := hq
  have := hk
  exact geometricallyConnected_of_geometricallyConnected_kernel q

namespace SubgroupPreimage

variable {H : GroupScheme S} (q : G ⟶ Q) (j : H ⟶ Q)

/-- Geometric connectedness of a homomorphism is preserved on actual subgroup preimages. -/
theorem geometricallyConnected_projection [GeometricallyConnected q.hom.hom.left] :
    GeometricallyConnected (projection q j).hom.hom.left :=
  MorphismProperty.of_isPullback (isPullback_scheme q j) inferInstance

/-- A smooth geometrically connected homomorphism has connected preimage of every
connected subgroup. -/
theorem connectedSpace [Smooth q.hom.hom.left]
    [GeometricallyConnected q.hom.hom.left] [ConnectedSpace H.X.left] :
    ConnectedSpace (groupScheme q j).X.left := by
  have : Smooth (projection q j).hom.hom.left := smooth_projection q j
  have : GeometricallyConnected (projection q j).hom.hom.left :=
    geometricallyConnected_projection q j
  exact GeometricallyConnected.connectedSpace (f := (projection q j).hom.hom.left)
    (projection q j).hom.hom.left.isOpenMap

/-- Connectedness of a smooth subgroup preimage follows from a geometrically connected
kernel and scheme surjectivity of the homomorphism. -/
theorem connectedSpace_of_geometricallyConnected_kernel [Smooth q.hom.hom.left]
    [Surjective q.hom.hom.left] [GeometricallyConnected (kernel q).X.hom]
    [ConnectedSpace H.X.left] : ConnectedSpace (groupScheme q j).X.left := by
  have := geometricallyConnected_of_geometricallyConnected_kernel q
  exact connectedSpace q j

end SubgroupPreimage

end Langlands.GroupScheme

import Langlands.GroupScheme.KernelPair
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Connected fibres and connected inverse images of fppf quotient maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.FppfQuotientGeometry

/-- A space embedding onto a connected subset is connected. -/
theorem connectedSpace_of_isEmbedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsEmbedding f) (h : _root_.IsConnected (Set.range f)) :
    ConnectedSpace X := by
  rw [connectedSpace_iff_univ]
  refine ⟨?_, ?_⟩
  · obtain ⟨_, x, rfl⟩ := h.nonempty
    exact ⟨x, trivial⟩
  · rw [← hf.isInducing.isPreconnected_image, Set.image_univ]
    exact h.isPreconnected

variable {S : Scheme.{u}} {G Q : GroupScheme S} (q : G ⟶ Q)

theorem geometricallyConnected_fst_kernel [GeometricallyConnected (kernel q).X.hom] :
    GeometricallyConnected (fst G.X (kernel q).X).left := by
  change GeometricallyConnected (pullback.fst G.X.hom (kernel q).X.hom)
  infer_instance

/-- With geometrically connected kernel, every fibre of a surjective homomorphism is
connected. -/
theorem isConnected_preimage_singleton [GeometricallyConnected (kernel q).X.hom]
    [Surjective q.hom.hom.left] (y : Q.X.left) :
    _root_.IsConnected (q.hom.hom.left ⁻¹' {y}) := by
  obtain ⟨x, rfl⟩ := q.hom.hom.left.surjective y
  have := geometricallyConnected_fst_kernel q
  have hF := (fst G.X (kernel q).X).left.isConnected_preimage_singleton x
  have himg := Scheme.image_preimage_eq_of_isPullback (KernelPair.isPullback_scheme q) {x}
  rw [Set.image_singleton] at himg
  rw [← himg]
  exact hF.image _ (KernelPair.action q).left.continuous.continuousOn

/-- A flat surjective homomorphism locally of finite presentation with geometrically connected
kernel has connected inverse images of closed connected subsets. -/
theorem isConnected_preimage [GeometricallyConnected (kernel q).X.hom] [Flat q.hom.hom.left]
    [Surjective q.hom.hom.left] [LocallyOfFinitePresentation q.hom.hom.left]
    {s : Set Q.X.left} (hs : _root_.IsConnected s) (hs' : IsClosed s) :
    _root_.IsConnected (q.hom.hom.left ⁻¹' s) :=
  Topology.IsCoinducing.isConnected_preimage_of_isClosed (isConnected_preimage_singleton q)
    (q.hom.hom.left.isOpenMap.isQuotientMap q.hom.hom.left.continuous
      q.hom.hom.left.surjective).isCoinducing hs' hs

end Langlands.GroupScheme.FppfQuotientGeometry

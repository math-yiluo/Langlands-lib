import Langlands.GroupScheme.SplitSolvableExtension
import Langlands.GroupScheme.SplitSolvableSmoothExtensionStatement
import Langlands.GroupScheme.ConnectedKernelGeometry
import Langlands.GroupScheme.GeometricConnectedness

/-! # Split-solvable series through a smooth connected kernel -/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

namespace RelativeRoot

variable {k : Type u} [Field k]
    {N G Q : GroupScheme (Spec (CommRingCat.of k))}
    {K : SubgroupFunctor G} {i : N ⟶ G} {q : G ⟶ Q}

/-- A finite-type connected representative of an fppf kernel makes the quotient
map geometrically connected. -/
theorem IsFppfQuotient.geometricallyConnected_of_connected_kernel
    (hq : IsFppfQuotient K q) (hi : K.IsRepresentedBy i)
    [LocallyOfFiniteType N.X.hom] [QuasiCompact N.X.hom]
    [ConnectedSpace N.X.left] : GeometricallyConnected q.hom.hom.left := by
  let e := hq.kernelIso hi
  let : IsIso e.hom.hom.hom := (Grp.forget _).map_isIso e.hom
  let : IsIso e.hom.hom.hom.left := (Over.forget _).map_isIso e.hom.hom.hom
  have hcomp : GeometricallyConnected
      (e.hom.hom.hom.left ≫ (kernel q).X.hom) := by
    rw [Over.w e.hom.hom.hom]
    exact N.geometricallyConnected_of_connected
  let : GeometricallyConnected (kernel q).X.hom :=
    (MorphismProperty.cancel_left_of_respectsIso
      (@GeometricallyConnected : MorphismProperty Scheme.{u})
      e.hom.hom.hom.left (kernel q).X.hom).mp hcomp
  let : Surjective q.hom.hom.left := hq.2.1
  exact geometricallyConnected_of_geometricallyConnected_kernel q

end RelativeRoot

namespace SplitSolvable

variable {k : Type u} [Field k]
    {N G Q : GroupScheme (Spec (CommRingCat.of k))}
    {i : N ⟶ G} {q : G ⟶ Q}

/-- Kernel and quotient series join without extra assumptions on the geometry
of the quotient map when the represented kernel is smooth connected affine. -/
theorem HasSeries.of_smooth_connected_extension {n m : ℕ}
    [Mono i.hom.hom] [IsAffineHom G.X.hom]
    [Smooth N.X.hom] [IsAffineHom N.X.hom] [ConnectedSpace N.X.left]
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hN : HasSeries n N) (hQ : HasSeries m Q) :
    HasSeries (n + m) G := by
  let hi : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let : IsSeparated Q.X.hom := fieldSeparated k Q
  have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hqc
  let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp q.hom.hom.left Q.X.hom
  let : Smooth q.hom.hom.left := hq.smooth_of_smooth_kernel hi inferInstance
  let : GeometricallyConnected q.hom.hom.left :=
    hq.geometricallyConnected_of_connected_kernel hi
  exact HasSeries.of_extension hq hN hQ

end SplitSolvable

/-- The smooth connected kernel extension proposition. -/
theorem smoothConnectedExtensionSeries : SmoothConnectedExtensionSeriesStatement.{u} := by
  intro k _ N G Q i q _ _ _ _ _ n m hq hN hQ
  exact SplitSolvable.HasSeries.of_smooth_connected_extension hq hN hQ

/-- An fppf extension of a split torus by a split-unipotent smooth connected
affine kernel has a represented Ga/Gm series. -/
theorem IsSplitSolvableGroupScheme.of_splitUnipotent_kernel_splitTorus_quotient
    {k : Type u} [Field k]
    {N G Q : GroupScheme (Spec (CommRingCat.of k))}
    (i : N ⟶ G) (q : G ⟶ Q)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth N.X.hom] [IsAffineHom N.X.hom] [ConnectedSpace N.X.left]
    (hi : IsClosedSubgroup i)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hG : IsSolvableGroupScheme G) (hN : RelativeRoot.IsSplitUnipotent N)
    (hQ : IsSplitTorus Q) : IsSplitSolvableGroupScheme G := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom.left := inferInstance
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨n, hn⟩ := hN
  obtain ⟨m, hm⟩ := hQ.isSplitSolvableGroupScheme.hasSeries
  exact ⟨inferInstance, inferInstance, inferInstance, hG,
    n + m, SplitSolvable.HasSeries.of_smooth_connected_extension hq
      (SplitSolvable.HasSeries.of_splitSeries hn) hm⟩

end Langlands.GroupScheme

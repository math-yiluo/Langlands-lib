import Langlands.GroupScheme.AffineOrbitImage
import Langlands.GroupScheme.OrbitMapFlatProof
import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
import Langlands.GroupScheme.HomogeneousQuotientComparison

/-! # Faithfully flat projections to actual closed affine orbits -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A surjective morphism between locally finite type schemes over an algebraically
closed field lifts every rational point on the same field. -/
theorem rationalPoint_lifts_of_surjective
    {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [Surjective f.left]
    (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Y) :
    ∃ x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X, x ≫ f = y := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  let z : Y.left := y.left (IsLocalRing.closedPoint k)
  have hzc : IsClosed ({z} : Set Y.left) :=
    ((pointEquivClosedPoint Y.hom) ⟨y.left, y.w⟩).property
  have hne : (f.left ⁻¹' ({z} : Set Y.left)).Nonempty := by
    obtain ⟨x, hx⟩ := f.left.surjective z
    exact ⟨x, hx⟩
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints hne
    (hzc.preimage f.left.continuous).isLocallyClosed
  let x' : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X :=
    Over.homMk (pointOfClosedPoint X.hom x hxc) (by simp)
  refine ⟨x', Over.OverMorphism.ext ?_⟩
  apply ext_of_apply_closedPoint_eq Y.hom (x' ≫ f).w y.w
  simpa [x', z] using hx

/-- A quasi-compact morphism with closed topological image is surjective onto
its actual schematic image. -/
theorem surjective_toImage_of_isClosed_range {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] (hclosed : IsClosed (Set.range f)) :
    Surjective f.toImage := by
  refine ⟨fun y => ?_⟩
  have hy : y.1 ∈ Set.range f := by
    have hy := y.2
    change y.1 ∈ (f.ker.support : Set Y) at hy
    rwa [Scheme.Hom.support_ker, hclosed.closure_eq] at hy
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

namespace SchemeAction

variable {S : Scheme.{u}} {G : GroupScheme S} {X : Over S}

/-- Factoring an orbit map through its closed image preserves all its test fibers. -/
theorem orbitImageProjection_comp_eq_iff
    (a : SchemeAction G X) (x : 𝟙_ (Over S) ⟶ X)
    {T : Over S} (g h : T ⟶ G.X) :
    g ≫ a.orbitImageProjection x = h ≫ a.orbitImageProjection x ↔
      g ≫ a.orbitMap x = h ≫ a.orbitMap x := by
  rw [← cancel_mono (a.orbitImageInclusion x)]
  simp only [Category.assoc, orbitImageProjection_comp]

end SchemeAction

namespace SchemeAction

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Flat G.X.hom] [IsReduced G.X.left]
    {X : Over (Spec (CommRingCat.of k))} [IsAffine X.left]
    [LocallyOfFiniteType X.hom]
    (a : SchemeAction G X) (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
    [QuasiCompact (a.orbitMap x).left]

/-- A closed orbit has a flat surjective quasi-compact projection to its actual
reduced schematic image. -/
theorem orbitImageProjection_faithfullyFlat
    (hclosed : IsClosed (Set.range (a.orbitMap x).left)) :
    Flat (a.orbitImageProjection x).left ∧
      Surjective (a.orbitImageProjection x).left ∧
      QuasiCompact (a.orbitImageProjection x).left := by
  have : IsReduced (a.orbitImage x).left := a.orbitImage_reduced x
  have : LocallyOfFiniteType (a.orbitImage x).hom := by
    change LocallyOfFiniteType ((a.orbitImageInclusion x).left ≫ X.hom)
    infer_instance
  have : Surjective (a.orbitImageProjection x).left :=
    surjective_toImage_of_isClosed_range (a.orbitMap x).left hclosed
  have htrans : ∀ y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ a.orbitImage x,
      ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X,
        (a.orbitImageAction x).act g (a.orbitImagePoint x) = y := by
    intro y
    obtain ⟨g, hg⟩ := rationalPoint_lifts_of_surjective (a.orbitImageProjection x) y
    refine ⟨g, ?_⟩
    rw [← a.orbitImageAction_orbitMap x] at hg
    simpa only [comp_orbitMap, toUnit_unit, Category.id_comp] using hg
  have h := orbitMapFaithfullyFlat k G (a.orbitImage x)
    (a.orbitImageAction x) (a.orbitImagePoint x) htrans
  change Flat ((a.orbitImageAction x).orbitMap (a.orbitImagePoint x)).left ∧
    Surjective ((a.orbitImageAction x).orbitMap (a.orbitImagePoint x)).left ∧
    QuasiCompact ((a.orbitImageAction x).orbitMap (a.orbitImagePoint x)).left at h
  rwa [a.orbitImageAction_orbitMap x] at h

end SchemeAction

namespace SchemeAction

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {X : Over (Spec (CommRingCat.of k))} [IsAffine X.left]
    [LocallyOfFiniteType X.hom]
    (a : SchemeAction G X) (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
    {H : GroupScheme (Spec (CommRingCat.of k))}
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : Smooth H.X.hom)
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ a.orbitMap x = h ≫ a.orbitMap x ↔
        g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)
    (hclosed : IsClosed (Set.range (a.orbitMap x).left))

/-- The actual closed affine orbit is the smooth homogeneous quotient by its
prescribed smooth closed stabilizer. -/
def quotientOfClosedAffineOrbit :
    HomogeneousQuotientFromEmbedding.HomogeneousQuotient i := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : QuasiCompact (a.orbitMap x).left := inferInstance
  let : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k G.X.left G.X.hom
  let : IsSeparated X.hom := inferInstance
  let D := HomogeneousQuotientFromEmbedding.quotientOfMapKernel i hi hH
    X (a.orbitMap x) hfib
  let : Smooth D.projection.left := D.smooth_projection
  let : Surjective D.projection.left := D.surjective_projection
  let : QuasiCompact D.projection.left := D.quasiCompact_projection
  have hff := a.orbitImageProjection_faithfullyFlat x hclosed
  let : Flat (a.orbitImageProjection x).left := hff.1
  let : Surjective (a.orbitImageProjection x).left := hff.2.1
  let : QuasiCompact (a.orbitImageProjection x).left := hff.2.2
  have hcomp : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ D.projection = h ≫ D.projection ↔
        g ≫ a.orbitImageProjection x = h ≫ a.orbitImageProjection x := by
    intro T g h
    exact (D.fibers T g h).trans
      ((a.orbitImageProjection_comp_eq_iff x g h).trans (hfib T g h)).symm
  let e := HomogeneousQuotientComparison.iso D.projection (a.orbitImageProjection x) hcomp
  have he : D.projection.left ≫ e.hom.left = (a.orbitImageProjection x).left :=
    congrArg Over.Hom.left (HomogeneousQuotientComparison.comp_iso_hom
      D.projection (a.orbitImageProjection x) hcomp)
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have hsm : Smooth (a.orbitImageProjection x).left := by
    rw [← he]
    infer_instance
  refine ⟨a.orbitImage x, a.orbitImageProjection x, ?_, ?_, ?_,
    hsm, hff.2.1, hff.2.2, ?_⟩
  · change IsSeparated ((a.orbitImageInclusion x).left ≫ X.hom)
    infer_instance
  · change LocallyOfFiniteType ((a.orbitImageInclusion x).left ≫ X.hom)
    infer_instance
  · infer_instance
  · intro T g h
    exact (a.orbitImageProjection_comp_eq_iff x g h).trans (hfib T g h)

/-- The quotient constructed from a closed affine orbit has affine underlying scheme. -/
theorem quotientOfClosedAffineOrbit_affine :
    IsAffine (a.quotientOfClosedAffineOrbit x i hi hH hfib hclosed).scheme.left := by
  change IsAffine (a.orbitImage x).left
  infer_instance

end SchemeAction

end Langlands.GroupScheme

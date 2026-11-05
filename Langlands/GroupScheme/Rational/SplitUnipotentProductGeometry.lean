import Langlands.GroupScheme.AffineClosedOrbit
import Langlands.GroupScheme.HomogeneousQuotientDimension
import Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimProof
import Langlands.AlgebraicGeometry.Picard.SectionCutDimensionProof
import Langlands.GroupScheme.RelativeIdentityComponent.OpenGeometry

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Order
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot.ProductGeometry

theorem surjective_of_closedImmersion_of_fullDimension
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [ConnectedSpace Y] [CompactSpace Y]
    {d : ℕ} (hd : SmoothOfRelativeDimension d p)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hX : (d : WithBot ℕ∞) ≤ topologicalKrullDim X) : Surjective i := by
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have : IrreducibleSpace Y :=
    Langlands.AlgebraicGeometry.irreducibleSpace_of_smooth_connected p
  have hY : topologicalKrullDim Y ≤ (d : WithBot ℕ∞) :=
    Langlands.AlgebraicGeometry.fieldSmoothTopologicalKrullDim k Y p d hd inferInstance
  have hr : Set.range i = Set.univ := by
    by_contra hne
    have hZ := Langlands.AlgebraicGeometry.Picard.topologicalKrullDim_add_one_le_of_isClosed
      (Set.range i) i.isClosedEmbedding.isClosed_range hne
    have heq : topologicalKrullDim X = topologicalKrullDim (Set.range i) :=
      i.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq _
    rw [← heq] at hZ
    have hadd : (d : WithBot ℕ∞) + 1 ≤ topologicalKrullDim X + 1 := by
      simpa only [add_comm] using add_le_add_right hX 1
    have hh : (d : WithBot ℕ∞) + 1 ≤ (d : WithBot ℕ∞) :=
      hadd.trans (hZ.trans hY)
    have hn : d + 1 ≤ d := by exact_mod_cast hh
    omega
  exact ⟨Set.range_eq_univ.mp hr⟩

section Orbit
variable {k : Type u} [Field k] [IsAlgClosed k]
    {G U E : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left]
    [IsAffineHom E.X.hom]
    (a : SchemeAction G U.X) (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X)
    (i : E ⟶ G) (hi : IsClosedSubgroup i) (hE : Smooth E.X.hom)
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ a.orbitMap x = h ≫ a.orbitMap x ↔
        g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)
    (hclosed : IsClosed (Set.range (a.orbitMap x).left))
    (hdim : Lie.dimension G = Lie.dimension E + Lie.dimension U)

include i hi hE hfib hclosed hdim in
theorem orbitImageInclusion_isIso_of_dimension :
    IsIso (a.orbitImageInclusion x).left := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  let Q := a.quotientOfClosedAffineOrbit x i hi hE hfib hclosed
  let : Smooth Q.projection.left := Q.smooth_projection
  let : Surjective Q.projection.left := Q.surjective_projection
  let : Mono i.hom.hom := by
    let : IsClosedImmersion i.hom.hom.left := hi
    exact Over.mono_of_mono_left _
  let D := HomogeneousQuotient.dimensionData i Q.projection Q.fibers
  have hdQ : D.quotientDimension = Lie.dimension U := by
    have h := D.lie_dimension_eq
    omega
  obtain ⟨d, hd⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    U.X.left (Spec (CommRingCat.of k)) U.X.hom inferInstance inferInstance
  have hUd : Lie.dimension U = d :=
    Lie.dimension_eq_of_smoothOfRelativeDimension U hd
  have hbound : (d : WithBot ℕ∞) ≤ topologicalKrullDim (a.orbitImage x).left := by
    rw [← hUd, ← hdQ]
    exact D.quotientDimension_cast_le
  have : Surjective (a.orbitImageInclusion x).left :=
    surjective_of_closedImmersion_of_fullDimension U.X.hom hd
      (a.orbitImageInclusion x).left hbound
  have : IsReduced U.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k U.X.left U.X.hom
  exact isIso_of_isClosedImmersion_of_surjective _

include i hi hE hfib hclosed hdim in
/-- The schematic orbit image equals the ambient smooth connected group. -/
def orbitImageIsoOfDimension : (a.orbitImage x).left ≅ U.X.left := by
  let : IsIso (a.orbitImageInclusion x).left :=
    orbitImageInclusion_isIso_of_dimension a x i hi hE hfib hclosed hdim
  exact asIso (a.orbitImageInclusion x).left

include i hi hE hfib hclosed hdim in
/-- A closed orbit with the full expected dimension has a smooth surjective
actual orbit map. -/
theorem orbitMap_smooth_surjective_of_dimension :
    Smooth (a.orbitMap x).left ∧ Surjective (a.orbitMap x).left := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  let Q := a.quotientOfClosedAffineOrbit x i hi hE hfib hclosed
  have : Smooth (a.orbitImageProjection x).left := Q.smooth_projection
  have : Surjective (a.orbitImageProjection x).left := Q.surjective_projection
  have : IsIso (a.orbitImageInclusion x).left :=
    orbitImageInclusion_isIso_of_dimension a x i hi hE hfib hclosed hdim
  have he := congrArg Over.Hom.left (a.orbitImageProjection_comp x)
  change (a.orbitImageProjection x).left ≫ (a.orbitImageInclusion x).left =
    (a.orbitMap x).left at he
  constructor <;> rw [← he] <;> infer_instance

end Orbit
end Langlands.GroupScheme.RelativeRoot.ProductGeometry

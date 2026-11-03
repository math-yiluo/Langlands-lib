import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.GroupScheme.Dynamic.SmoothProof

/-! # Smooth closed subgroups detected on algebraically closed field points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G H K : GroupScheme (Spec (CommRingCat.of k))}

namespace SubgroupFunctor

variable {F F' : SubgroupFunctor G} {i : H ⟶ G} {j : K ⟶ G}

/-- Smooth-source containment in a closed represented subgroup is detected on
algebraically closed field points. -/
theorem IsRepresentedBy.le_iff_algClosed_points_of_smooth [Smooth H.X.hom]
    (hi : F.IsRepresentedBy i) (hj : F'.IsRepresentedBy j) (hjc : IsClosedSubgroup j) :
    F ≤ F' ↔
      F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≤
        F'.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  have : IsReduced H.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k H.X.left H.X.hom
  rw [← hi.2, ← hj.2]
  exact range_le_iff_algClosed_points hjc

/-- Two smooth closed represented subgroup functors agree on every test scheme
exactly when their algebraically closed field points agree. -/
theorem IsRepresentedBy.eq_iff_algClosed_points_of_smooth
    [Smooth H.X.hom] [Smooth K.X.hom]
    (hi : F.IsRepresentedBy i) (hj : F'.IsRepresentedBy j)
    (hic : IsClosedSubgroup i) (hjc : IsClosedSubgroup j) :
    F = F' ↔
      F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =
        F'.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  constructor
  · rintro rfl
    rfl
  · intro h
    exact le_antisymm ((hi.le_iff_algClosed_points_of_smooth hj hjc).mpr h.le)
      ((hj.le_iff_algClosed_points_of_smooth hi hic).mpr h.ge)

/-- Taking rational points is an order embedding on smooth closed represented
subgroup functors over an algebraically closed field. -/
def smoothClosedSubgroupPointsOrderEmbedding :
    {F : SubgroupFunctor G //
      ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
        F.IsRepresentedBy i ∧ IsClosedSubgroup i ∧ Smooth H.X.hom} ↪o
      Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) where
  toFun F := F.val.carrier _
  inj' := by
    intro F F' h
    obtain ⟨H, i, hi, hic, hs⟩ := F.property
    obtain ⟨K, j, hj, hjc, hs'⟩ := F'.property
    have : Smooth H.X.hom := hs
    have : Smooth K.X.hom := hs'
    exact Subtype.ext ((hi.eq_iff_algClosed_points_of_smooth hj hic hjc).mpr h)
  map_rel_iff' := by
    intro F F'
    obtain ⟨H, i, hi, _, hs⟩ := F.property
    obtain ⟨K, j, hj, hjc, _⟩ := F'.property
    have : Smooth H.X.hom := hs
    exact (hi.le_iff_algClosed_points_of_smooth hj hjc).symm

end SubgroupFunctor

namespace Dynamic

variable [IsAffineHom G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) {i : H ⟶ G}

/-- Containment of a smooth represented subgroup in the actual dynamic parabolic
is detected on algebraically closed field points. -/
theorem le_parabolic_iff_algClosed_points [Smooth H.X.hom]
    {F : SubgroupFunctor G} (hi : F.IsRepresentedBy i) :
    F ≤ parabolic χ ↔
      F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≤
        (parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact hi.le_iff_algClosed_points_of_smooth
    (Affine.isRepresentedBy_parabolicHom χ) (Affine.isClosedSubgroup_parabolicHom χ)

/-- Containment of the actual dynamic parabolic in a closed represented subgroup
is detected on algebraically closed field points. -/
theorem parabolic_le_iff_algClosed_points [Smooth G.X.hom]
    {F : SubgroupFunctor G} (hi : F.IsRepresentedBy i) (hic : IsClosedSubgroup i) :
    parabolic χ ≤ F ↔
      (parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≤
        F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hp := Affine.isRepresentedBy_parabolicHom χ
  have : Smooth (Affine.parabolicScheme χ).X.hom :=
    (dynamicSmooth k G χ (Affine.parabolicScheme χ) (Affine.parabolicHom χ)).1 hp
  exact hp.le_iff_algClosed_points_of_smooth hi hic

/-- Equality with the actual dynamic parabolic on every test scheme is equivalent
to equality on algebraically closed field points for a smooth closed subgroup. -/
theorem range_eq_parabolic_iff_algClosed_points [Smooth G.X.hom] [Smooth H.X.hom]
    (hic : IsClosedSubgroup i) :
    SubgroupFunctor.range i = parabolic χ ↔
      (SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =
        (parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  have : IsClosedImmersion i.hom.hom.left := hic
  have hi : (SubgroupFunctor.range i).IsRepresentedBy i :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  constructor
  · rintro h
    rw [h]
  · intro h
    exact le_antisymm ((le_parabolic_iff_algClosed_points χ hi).mpr h.le)
      ((parabolic_le_iff_algClosed_points χ hi hic).mpr h.ge)

end Dynamic

end Langlands.GroupScheme

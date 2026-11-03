import Langlands.GroupScheme.Rational.TorusCentralizerImage
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Comparing closed schematically dominant group factorizations -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}}

/-- Flat base change preserves a quasi-compact schematically dominant group homomorphism. -/
theorem isSchemeTheoreticallyDominant_baseChange (b : S' ⟶ S) [Flat b]
    {G H : GroupScheme S} (f : G ⟶ H)
    [QuasiCompact f.hom.hom.left] [IsSchemeTheoreticallyDominant f.hom.hom.left] :
    IsSchemeTheoreticallyDominant ((GroupScheme.baseChange b).map f).hom.hom.left := by
  have houter : IsPullback
      (((GroupScheme.baseChange b).map f).hom.hom.left ≫ pullback.snd H.X.hom b)
      (pullback.fst G.X.hom b) b (f.hom.hom.left ≫ H.X.hom) := by
    change IsPullback (((Over.pullback b).map f.hom.hom).left ≫ _) _ _ _
    simpa only [Over.w f.hom.hom, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback G.X.hom b).flip
  have hp := houter.of_right
    (show ((GroupScheme.baseChange b).map f).hom.hom.left ≫ pullback.fst H.X.hom b =
        pullback.fst G.X.hom b ≫ f.hom.hom.left by
      change ((Over.pullback b).map f.hom.hom).left ≫ _ = _
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback H.X.hom b).flip
  have : Flat (pullback.fst H.X.hom b) :=
    MorphismProperty.pullback_fst H.X.hom b ‹Flat b›
  exact IsSchemeTheoreticallyDominant.of_isPullback hp.flip

namespace SchematicImage

variable {G A B H : GroupScheme S}
  (p : G ⟶ A) (q : G ⟶ B) (i : A ⟶ H) (j : B ⟶ H)
  [IsSchemeTheoreticallyDominant p.hom.hom.left]
  [IsSchemeTheoreticallyDominant q.hom.hom.left]
  (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
  (h : p ≫ i = q ≫ j)

include p q hi hj h

/-- Two closed dominant factorizations of the same homomorphism have the same all-test range. -/
theorem range_eq_of_dominantFactorizations :
    SubgroupFunctor.range i = SubgroupFunctor.range j := by
  apply le_antisymm
  · apply (SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant p i j hj).mp
    rw [h]
    intro T x hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨t ≫ q.hom.hom, Category.assoc _ _ _⟩
  · apply (SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant q j i hi).mp
    rw [← h]
    intro T x hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨t ≫ p.hom.hom, Category.assoc _ _ _⟩

/-- The actual comparison isomorphism between two closed dominant factorizations. -/
def isoOfDominantFactorizations : A ≅ B := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion j.hom.hom.left := hj
  let ri : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨Over.mono_of_mono_left _, rfl⟩
  let rj : (SubgroupFunctor.range i).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, (range_eq_of_dominantFactorizations p q i j hi hj h).symm⟩
  exact ri.isoOfIsRepresentedBy rj

/-- The comparison preserves the specified inclusions into the original target. -/
theorem isoOfDominantFactorizations_hom_comp :
    (isoOfDominantFactorizations p q i j hi hj h).hom ≫ j = i := by
  unfold isoOfDominantFactorizations
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end SchematicImage

end Langlands.GroupScheme

import Langlands.AlgebraicGeometry.Picard.TwoAxisRigidification

/-! # Self-products of specified cartesian squares -/

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

variable {S T X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ T)
  (a : X ⟶ Y) (b : S ⟶ T) (w : a ≫ q = p ≫ b)

/-- The map on actual self-products induced by a specified commutative square. -/
def cartesianSelfProductMap : pullback p p ⟶ pullback q q :=
  pullback.map p p q q a a b w.symm w.symm

@[reassoc (attr := simp)]
theorem cartesianSelfProductMap_fst :
    cartesianSelfProductMap p q a b w ≫ pullback.fst q q =
      pullback.fst p p ≫ a := by
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cartesianSelfProductMap_snd :
    cartesianSelfProductMap p q a b w ≫ pullback.snd q q =
      pullback.snd p p ≫ a := by
  exact pullback.lift_snd _ _ _

/-- A cartesian square induces a cartesian square on the actual self-products. -/
theorem cartesianSelfProductMap_isPullback (h : IsPullback a p q b) :
    IsPullback (cartesianSelfProductMap p q a b w)
      (pullback.fst p p ≫ p) (pullback.fst q q ≫ q) b := by
  have hw : cartesianSelfProductMap p q a b w ≫ (pullback.fst q q ≫ q) =
      (pullback.fst p p ≫ p) ≫ b := by
    rw [← Category.assoc, cartesianSelfProductMap_fst, Category.assoc, w,
      ← Category.assoc]
  let l (s : PullbackCone (pullback.fst q q ≫ q) b) : s.pt ⟶ pullback p p :=
    pullback.lift
      (h.lift (s.fst ≫ pullback.fst q q) s.snd (by
        simpa only [Category.assoc] using s.condition))
      (h.lift (s.fst ≫ pullback.snd q q) s.snd (by
        rw [Category.assoc, ← pullback.condition]
        exact s.condition))
      (by simp only [IsPullback.lift_snd])
  have hl₁ (s : PullbackCone (pullback.fst q q ≫ q) b) :
      l s ≫ cartesianSelfProductMap p q a b w = s.fst := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, cartesianSelfProductMap_fst,
        cartesianSelfProductMap_snd, l, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc, IsPullback.lift_fst]
  have hl₂ (s : PullbackCone (pullback.fst q q ≫ q) b) :
      l s ≫ (pullback.fst p p ≫ p) = s.snd := by
    simp only [l, pullback.lift_fst_assoc, IsPullback.lift_snd]
  refine IsPullback.of_isLimit' ⟨hw⟩
    (PullbackCone.IsLimit.mk _ l hl₁ hl₂ ?_)
  intro s j hj₁ hj₂
  apply pullback.hom_ext
  · apply h.hom_ext
    · rw [Category.assoc, ← cartesianSelfProductMap_fst p q a b w,
        ← Category.assoc, hj₁]
      simp only [l, Category.assoc, pullback.lift_fst_assoc, IsPullback.lift_fst]
    · rw [Category.assoc, hj₂]
      simp only [l, Category.assoc, pullback.lift_fst_assoc, IsPullback.lift_snd]
  · apply h.hom_ext
    · rw [Category.assoc, ← cartesianSelfProductMap_snd p q a b w,
        ← Category.assoc, hj₁]
      simp only [l, Category.assoc, pullback.lift_snd_assoc, IsPullback.lift_fst]
    · rw [Category.assoc, ← pullback.condition, hj₂]
      simp only [l, Category.assoc, pullback.lift_snd_assoc, IsPullback.lift_snd]

end Langlands.AlgebraicGeometry.Picard

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S T : Scheme.{u}} (A : AbelianScheme S) (B : AbelianScheme T)
  (a : A.X.left ⟶ B.X.left) (b : S ⟶ T) (w : a ≫ B.X.hom = A.X.hom ≫ b)

/-- The self-product comparison for a specified morphism of abelian-scheme carriers. -/
abbrev cartesianMumfordProductMap :
    (mumfordProduct A).left ⟶ (mumfordProduct B).left :=
  cartesianSelfProductMap A.X.hom B.X.hom a b w

/-- The first unit axes commute when the carrier map respects the units. -/
theorem mumfordSection_cartesianMumfordProductMap
    (hu : unitSection A ≫ a = b ≫ unitSection B) :
    mumfordSection A ≫ cartesianMumfordProductMap A B a b w =
      a ≫ mumfordSection B := by
  apply pullback.hom_ext
  · simp only [cartesianMumfordProductMap, Category.assoc,
      cartesianSelfProductMap_fst, mumfordSection, relativeSection,
      pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp,
      Category.comp_id]
  · simp only [cartesianMumfordProductMap, Category.assoc,
      cartesianSelfProductMap_snd, mumfordSection, relativeSection,
      pullback.lift_snd, pullback.lift_snd_assoc]
    rw [hu, ← Category.assoc, ← w, Category.assoc]

/-- The second unit axes commute under the same unit compatibility. -/
theorem twoAxisSecond_cartesianMumfordProductMap
    (hu : unitSection A ≫ a = b ≫ unitSection B) :
    twoAxisSecond A ≫ cartesianMumfordProductMap A B a b w =
      a ≫ twoAxisSecond B := by
  apply pullback.hom_ext
  · simp only [cartesianMumfordProductMap, Category.assoc,
      cartesianSelfProductMap_fst, twoAxisSecond, pullback.lift_fst,
      pullback.lift_fst_assoc]
    rw [hu, ← Category.assoc, ← w, Category.assoc]
  · simp only [cartesianMumfordProductMap, Category.assoc,
      cartesianSelfProductMap_snd, twoAxisSecond, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.id_comp, Category.comp_id]

end Langlands.AbelianScheme

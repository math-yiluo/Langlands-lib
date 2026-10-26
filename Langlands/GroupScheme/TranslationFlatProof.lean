import Langlands.GroupScheme.TranslationFlatStatement
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.GroupScheme

universe u

private lemma translation_naturality {S : Scheme.{u}} {G H : Grp (Over S)}
    (f : G ⟶ H) (a : 𝟙_ (Over S) ⟶ G.X) :
    (GrpObj.mulRight a).hom ≫ f.hom.hom =
      f.hom.hom ≫ (GrpObj.mulRight (a ≫ f.hom.hom)).hom := by
  change ((𝟙 G.X) * (toUnit G.X ≫ a)) ≫ f.hom.hom =
    f.hom.hom ≫ ((𝟙 H.X) * (toUnit H.X ≫ a ≫ f.hom.hom))
  rw [mul_comp, comp_mul]
  simp

private lemma rationalPoint_surjective {K : Type u} [Field K] [IsAlgClosed K]
    {G : Grp (Over (Spec (CommRingCat.of K)))} (f : G ⟶ G)
    [LocallyOfFiniteType G.X.hom] [Surjective f.hom.hom.left] :
    Function.Surjective (fun a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X =>
      a ≫ f.hom.hom) := by
  have : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  intro b
  let z : G.X.left := b.left (IsLocalRing.closedPoint K)
  have hzc : IsClosed ({z} : Set G.X.left) :=
    ((pointEquivClosedPoint G.X.hom) ⟨b.left, b.w⟩).property
  have hne : (f.hom.hom.left ⁻¹' ({z} : Set G.X.left)).Nonempty := by
    obtain ⟨a, ha⟩ := f.hom.hom.left.surjective z
    exact ⟨a, ha⟩
  obtain ⟨a, ha, hac⟩ := nonempty_inter_closedPoints hne
    (hzc.preimage f.hom.hom.left.continuous).isLocallyClosed
  let a' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X :=
    Over.homMk (pointOfClosedPoint G.X.hom a hac) (by simp)
  refine ⟨a', Over.OverMorphism.ext ?_⟩
  apply ext_of_apply_closedPoint_eq G.X.hom (a' ≫ f.hom.hom).w b.w
  simpa [a', z] using ha

private lemma flat_restrict_translation {K : Type u} [Field K]
    {G : Grp (Over (Spec (CommRingCat.of K)))} (f : G ⟶ G)
    (a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X)
    (U : G.X.left.Opens) [Flat (f.hom.hom.left ∣_ U)] :
    Flat (f.hom.hom.left ∣_ (GrpObj.mulRight (a ≫ f.hom.hom)).hom.left ⁻¹ᵁ U) := by
  have hn : (GrpObj.mulRight a).hom.left ≫ f.hom.hom.left =
      f.hom.hom.left ≫ (GrpObj.mulRight (a ≫ f.hom.hom)).hom.left :=
    congrArg (fun h => h.left) (translation_naturality f a)
  have h : Flat (((GrpObj.mulRight a).hom.left ≫ f.hom.hom.left) ∣_ U) := by
    rw [morphismRestrict_comp]
    infer_instance
  rw [hn, morphismRestrict_comp,
    MorphismProperty.cancel_right_of_respectsIso @Flat] at h
  exact h

/-- Flatness on a nonempty target open propagates by group translations. -/
theorem translationFlat : TranslationFlatStatement.{u} := by
  intro K _ _ G f hft hfin hsurj hU
  have := hft
  have := hfin
  have := hsurj
  have : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  obtain ⟨U, hUne, hUflat⟩ := hU
  have := hUflat
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hUne U.isOpen.isLocallyClosed
  let y' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X :=
    Over.homMk (pointOfClosedPoint G.X.hom y hyc) (by simp)
  let V (a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X) : G.X.left.Opens :=
    (GrpObj.mulRight (a ≫ f.hom.hom)).hom.left ⁻¹ᵁ U
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Flat) V
  · rw [← Opens.coe_eq_univ, ← not_ne_iff, ← Set.nonempty_compl]
    intro hne
    obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints hne
      (iSup V).isOpen.isClosed_compl.isLocallyClosed
    let x' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X :=
      Over.homMk (pointOfClosedPoint G.X.hom x hxc) (by simp)
    obtain ⟨a, ha⟩ := rationalPoint_surjective f (x'⁻¹ * y')
    change a ≫ f.hom.hom = x'⁻¹ * y' at ha
    have hxy : x' ≫ (GrpObj.mulRight (a ≫ f.hom.hom)).hom = y' := by
      rw [ha]
      change x' ≫ ((𝟙 G.X) * (toUnit G.X ≫ (x'⁻¹ * y'))) = y'
      rw [comp_mul]
      simp
    have hxy' : (GrpObj.mulRight (a ≫ f.hom.hom)).hom.left x = y := by
      have h := congr(($hxy).left (IsLocalRing.closedPoint K))
      change (GrpObj.mulRight (a ≫ f.hom.hom)).hom.left
        (pointOfClosedPoint G.X.hom x hxc (IsLocalRing.closedPoint K)) =
        pointOfClosedPoint G.X.hom y hyc (IsLocalRing.closedPoint K) at h
      simpa only [pointOfClosedPoint_apply] using h
    apply hx
    apply Opens.mem_iSup.mpr
    refine ⟨a, ?_⟩
    change (GrpObj.mulRight (a ≫ f.hom.hom)).hom.left x ∈ U
    rwa [hxy']
  · intro a
    exact flat_restrict_translation f a U

end Langlands.GroupScheme

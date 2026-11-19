import Langlands.AlgebraicGeometry.AffineLiftingSmooth
import Langlands.AlgebraicGeometry.SmoothLifting.SquareZero

/-! # The square-zero lifting criterion for smoothness -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry

/-- Every lifting problem on an affine square-zero quotient has a solution over the target. -/
def HasAffineSquareZeroLifting {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (C : CommRingCat.{u}) (I : Ideal C), I ^ 2 = ⊥ →
    ∀ (x₀ : Spec (CommRingCat.of (C ⧸ I)) ⟶ X) (y : Spec C ⟶ Y),
      x₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y →
      ∃ x : Spec C ⟶ X, x ≫ f = y ∧
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ x = x₀

namespace HasAffineSquareZeroLifting

private theorem sqZero_of_pow_eq_bot {C : Type u} [CommRing C] {I : Ideal C}
    (hI : I ^ 2 = ⊥) : SmoothLifting.SqZero I := by
  intro a ha b hb
  have h := Ideal.mul_mem_mul ha hb
  rwa [← pow_two, hI, Ideal.mem_bot] at h

theorem of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] :
    HasAffineSquareZeroLifting f := by
  intro C I hI x₀ y h
  let q := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have hq : SmoothLifting.SqZero (RingHom.ker q.hom) := by
    change SmoothLifting.SqZero (RingHom.ker (Ideal.Quotient.mk I))
    rw [Ideal.mk_ker]
    exact sqZero_of_pow_eq_bot hI
  obtain ⟨x, hx₀, hx⟩ :=
    SmoothLifting.exists_lift_sqZero q Ideal.Quotient.mk_surjective hq x₀ y h
  exact ⟨x, hx, hx₀⟩

theorem pullback_snd {X Y Z : Scheme.{u}} {f : X ⟶ Z} (hf : HasAffineSquareZeroLifting f)
    (g : Y ⟶ Z) : HasAffineSquareZeroLifting (Limits.pullback.snd f g) := by
  intro C I hI x₀ y h
  obtain ⟨x, hx, hx₀⟩ := hf C I hI (x₀ ≫ pullback.fst f g) (y ≫ g) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, h, Category.assoc])
  refine ⟨pullback.lift x y hx, pullback.lift_snd _ _ _, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hx₀]
  · rw [Category.assoc, pullback.lift_snd]
    exact h.symm

theorem of_openImmersion {X' X Y : Scheme.{u}} {f : X ⟶ Y} (hf : HasAffineSquareZeroLifting f)
    (j : X' ⟶ X) [IsOpenImmersion j] : HasAffineSquareZeroLifting (j ≫ f) := by
  intro C I hI x₀ y h
  let q := CommRingCat.ofHom (Ideal.Quotient.mk I)
  obtain ⟨x, hx, hx₀⟩ := hf C I hI (x₀ ≫ j) y (by simpa only [Category.assoc] using h)
  have hker : RingHom.ker q.hom ≤ nilradical C := by
    change RingHom.ker (Ideal.Quotient.mk I) ≤ nilradical C
    rw [Ideal.mk_ker]
    exact (sqZero_of_pow_eq_bot hI).le_nilradical
  have hs := SmoothLifting.specMap_surjective q Ideal.Quotient.mk_surjective hker
  have hrange : Set.range x ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := hs a
    exact ⟨x₀ b, by
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun t : _ ⟶ X => t b) hx₀.symm⟩
  refine ⟨IsOpenImmersion.lift j x hrange, ?_, ?_⟩
  · rw [← Category.assoc, IsOpenImmersion.lift_fac, hx]
  · rw [← cancel_mono j, Category.assoc, IsOpenImmersion.lift_fac]
    exact hx₀

set_option backward.isDefEq.respectTransparency false in
private theorem smooth_affine {R : CommRingCat.{u}} {X : Scheme.{u}} [IsAffine X]
    {f : X ⟶ Spec R} [LocallyOfFinitePresentation f] (hf : HasAffineSquareZeroLifting f) :
    Smooth f := by
  let U : Over (Spec R) := Over.mk f
  let V : Over (Spec R) := Over.mk (𝟙 (Spec R))
  let g : U ⟶ V := Over.homMk f
  let : IsAffine U.left := inferInstanceAs (IsAffine X)
  let : IsAffine V.left := inferInstanceAs (IsAffine (Spec R))
  let : LocallyOfFinitePresentation g.left := inferInstanceAs (LocallyOfFinitePresentation f)
  refine AffineLifting.smooth_of_lifting g (fun C I hI y x₀ h => ?_)
  have h₀ := congrArg (fun t => t.left) h
  change x₀.left ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y.left at h₀
  obtain ⟨x, hx, hx₀⟩ := hf (CommRingCat.of C) I hI x₀.left y.left h₀
  have hy : y.left = ((algSpec R).obj (op C)).hom :=
    (Category.comp_id y.left).symm.trans (Over.w y)
  refine ⟨Over.homMk x (hx.trans hy), ?_, ?_⟩
  · exact Over.OverMorphism.ext hx
  · exact Over.OverMorphism.ext hx₀

private theorem smooth_overSpec {R : CommRingCat.{u}} {X : Scheme.{u}} {f : X ⟶ Spec R}
    [LocallyOfFinitePresentation f] (hf : HasAffineSquareZeroLifting f) : Smooth f := by
  let 𝒰 := X.affineOpenCover
  have : IsZariskiLocalAtSource @Smooth.{u} := HasRingHomProperty.instIsZariskiLocalAtSource
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth.{u}) 𝒰.openCover
  intro k
  let j := 𝒰.f k
  change Smooth (j ≫ f)
  let : IsOpenImmersion j := 𝒰.openCover.map_prop k
  let : LocallyOfFinitePresentation (j ≫ f) := locallyOfFinitePresentation_comp j f
  let : IsAffine (Spec (𝒰.X k)) := inferInstance
  exact smooth_affine (hf.of_openImmersion j)

/-- Affine square-zero lifting implies smoothness for a locally finitely presented morphism. -/
theorem smooth {X Y : Scheme.{u}} {f : X ⟶ Y} [LocallyOfFinitePresentation f]
    (hf : HasAffineSquareZeroLifting f) : Smooth f := by
  let 𝒰 := Y.affineOpenCover
  have : IsZariskiLocalAtTarget @Smooth.{u} := HasRingHomProperty.instIsZariskiLocalAtTarget _
  refine IsZariskiLocalAtTarget.of_openCover (P := @Smooth.{u}) 𝒰.openCover fun k => ?_
  change Smooth (Limits.pullback.snd f (𝒰.f k))
  exact smooth_overSpec (hf.pullback_snd (𝒰.f k))

end HasAffineSquareZeroLifting

end Langlands.AlgebraicGeometry

import Langlands.AlgebraicGeometry.Picard.PointFiberArtinianLifting
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberTestChange

/-! # Reductions of actual Picard chart versality to affine charts and identity tests -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianChartTestReduction

open Langlands.AlgebraicGeometry.Deformation
open Langlands.CategoryTheory
open ArtinianChartLifting ArtinianChartVersality

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  {U : Over (Spec (CommRingCat.of R))} (L : LineBundle ((relativeSpace f).obj U))

/-- Lifting at a specified residue map on the identity test of the source test ring. The
test bundle is an arbitrary actual line bundle on the relative space of the source. -/
def HasBaseLiftingForAt {K : Type u} [Field K] [Algebra R K]
    (p : ArtinianTest.residueBase R K ⟶ U) {A B : ArtinianTest R K} (q : A ⟶ B) : Prop :=
  ∀ (N : LineBundle ((relativeSpace f).obj (ArtinianTest.base A)))
    (y : FiberPoints f L N (Over.mk (ArtinianTest.baseMap q))),
    ArtinianTest.reduction B ≫ y.1 = p →
      ∃ x : FiberPoints f L N (Over.mk (𝟙 (ArtinianTest.base A))),
        restrict f L q N (Category.comp_id _) x = y

/-- Lifting on arbitrary slice tests is equivalent to lifting on the identity test of the
source, with an arbitrary actual line bundle there. -/
theorem hasLiftingForAt_iff_base {K : Type u} [Field K] [Algebra R K]
    (p : ArtinianTest.residueBase R K ⟶ U) {A B : ArtinianTest R K} (q : A ⟶ B) :
    HasLiftingForAt f L p q ↔ HasBaseLiftingForAt f L p q := by
  constructor
  · intro h N y hy
    exact h (ArtinianTest.base A) N (𝟙 _) (ArtinianTest.baseMap q) (Category.comp_id _) y hy
  · intro h T M a b w y hy
    subst w
    let F := relative f
    let N : LineBundle ((relativeSpace f).obj (ArtinianTest.base A)) :=
      ((F.map a.op.toLoc).toFunctor.obj (Core.mk M)).of
    let e := PseudofunctorPointFiberTestChange.basePointsEquiv F (Core.mk L) (Core.mk M) a
    let y' : FiberPoints f L N (Over.mk (ArtinianTest.baseMap q)) :=
      (e (Over.mk (ArtinianTest.baseMap q))).symm y
    have hy' : ArtinianTest.reduction B ≫ y'.1 = p := hy
    obtain ⟨x', hx'⟩ := h N y' hy'
    let x'' := e (Over.mk (𝟙 (ArtinianTest.base A))) x'
    let r : Over.mk a ⟶ (Over.map a).obj (Over.mk (𝟙 (ArtinianTest.base A))) :=
      Over.homMk (𝟙 _) (by simp)
    refine ⟨PseudofunctorPointFiber.restrict F (Core.mk L) (Core.mk M) r x'', ?_⟩
    change PseudofunctorPointFiber.restrict F (Core.mk L) (Core.mk M) (testArrow q rfl)
        (PseudofunctorPointFiber.restrict F (Core.mk L) (Core.mk M) r x'') = y
    rw [← PseudofunctorPointFiber.restrict_comp]
    have hq : testArrow q rfl ≫ r =
        (Over.map a).map (testArrow q (Category.comp_id (ArtinianTest.baseMap q))) := by
      apply Over.OverMorphism.ext
      simp [r, testArrow]
    rw [hq, ← PseudofunctorPointFiberTestChange.basePointsEquiv_restrict]
    change e (Over.mk (ArtinianTest.baseMap q)) (restrict f L q N (Category.comp_id _) x') = y
    rw [hx']
    exact (e (Over.mk (ArtinianTest.baseMap q))).apply_symm_apply y

/-- Versality of the restriction of a family along an open immersion implies versality of
the family at the composite point. This is the converse of
`PointFiberArtinianLifting.isFormallyVersalAt_restrictBundle`. -/
theorem isFormallyVersalAt_of_restrictBundle {V : Over (Spec (CommRingCat.of R))} (ι : V ⟶ U)
    [IsOpenImmersion ι.left] {K : Type u} [Field K] [Algebra R K]
    (p : ArtinianTest.residueBase R K ⟶ V)
    (h : IsFormallyVersalAt f (restrictBundle f L ι) p) :
    IsFormallyVersalAt f L (p ≫ ι) := by
  have : Mono ι := Over.mono_of_mono_left ι
  intro A B q hq T M a b w y hy
  rcases y with ⟨b', d⟩
  have hrange : Set.range b'.left ⊆ Set.range ι.left := by
    rintro _ ⟨z, rfl⟩
    have : Unique (PrimeSpectrum B.algebra) := PrimeSpectrum.unique_of_ringKrullDimLE_zero
    let c : (ArtinianTest.residueBase R K).left := (default : PrimeSpectrum K)
    have hz : z = (ArtinianTest.reduction B).left c :=
      Subsingleton.elim (α := PrimeSpectrum B.algebra) _ _
    have hc := congrArg (fun φ : ArtinianTest.residueBase R K ⟶ U ↦ φ.left c) hy
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at hc
    exact ⟨p.left c, by rw [hz]; exact hc.symm⟩
  obtain ⟨g, hg⟩ : ∃ g : ArtinianTest.base B ⟶ V, g ≫ ι = b' :=
    ⟨Over.homMk (IsOpenImmersion.lift ι.left b'.left hrange) (by
      rw [← Over.w ι, ← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w b'), by
      ext
      exact IsOpenImmersion.lift_fac _ _ _⟩
  subst hg
  let y' : FiberPoints f (restrictBundle f L ι) M (Over.mk b) :=
    ⟨g, (PseudofunctorPointFiberAtlasRestriction.atlasComparison (relative f) ι (Core.mk L)
      g).symm ≪≫ d⟩
  have hy' : ArtinianTest.reduction B ≫ y'.1 = p := by
    apply (cancel_mono ι).mp
    simpa only [Category.assoc] using hy
  obtain ⟨x', hx'⟩ := h q hq T M a b w y' hy'
  refine ⟨PseudofunctorPointFiberAtlasRestriction.mapPoints (relative f) ι (Core.mk L)
    (Core.mk M) (Over.mk a) x', ?_⟩
  change PseudofunctorPointFiber.restrict (relative f) (Core.mk L) (Core.mk M)
      (testArrow q w) (PseudofunctorPointFiberAtlasRestriction.mapPoints (relative f) ι
        (Core.mk L) (Core.mk M) (Over.mk a) x') = _
  rw [← PseudofunctorPointFiberAtlasRestriction.mapPoints_restrict]
  change PseudofunctorPointFiberAtlasRestriction.mapPoints (relative f) ι (Core.mk L)
    (Core.mk M) (Over.mk b) (restrict f (restrictBundle f L ι) q M w x') = _
  rw [hx']
  simp [y', PseudofunctorPointFiberAtlasRestriction.mapPoints]

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianChartTestReduction

import Langlands.Global.AdelicSpreadModelPullbackStatement
import Langlands.Global.AdelicFixedModelPullbackProof

/-! # Actual generic-fiber adelic comparisons for arithmetic model pullbacks -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Natural point homeomorphisms carry a cone-leg pullback comparison to the
comparison for the image cone, with the product subspace topology. -/
private theorem isHomeomorph_imagePullbackPointComparison
    (C B A : Type u) [CommRing C] [CommRing B] [CommRing A]
    [Algebra C A] [Algebra B A]
    (G : Over (Spec (CommRingCat.of C)) ⥤ Over (Spec (CommRingCat.of B)))
    (τ : ∀ W : Over (Spec (CommRingCat.of C)), TopologicalSpace (RingPoint C W A))
    (σ : ∀ W : Over (Spec (CommRingCat.of C)),
      TopologicalSpace (RingPoint B (G.obj W) A))
    (e : ∀ W, @Homeomorph (RingPoint C W A) (RingPoint B (G.obj W) A)
      (τ W) (σ W))
    (he : ∀ {V W} (h : V ⟶ W) (p : RingPoint C V A),
      e W (p ≫ h) = e V p ≫ G.map h)
    {X Y Z : Over (Spec (CommRingCat.of C))}
    {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
    (hl : letI := τ X
      letI := τ Y
      @IsHomeomorph (RingPoint C c.pt A)
        {q : RingPoint C X A × RingPoint C Y A // q.1 ≫ f = q.2 ≫ g}
        (τ c.pt) inferInstance (affineSchemePullbackPointComparison C A c)) :
    letI := σ X
    letI := σ Y
    @IsHomeomorph (RingPoint B (G.obj c.pt) A)
      {q : RingPoint B (G.obj X) A × RingPoint B (G.obj Y) A //
        q.1 ≫ G.map f = q.2 ≫ G.map g}
      (σ c.pt) inferInstance
      (affineSchemePullbackPointComparison B A (c.map G)) := by
  let := τ X
  let := τ Y
  let := τ c.pt
  let := σ X
  let := σ Y
  let := σ c.pt
  let E := ((e X).prodCongr (e Y)).subtype
    (p := fun q : RingPoint C X A × RingPoint C Y A => q.1 ≫ f = q.2 ≫ g)
    (q := fun q : RingPoint B (G.obj X) A × RingPoint B (G.obj Y) A =>
      q.1 ≫ G.map f = q.2 ≫ G.map g)
    (fun q => by
      change q.1 ≫ f = q.2 ≫ g ↔ e X q.1 ≫ G.map f = e Y q.2 ≫ G.map g
      rw [← he, ← he]
      exact (e Z).injective.eq_iff.symm)
  let H := IsHomeomorph.homeomorph _ hl
  have hfun : (⇑(((e c.pt).symm.trans H).trans E)) =
      affineSchemePullbackPointComparison B A (c.map G) := by
    funext p
    apply Subtype.ext
    apply Prod.ext
    · change e X ((e c.pt).symm p ≫ c.fst) = p ≫ G.map c.fst
      rw [he, (e c.pt).apply_symm_apply]
    · change e Y ((e c.pt).symm p ≫ c.snd) = p ≫ G.map c.snd
      rw [he, (e c.pt).apply_symm_apply]
  rw [← hfun]
  exact (((e c.pt).symm.trans H).trans E).isHomeomorph

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Actual adelic pullbacks for the generic fibers of specified model cones. -/
theorem adelicSpreadModelPullback : AdelicSpreadModelPullbackStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ _ S X Y Z _ _ _ _ _ _ _ f g c hc
    let G := Over.pullback
      (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))
    let : Algebra F (curvePlaceAdeleOver k F S) :=
      inferInstanceAs (Algebra F (CurvePlaceAdeleRing k F))
    exact isHomeomorph_imagePullbackPointComparison
      (curvePlaceSIntegers k F S) F (curvePlaceAdeleOver k F S) G
      (curvePlaceFixedModelAdelePointTopology k F S)
      (fun W => curvePlaceSpreadAdelePointTopology k F S W (G.obj W) (Iso.refl _))
      (fun W => curvePlaceSpreadAdelePointHomeomorph k F S W (G.obj W) (Iso.refl _))
      (fun h p => by
        change curvePlaceGenericFiberAdelePointEquiv k F S _ (p ≫ h) ≫ 𝟙 _ =
          (curvePlaceGenericFiberAdelePointEquiv k F S _ p ≫ 𝟙 _) ≫ G.map h
        simpa only [Category.comp_id] using
          curvePlaceGenericFiberAdelePointEquiv_natural k F S h p)
      c (adelicFixedModelPullback.1 k F S X Y Z f g c hc)
  · intro K _ _ S X Y Z _ _ _ _ _ _ _ f g c hc
    let G := Over.pullback
      (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype))
    let : Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) :=
      (numberFieldAdeleOver K S).algebra
    let : Algebra K (numberFieldAdeleOver K S) :=
      inferInstanceAs (Algebra K (Adeles K))
    exact isHomeomorph_imagePullbackPointComparison
      ((S : Set (FinitePlace K)).integer K) K (numberFieldAdeleOver K S) G
      (numberFieldFixedModelAdelePointTopology K S)
      (fun W => numberFieldSpreadAdelePointTopology K S W (G.obj W) (Iso.refl _))
      (fun W => numberFieldSpreadAdelePointHomeomorph K S W (G.obj W) (Iso.refl _))
      (fun h p => by
        change numberFieldGenericFiberAdelePointEquiv K S _ (p ≫ h) ≫ 𝟙 _ =
          (numberFieldGenericFiberAdelePointEquiv K S _ p ≫ 𝟙 _) ≫ G.map h
        simpa only [Category.comp_id] using
          numberFieldGenericFiberAdelePointEquiv_natural K S h p)
      c (adelicFixedModelPullback.2 K S X Y Z f g c hc)

end Langlands.Global

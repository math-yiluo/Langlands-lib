import Langlands.Global.InfiniteAdelicGroupProduct
import Langlands.GroupScheme.AffinePointCoordinateSmooth
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Langlands.Global.ArchimedeanGL

/-! # Actual infinite adelic coordinate smoothness at the completions -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry NumberField
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Global.InfiniteAdelicGroupPoints

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- The existing mixed-coordinate criterion is exactly the collection of actual
completion criteria in real and complex coordinates. -/
theorem coordinateSmooth_iff_completions (p : M → InfiniteAdelicGroupPoints F G) :
    G.CoordinateSmooth (CommAlgCat.of F (InfiniteAdeleRing F))
        (B := mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom I p ↔
      (∀ vr : {v : InfinitePlace F // IsReal v},
        G.CoordinateSmooth (CommAlgCat.of F vr.1.Completion) (B := ℝ)
          (ringEquivRealOfIsReal vr.2).toRingHom I
          (fun x => atPlace F G vr.1 (p x))) ∧
      (∀ vc : {v : InfinitePlace F // IsComplex v},
        G.CoordinateSmooth (CommAlgCat.of F vc.1.Completion) (B := ℂ)
          (ringEquivComplexOfIsComplex vc.2).toRingHom I
          (fun x => atPlace F G vc.1 (p x))) := by
  constructor
  · intro hp
    constructor
    · intro vr a
      have h := contMDiff_pi_space.mp ((contMDiff_prod_module_iff _).mp (hp a)).1 vr
      change ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x => ringEquivRealOfIsReal vr.2
          (G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) (p x) a vr.1)) at h
      change ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x => ringEquivRealOfIsReal vr.2
          (G.affinePointEvaluation (CommAlgCat.of F vr.1.Completion)
            (atPlace F G vr.1 (p x)) a))
      exact h.congr (fun x => congrArg (ringEquivRealOfIsReal vr.2)
        (atPlace_evaluation F G (p x) a vr.1))
    · intro vc a
      have h := contMDiff_pi_space.mp ((contMDiff_prod_module_iff _).mp (hp a)).2 vc
      change ContMDiff I 𝓘(ℝ, ℂ) ∞
        (fun x => ringEquivComplexOfIsComplex vc.2
          (G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) (p x) a vc.1)) at h
      change ContMDiff I 𝓘(ℝ, ℂ) ∞
        (fun x => ringEquivComplexOfIsComplex vc.2
          (G.affinePointEvaluation (CommAlgCat.of F vc.1.Completion)
            (atPlace F G vc.1 (p x)) a))
      exact h.congr (fun x => congrArg (ringEquivComplexOfIsComplex vc.2)
        (atPlace_evaluation F G (p x) a vc.1))
  · intro hp a
    apply (contMDiff_prod_module_iff _).mpr
    constructor
    · apply contMDiff_pi_space.mpr
      intro vr
      change ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x => ringEquivRealOfIsReal vr.2
          (G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) (p x) a vr.1))
      have h := hp.1 vr a
      change ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x => ringEquivRealOfIsReal vr.2
          (G.affinePointEvaluation (CommAlgCat.of F vr.1.Completion)
            (atPlace F G vr.1 (p x)) a)) at h
      exact h.congr (fun x => congrArg (ringEquivRealOfIsReal vr.2)
        (atPlace_evaluation F G (p x) a vr.1).symm)
    · apply contMDiff_pi_space.mpr
      intro vc
      change ContMDiff I 𝓘(ℝ, ℂ) ∞
        (fun x => ringEquivComplexOfIsComplex vc.2
          (G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) (p x) a vc.1))
      have h := hp.2 vc a
      change ContMDiff I 𝓘(ℝ, ℂ) ∞
        (fun x => ringEquivComplexOfIsComplex vc.2
          (G.affinePointEvaluation (CommAlgCat.of F vc.1.Completion)
            (atPlace F G vc.1 (p x)) a)) at h
      exact h.congr (fun x => congrArg (ringEquivComplexOfIsComplex vc.2)
        (atPlace_evaluation F G (p x) a vc.1).symm)

/-- The actual completion decomposition preserves exactly the specified
coordinate-smooth families. -/
def coordinateSmoothCompletionFamilyEquiv :
    {p : M → InfiniteAdelicGroupPoints F G //
      G.CoordinateSmooth (CommAlgCat.of F (InfiniteAdeleRing F))
        (B := mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom I p} ≃
    {p : M → ((v : InfinitePlace F) → InfinitePlaceGroupPoints F G v) //
      (∀ vr : {v : InfinitePlace F // IsReal v},
        G.CoordinateSmooth (CommAlgCat.of F vr.1.Completion) (B := ℝ)
          (ringEquivRealOfIsReal vr.2).toRingHom I (fun x => p x vr.1)) ∧
      (∀ vc : {v : InfinitePlace F // IsComplex v},
        G.CoordinateSmooth (CommAlgCat.of F vc.1.Completion) (B := ℂ)
          (ringEquivComplexOfIsComplex vc.2).toRingHom I (fun x => p x vc.1))} where
  toFun p := ⟨fun x => completions F G (p.1 x),
    (coordinateSmooth_iff_completions F G I p.1).mp p.2⟩
  invFun p := ⟨fun x => assemble F G (p.1 x), by
    apply (coordinateSmooth_iff_completions F G I _).mpr
    simpa only [atPlace_assemble] using p.2⟩
  left_inv p := by
    apply Subtype.ext
    funext x
    exact (completions F G).symm_apply_apply (p.1 x)
  right_inv p := by
    apply Subtype.ext
    funext x
    exact (completions F G).apply_symm_apply (p.1 x)

omit [IsAffine G.X.left] in
/-- A mixed-coordinate-smooth family is continuous for the original infinite
adelic evaluation topology. -/
theorem coordinateSmooth_continuous {p : M → InfiniteAdelicGroupPoints F G}
    (hp : G.CoordinateSmooth (CommAlgCat.of F (InfiniteAdeleRing F))
        (B := mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom I p) :
    Continuous p := by
  apply (G.continuous_affinePoints_iff (CommAlgCat.of F (InfiniteAdeleRing F)) p).mpr
  intro a
  have h := (infiniteAdeleHomeomorph F).symm.continuous.comp (hp a).continuous
  change Continuous (fun x =>
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (InfiniteAdeleRing.ringEquiv_mixedSpace F
        (G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) (p x) a))) at h
  simpa only [RingEquiv.symm_apply_apply] using h

end Langlands.Global.InfiniteAdelicGroupPoints

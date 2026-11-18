import Langlands.GroupScheme.Lie.PointTangent
import Langlands.GroupScheme.Lie.SmoothOpenChart
import Langlands.AlgebraicGeometry.TangentSmoothness
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof

/-! # Smoothness from a chart surjective on identity tangent points -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.TangentSmoothness

variable {K : Type u} [Field K]

/-- Identity-preserving maps of underlying group schemes need not be group
homomorphisms to inherit tangent surjectivity from the actual identity kernels. -/
theorem isTangentSurjectiveAt_of_lieKernel_surjective
    {H G : GroupScheme (Spec (CommRingCat.of K))} (f : H.X ⟶ G.X)
    (hf : ∀ T : Over (Spec (CommRingCat.of K)), (1 : T ⟶ H.X) ≫ f = 1)
    (h : ∀ x : lieKernel G K, ∃ y : lieKernel H K, y.val ≫ f = x.val) :
    IsTangentSurjectiveAt H.X.hom G.X.hom f.left
      (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X).left := by
  intro t ht
  have he : (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X).left ≫ f.left =
      (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X).left :=
    congrArg CommaMorphism.left (hf _)
  rw [he] at ht
  let x := (Lie.kernelTangentEquiv G).symm ⟨t, ht⟩
  obtain ⟨y, hy⟩ := h x
  exact ⟨y.val.left, (Lie.kernelTangentEquiv H y).property,
    congrArg CommaMorphism.left hy⟩

/-- A locally finite-type field group with a smooth source chart surjective
on tangent vectors at one rational point is smooth. The chart itself is
not required to be a homomorphism or an immersion. -/
theorem smooth_of_isTangentSurjectiveAt
    (G : GroupScheme (Spec (CommRingCat.of K))) [LocallyOfFiniteType G.X.hom]
    (U : Over (Spec (CommRingCat.of K))) [Smooth U.hom]
    (f : U ⟶ G.X) (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ U)
    (h : IsTangentSurjectiveAt U.hom G.X.hom f.left x.left) : Smooth G.X.hom := by
  have : LocallyOfFinitePresentation f.left :=
    locallyOfFinitePresentation_of_comp_eq f.left (Over.w f)
  have hz := mem_smoothLocus_of_isTangentSurjectiveAt f.left (Over.w f) (Over.w x) h
  let W := f.left.smoothLocus
  let p := W.ι ≫ f.left
  have hp : Smooth p := by
    dsimp only [p, W]
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
      Scheme.Opens.ι_preimage_self]
  have hpg : Smooth (p ≫ G.X.hom) := by
    dsimp only [p]
    rw [Category.assoc, Over.w f]
    infer_instance
  let V : G.X.left.Opens := ⟨Set.range p, p.isOpenMap.isOpen_range⟩
  have hWV : (⊤ : W.toScheme.Opens) ≤ p ⁻¹ᵁ V := fun w _ => ⟨w, rfl⟩
  let r := p.resLE V ⊤ hWV
  have hr : Smooth r := IsZariskiLocalAtSource.resLE hWV hp
  have hrs : Surjective r := by
    constructor
    rintro ⟨_, w, rfl⟩
    refine ⟨⟨w, trivial⟩, V.ι.isOpenEmbedding.injective ?_⟩
    change (r ≫ V.ι) ⟨w, trivial⟩ = _
    rw [Scheme.Hom.resLE_comp_ι]
    rfl
  have hrg : Smooth (r ≫ V.ι ≫ G.X.hom) := by
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
    infer_instance
  have hV : Smooth (V.ι ≫ G.X.hom) :=
    Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp r _
  have hne : Nonempty V := ⟨⟨p ⟨x.left (IsLocalRing.closedPoint K), hz⟩,
    ⟨⟨x.left (IsLocalRing.closedPoint K), hz⟩, rfl⟩⟩⟩
  apply HasNonemptySmoothOpenChart.smooth
  refine ⟨Over.mk (V.ι ≫ G.X.hom), Over.homMk V.ι, hV, hne, ?_⟩
  exact inferInstanceAs (IsOpenImmersion V.ι)

/-- A smooth field group source and an identity-preserving chart whose actual
identity tangent kernels are surjective suffice to prove the target smooth. -/
theorem smooth_of_lieKernel_surjective_chart
    {H G : GroupScheme (Spec (CommRingCat.of K))}
    [Smooth H.X.hom] [LocallyOfFiniteType G.X.hom] (f : H.X ⟶ G.X)
    (hf : ∀ T : Over (Spec (CommRingCat.of K)), (1 : T ⟶ H.X) ≫ f = 1)
    (h : ∀ x : lieKernel G K, ∃ y : lieKernel H K, y.val ≫ f = x.val) :
    Smooth G.X.hom :=
  smooth_of_isTangentSurjectiveAt G H.X f 1
    (isTangentSurjectiveAt_of_lieKernel_surjective f hf h)

/-- An actual identity-preserving chart from a smooth field group with
surjective identity tangent kernels. Its morphism need not be a homomorphism. -/
structure LieKernelSurjectiveChart (G : GroupScheme (Spec (CommRingCat.of K))) where
  source : GroupScheme (Spec (CommRingCat.of K))
  smoothSource : Smooth source.X.hom
  chart : source.X ⟶ G.X
  one_chart : ∀ T : Over (Spec (CommRingCat.of K)), (1 : T ⟶ source.X) ≫ chart = 1
  tangent_surjective : ∀ x : lieKernel G K, ∃ y : lieKernel source K, y.val ≫ chart = x.val

/-- The actual chart data imply smoothness of a locally finite-type target. -/
theorem LieKernelSurjectiveChart.smooth
    {G : GroupScheme (Spec (CommRingCat.of K))} [LocallyOfFiniteType G.X.hom]
    (c : LieKernelSurjectiveChart G) : Smooth G.X.hom := by
  have : Smooth c.source.X.hom := c.smoothSource
  exact smooth_of_lieKernel_surjective_chart c.chart c.one_chart c.tangent_surjective

end Langlands.GroupScheme

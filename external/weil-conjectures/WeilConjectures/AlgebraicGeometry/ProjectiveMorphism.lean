/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.DenseCompactification
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineImmersion

/-!
# Projective morphisms, properness and compactifications of affine schemes

Projective morphisms in the sense of blueprint `def-kun-projective` (a closed immersion into a
projective space `ℙ(n; Y)` followed by the projection) are the H-projective morphisms
`AlgebraicGeometry.IsHProjective` of `WeilConjectures/AlgebraicGeometry/Curve/SmoothProjective`.

## Main results

- `AlgebraicGeometry.isHProjective_iff` (blueprint `def-kun-projective`): the defining
  characterisation of projective morphisms.
- `AlgebraicGeometry.isProper_of_isHProjective` (blueprint `lem-kun-projective-implies-proper`).
- `AlgebraicGeometry.isProper_isStableUnderBaseChange_and_comp` (blueprint
  `lem-kun-proper-stability`).
- `AlgebraicGeometry.exists_isHProjective_compactification_of_isAffine` (blueprint
  `corollary-open-direct-image-over-field--2`): an affine scheme of finite type over a field is a
  dense open subscheme of a projective scheme of the same dimension.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

/-- Blueprint `def-kun-projective`: **projective morphisms.** A morphism `f : X ⟶ Y` is
projective (`AlgebraicGeometry.IsHProjective`) if and only if there are a finite type `n` of
homogeneous coordinates and a closed immersion `i : X ⟶ ℙ(n; Y)` whose composite with the
structural projection `ℙ(n; Y) ⟶ Y` is `f`. A scheme is projective over a field `k` if its
structure morphism is projective. -/
theorem isHProjective_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsHProjective f ↔
      ∃ (n : Type u) (_ : Finite n) (i : X ⟶ ℙ(n; Y)), IsClosedImmersion i ∧ i ≫ ℙ(n; Y) ↘ Y = f :=
  ⟨fun h ↦ h.exists_isClosedImmersion, fun h ↦ ⟨h⟩⟩

/-- Blueprint `lem-kun-projective-implies-proper`: **projective morphisms are proper**, as the
composite of a closed immersion with the proper projection `ℙ(n; Y) ⟶ Y`. -/
theorem isProper_of_isHProjective {X Y : Scheme.{u}} (f : X ⟶ Y) [IsHProjective f] :
    IsProper f :=
  inferInstance

/-- Blueprint `lem-kun-proper-stability`: **properness survives base change and composition.**
Proper morphisms are stable under base change and under composition; in particular, if `X` is
proper over a field `k` and `Y` is any `k`-scheme, the projection `X ×_k Y ⟶ Y` is proper. -/
theorem isProper_isStableUnderBaseChange_and_comp :
    MorphismProperty.IsStableUnderBaseChange @IsProper ∧
      MorphismProperty.IsStableUnderComposition @IsProper ∧
      ∀ {k : Type u} [Field k] {X Y : Scheme.{u}} (a : X ⟶ Spec (.of k))
        (b : Y ⟶ Spec (.of k)) [IsProper a], IsProper (pullback.snd a b) :=
  ⟨inferInstance, inferInstance, fun _ _ ↦ inferInstance⟩

/-- Blueprint `corollary-open-direct-image-over-field--2`: **compactification of an affine scheme.**
Let `X` be an affine scheme of finite type over a field `K`. There is an open immersion
`j : X ⟶ X̄` over `K` with dense image into a projective `K`-scheme `X̄`, and
`dim X̄ = dim X`. Take an immersion `X ⟶ ℙ(n; K)` and let `X̄` be the scheme-theoretic
closure of its image: it is a closed subscheme of `ℙ(n; K)`, the immersion factors through it as
a dense open immersion, and the dimension of `X̄` is that of its dense open subscheme `X`. -/
theorem exists_isHProjective_compactification_of_isAffine {K : Type u} [Field K]
    {X : Scheme.{u}} [IsAffine X] (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] :
    ∃ (X' : Scheme.{u}) (a' : X' ⟶ Spec (.of K)) (j : X ⟶ X'), IsHProjective a' ∧
      IsOpenImmersion j ∧ j ≫ a' = a ∧ Dense (Set.range j) ∧
      topologicalKrullDim X' = topologicalKrullDim X := by
  obtain ⟨n, _, i, hi, hia⟩ := exists_isImmersion_projectiveSpace a
  have : IsLocallyNoetherian ℙ(n; Spec (.of K)) :=
    LocallyOfFiniteType.isLocallyNoetherian (ℙ(n; Spec (.of K)) ↘ Spec (.of K))
  have : QuasiCompact i := by
    rw [← i.liftCoborder_ι]
    infer_instance
  have hcomm : i.toImage ≫ i.imageι ≫ ℙ(n; Spec (.of K)) ↘ Spec (.of K) = a := by
    rw [i.toImage_imageι_assoc, hia]
  have hdense : Dense (Set.range i.toImage) := by
    have hι := i.imageι.isClosedEmbedding
    refine dense_iff_closure_eq.mpr (hι.injective.image_injective ?_)
    rw [Set.image_univ, ← hι.closure_image_eq, ← Set.range_comp, ← TopCat.coe_comp,
      ← Scheme.Hom.comp_base, i.toImage_imageι, i.range_imageι]
  have hproj : IsHProjective (i.imageι ≫ ℙ(n; Spec (.of K)) ↘ Spec (.of K)) :=
    ⟨⟨n, inferInstance, i.imageι, inferInstance, rfl⟩⟩
  refine ⟨_, _, i.toImage, hproj, inferInstance, hcomm, hdense, le_antisymm ?_
    i.toImage.isOpenEmbedding.isInducing.topologicalKrullDim_le⟩
  refine (topologicalKrullDim_le_of_dense (i.imageι ≫ ℙ(n; Spec (.of K)) ↘ Spec (.of K))
    i.toImage.opensRange hdense).trans_eq ?_
  exact i.toImage.isOpenEmbedding.isEmbedding.topologicalKrullDim_eq_range.symm

end AlgebraicGeometry

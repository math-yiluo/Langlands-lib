import Langlands.AlgebraicGeometry.SectionComponentBaseChange
import Langlands.AlgebraicGeometry.SectionComponentLocality
import Langlands.AlgebraicGeometry.SectionComponentNoetherianModel
import Langlands.AlgebraicGeometry.GeometricallyReducedOfAlgClosedProof

/-! # Reduction of section-component openness to indexed Noetherian fibres

The common-field descent argument adapts
`P2M/Sol/S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.lean`
from the Anthropic FLT formalization at commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Copyright 2026 Anthropic, PBC,
licensed under Apache License, Version 2.0. See `licenses/Anthropic-FLT/LICENSE`,
`NOTICE` and `ATTRIBUTION.md`. The adaptation replaces connectedness descent by
faithfully flat descent of reducedness.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Geometric reducedness descends along an arbitrary surjective change of base. -/
theorem geometricallyReduced_of_surjective_baseChange
    {X S S' : Scheme.{u}} (f : X ⟶ S) (σ : S' ⟶ S) [Surjective σ]
    [hgr : GeometricallyReduced (pullback.snd f σ)] : GeometricallyReduced f := by
  refine ⟨fun K _ k Z a b hZ => ?_⟩
  obtain ⟨z, -⟩ := (pullback.fst k σ).surjective default
  let ι := (pullback k σ).fromSpecResidueField z
  let kL : Spec ((pullback k σ).residueField z) ⟶ Spec (.of K) :=
    ι ≫ pullback.fst k σ
  let l' : Spec ((pullback k σ).residueField z) ⟶ S' :=
    ι ≫ pullback.snd k σ
  have hkl : kL ≫ k = l' ≫ σ := by
    simp only [kL, l', Category.assoc, pullback.condition]
  have : Surjective kL := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  have s : IsPullback (pullback.fst b kL ≫ a) (pullback.snd b kL) f (l' ≫ σ) := by
    rw [← hkl]
    exact (IsPullback.of_hasPullback b kL).paste_horiz hZ
  let m : pullback b kL ⟶ pullback f σ :=
    pullback.lift (pullback.fst b kL ≫ a) (pullback.snd b kL ≫ l')
      (by simpa only [Category.assoc] using s.w)
  have hm₁ : m ≫ pullback.fst f σ = pullback.fst b kL ≫ a := pullback.lift_fst ..
  have hm₂ : m ≫ pullback.snd f σ = pullback.snd b kL ≫ l' := pullback.lift_snd ..
  have s' : IsPullback (m ≫ pullback.fst f σ) (pullback.snd b kL) f (l' ≫ σ) := by
    rw [hm₁]
    exact s
  have sq : IsPullback m (pullback.snd b kL) (pullback.snd f σ) l' :=
    IsPullback.of_right s' hm₂ (IsPullback.of_hasPullback f σ)
  have : IsReduced (pullback b kL) :=
    hgr.geometrically_isReduced l' m (pullback.snd b kL) sq
  exact GeometricallyReducedOfAlgClosedProof.isReduced_of_flat_of_surjective
    (pullback.fst b kL)

/-- Geometric reducedness descends through a Cartesian square with surjective base map. -/
theorem geometricallyReduced_of_surjective_isPullback
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : X' ⟶ X} {b : Y' ⟶ Y} (h : IsPullback g f' f b)
    [Surjective b] [GeometricallyReduced f'] : GeometricallyReduced f := by
  have : GeometricallyReduced (pullback.snd f b) := by
    rw [← h.isoPullback_inv_snd,
      MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyReduced)]
    infer_instance
  exact geometricallyReduced_of_surjective_baseChange f b

namespace SectionComponent

/-- A geometrically reduced fibre reflects geometric reducedness to its corresponding
fibre before arbitrary Cartesian base change. -/
theorem geometricallyReduced_fiber_of_isPullback
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : X' ⟶ X} {b : Y' ⟶ Y} (h : IsPullback g f' f b) (y' : Y')
    [hred : GeometricallyReduced (f'.fiberToSpecResidueField y')] :
    GeometricallyReduced (f.fiberToSpecResidueField (b y')) := by
  have : Surjective (Spec.map (b.residueFieldMap y')) :=
    ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  exact geometricallyReduced_of_surjective_isPullback (f' := f'.fiberToSpecResidueField y')
    (isPullback_fiberToSpecResidueField_of_isPullback h y')

/-- The local Noetherian assertion needed for approximation: at a geometrically reduced
indexed fibre, every point of its selected component is interior to the relative union. -/
def NoetherianFiberwiseOpennessStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (X : Scheme.{u})
    (f : X ⟶ Spec R) (e : Spec R ⟶ X) (he : e ≫ f = 𝟙 (Spec R)),
    Flat f → LocallyOfFinitePresentation f → QuasiCompact f → QuasiSeparated f →
      ∀ x : X, GeometricallyReduced (f.fiberToSpecResidueField (f x)) →
        x ∈ componentSet f e he → x ∈ interior (componentSet f e he)

/-- The Noetherian indexed-fibre assertion implies the exact arbitrary-base target. -/
theorem flatFinitePresentationOpenness_of_noetherianFiberwise
    (H : NoetherianFiberwiseOpennessStatement.{u}) :
    FlatFinitePresentationOpennessStatement.{u} := by
  apply flatFinitePresentationOpenness_iff_affineBase.mpr
  intro R X f e he hflat hlfp hqc hqs hgr
  have := hflat
  have := hlfp
  have := hqc
  have := hqs
  have := hgr
  obtain ⟨M⟩ := nonempty_noetherianSectionModel f e he
  let b := Spec.map (CommRingCat.ofHom (algebraMap ↥M.subalgebra R))
  have hcomp : M.comparison ⁻¹' componentSet M.morphism M.sectionMorphism M.section_eq =
      componentSet f e he :=
    preimage_componentSet_of_isPullback_locallyOfFiniteType M.cartesian M.section_comparison
  apply subset_interior_iff_isOpen.mp
  intro x hx
  have hxM : M.comparison x ∈ componentSet M.morphism M.sectionMorphism M.section_eq := by
    change x ∈ M.comparison ⁻¹' componentSet M.morphism M.sectionMorphism M.section_eq
    rw [hcomp]
    exact hx
  have hred : GeometricallyReduced (M.morphism.fiberToSpecResidueField (b (f x))) :=
    geometricallyReduced_fiber_of_isPullback M.cartesian (f x)
  have hbase : M.morphism (M.comparison x) = b (f x) :=
    congrArg (fun q : X ⟶ Spec (CommRingCat.of ↥M.subalgebra) => q x) M.cartesian.w
  have hred' : GeometricallyReduced
      (M.morphism.fiberToSpecResidueField (M.morphism (M.comparison x))) := by
    rw [hbase]
    exact hred
  have hxI := H (CommRingCat.of ↥M.subalgebra) M.scheme M.morphism M.sectionMorphism
    M.section_eq inferInstance inferInstance inferInstance inferInstance
    (M.comparison x) hred' hxM
  have hxI' := preimage_interior_subset_interior_preimage M.comparison.continuous hxI
  rwa [hcomp] at hxI'

end SectionComponent

end Langlands.AlgebraicGeometry

import Langlands.AlgebraicGeometry.EtaleLocalDimension
import Langlands.AlgebraicGeometry.SchemePureDimensionProof
import Langlands.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeSourceDescentProof

/-! # Relative pure fibre dimension and etale scheme charts -/

noncomputable section

universe u

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped Set.Notation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Local finite type and componentwise pure dimension `d` of every actual fibre. -/
def PureFibreDimensionMorphismProperty (d : ℕ) : MorphismProperty Scheme.{u} :=
  @LocallyOfFiniteType.{u} ⊓ HasPureDimensionFibers d

/-- Etale source maps preserve relative local topological dimension pointwise. -/
theorem relativeTopologicalKrullDimAt_etale_source
    {U X Y : Scheme.{u}} (p : U ⟶ X) (f : X ⟶ Y) [Etale p] (x : U) :
    relativeTopologicalKrullDimAt (p ≫ f) x =
      relativeTopologicalKrullDimAt f (p x) := by
  let y := (p ≫ f) x
  let m : (p ≫ f).fiber y ⟶ f.fiber y :=
    pullback.lift ((p ≫ f).fiberι y ≫ p) ((p ≫ f).fiberToSpecResidueField y) (by
      rw [Category.assoc]
      exact (p ≫ f).fiber_fac y)
  have hm₁ : m ≫ f.fiberι y = (p ≫ f).fiberι y ≫ p := pullback.lift_fst _ _ _
  have hm₂ : m ≫ f.fiberToSpecResidueField y =
      (p ≫ f).fiberToSpecResidueField y := pullback.lift_snd _ _ _
  have hbig : IsPullback ((p ≫ f).fiberι y) (m ≫ f.fiberToSpecResidueField y)
      (p ≫ f) (Y.fromSpecResidueField y) := by
    rw [hm₂]
    exact IsPullback.of_hasPullback _ _
  have hsmall : IsPullback (f.fiberι y) (f.fiberToSpecResidueField y)
      f (Y.fromSpecResidueField y) := IsPullback.of_hasPullback _ _
  have hm : IsPullback ((p ≫ f).fiberι y) m p (f.fiberι y) :=
    hbig.of_bot hm₁.symm hsmall
  have : Etale m := MorphismProperty.of_isPullback hm inferInstance
  have himage : f.fiberι y (m ((p ≫ f).asFiber x)) = p x := by
    rw [← Scheme.Hom.comp_apply, hm₁, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber]
  calc
    relativeTopologicalKrullDimAt (p ≫ f) x =
        topologicalKrullDimAt ((p ≫ f).asFiber x) := rfl
    _ = topologicalKrullDimAt (m ((p ≫ f).asFiber x)) :=
      topologicalKrullDimAt_etale m ((p ≫ f).asFiber x)
    _ = relativeTopologicalKrullDimAt f (f.fiberι y (m ((p ≫ f).asFiber x))) :=
      (relativeTopologicalKrullDimAt_fiberι f y _).symm
    _ = relativeTopologicalKrullDimAt f (p x) := congrArg _ himage

/-- A locally quasi-finite target map preserves relative local topological dimension.
Its discrete point fibres make the smaller fibre open in the composite fibre. -/
theorem relativeTopologicalKrullDimAt_locallyQuasiFinite_target
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyQuasiFinite g] (x : X) :
    relativeTopologicalKrullDimAt (f ≫ g) x = relativeTopologicalKrullDimAt f x := by
  let A : Set X := (f ≫ g) ⁻¹' {(f ≫ g) x}
  let B : Set X := f ⁻¹' {f x}
  let D : Set Y := g ⁻¹' {g (f x)}
  have hBA : B ⊆ A := by
    intro z hz
    change g (f z) = g (f x)
    exact congrArg g hz
  let k : A → D := fun z => ⟨f z.1, z.2⟩
  have hk : Continuous k :=
    (f.continuous.comp continuous_subtype_val).subtype_mk _
  have : DiscreteTopology D := isDiscrete_iff_discreteTopology.mp (g.isDiscrete_preimage_singleton (g (f x)))
  have hop : IsOpen (A ↓∩ B) := by
    have he : k ⁻¹' {(⟨f x, rfl⟩ : D)} = A ↓∩ B := by
      ext z
      change k z = ⟨f x, rfl⟩ ↔ f z.1 = f x
      exact Subtype.ext_iff
    rw [← he]
    exact (isOpen_discrete _).preimage hk
  have hj : IsOpenEmbedding (Set.inclusion hBA) := .inclusion hBA hop
  have hdim := topologicalKrullDimAt_eq_of_isOpenEmbedding hj (⟨x, rfl⟩ : B)
  exact (relativeTopologicalKrullDimAt_eq_preimage_singleton (f ≫ g) x).trans
    (hdim.symm.trans (relativeTopologicalKrullDimAt_eq_preimage_singleton f x).symm)

/-- Local finite type and pure fibre dimension are invariant under isomorphisms. -/
instance (d : ℕ) : (PureFibreDimensionMorphismProperty.{u} d).RespectsIso :=
  MorphismProperty.RespectsIso.inf @LocallyOfFiniteType (HasPureDimensionFibers d)

/-- Arbitrary scheme base change preserves local finite type and pure fibre dimension. -/
instance (d : ℕ) : (PureFibreDimensionMorphismProperty.{u} d).IsStableUnderBaseChange where
  of_isPullback {X Y P S} {f g f' g'} h hg := by
    have : LocallyOfFiniteType g := hg.1
    refine ⟨MorphismProperty.of_isPullback h hg.1, fun x => ?_⟩
    exact (hasPureDimension_locallyFiniteType_fiberBaseChange_iff h x d).mpr (hg.2 (f x))

/-- Etale source maps preserve local finite type and pure fibre dimension. -/
theorem pureFibreDimension_precomp_etale (d : ℕ)
    {U X Y : Scheme.{u}} (p : U ⟶ X) (f : X ⟶ Y)
    (hp : Etale p) (hf : PureFibreDimensionMorphismProperty d f) :
    PureFibreDimensionMorphismProperty d (p ≫ f) := by
  have : Etale p := hp
  have : LocallyOfFiniteType f := hf.1
  refine ⟨inferInstance, (hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq
    (p ≫ f) d).mpr ?_⟩
  intro x
  exact (relativeTopologicalKrullDimAt_etale_source p f x).trans
    ((hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq f d).mp hf.2 (p x))

/-- Etale target maps preserve local finite type and pure fibre dimension. -/
theorem pureFibreDimension_postcomp_etale (d : ℕ)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : PureFibreDimensionMorphismProperty d f) (hg : Etale g) :
    PureFibreDimensionMorphismProperty d (f ≫ g) := by
  have : Etale g := hg
  have : LocallyQuasiFinite g := Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale g
  have : LocallyOfFiniteType f := hf.1
  refine ⟨inferInstance, (hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq
    (f ≫ g) d).mpr ?_⟩
  intro x
  exact (relativeTopologicalKrullDimAt_locallyQuasiFinite_target f g x).trans
    ((hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq f d).mp hf.2 x)

/-- A composite with etale second map has pure fibre dimension exactly as the first map. -/
theorem pureFibreDimension_of_postcomp_etale (d : ℕ)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : Etale g) (hf : PureFibreDimensionMorphismProperty d (f ≫ g)) :
    PureFibreDimensionMorphismProperty d f := by
  have : Etale g := hg
  have : LocallyQuasiFinite g := Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale g
  have : LocallyOfFiniteType (f ≫ g) := hf.1
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f g
  refine ⟨inferInstance, (hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq f d).mpr ?_⟩
  intro x
  exact (relativeTopologicalKrullDimAt_locallyQuasiFinite_target f g x).symm.trans
    ((hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq (f ≫ g) d).mp hf.2 x)

/-- Pure fibre dimension descends through a surjective etale source map. -/
theorem pureFibreDimension_of_precomp_etale_surjective (d : ℕ)
    {U X Y : Scheme.{u}} (p : U ⟶ X) (f : X ⟶ Y)
    (hp : Etale p) (hs : Surjective p)
    (hf : PureFibreDimensionMorphismProperty d (p ≫ f)) :
    PureFibreDimensionMorphismProperty d f := by
  have : Etale p := hp
  have : LocallyOfFiniteType (p ≫ f) := hf.1
  have : LocallyOfFiniteType f :=
    Langlands.AlgebraicGeometry.locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp
      _ _ _ p f hs inferInstance inferInstance hf.1
  refine ⟨inferInstance, (hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq f d).mpr ?_⟩
  intro x
  obtain ⟨z, rfl⟩ := hs.surj x
  exact (relativeTopologicalKrullDimAt_etale_source p f z).symm.trans
    ((hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq (p ≫ f) d).mp hf.2 z)

/-- Pure fibre dimension, with local finite type retained, is invariant under
surjective etale source charts and under etale target maps. -/
def EtalePureFibreDimensionComparisonStatement : Prop :=
  ∀ d : ℕ,
    (∀ {U X Y : Scheme.{u}} (p : U ⟶ X) (f : X ⟶ Y),
      Etale p → Surjective p →
        (PureFibreDimensionMorphismProperty d (p ≫ f) ↔
          PureFibreDimensionMorphismProperty d f)) ∧
    (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      Etale g →
        (PureFibreDimensionMorphismProperty d (f ≫ g) ↔
          PureFibreDimensionMorphismProperty d f))

/-- The etale pure-fibre-dimension comparison follows from the pointwise relative
dimension identities and local-finite-type source descent. -/
theorem etalePureFibreDimensionComparison :
    EtalePureFibreDimensionComparisonStatement.{u} := by
  intro d
  constructor
  · intro U X Y p f hp hs
    exact ⟨pureFibreDimension_of_precomp_etale_surjective d p f hp hs,
      pureFibreDimension_precomp_etale d p f hp⟩
  · intro X Y Z f g hg
    exact ⟨pureFibreDimension_of_postcomp_etale d f g hg,
      fun hf => pureFibreDimension_postcomp_etale d f g hf hg⟩

end Langlands.AlgebraicGeometry.SchemeFiberGeometry

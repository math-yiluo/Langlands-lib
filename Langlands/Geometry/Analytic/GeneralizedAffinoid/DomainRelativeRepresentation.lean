import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCancellation
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainComparison
import Langlands.Geometry.Analytic.Spectrum.Properties
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Relative representations along actual full-domain inclusions -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}

/-- If a structural map and its composite represent full domains, the
second map fully represents its own actual spectral image. -/
theorem Represents.of_comp {i : BoundedAlgHom K A B}
    {j : BoundedAlgHom K B C} {U V : Set (BanachSpectrum A)}
    (hi : Represents K i U) (hij : Represents K (j.comp i) V) :
    Represents K j (Set.range (BanachSpectrum.comap j.toBoundedRingHom)) := by
  refine ⟨(isCompact_range (BanachSpectrum.comapContinuous
    j.toBoundedRingHom).continuous).isClosed, rfl, ?_⟩
  intro R φ hφ
  have hφ' : HasImageIn K (φ.comp i) V := by
    intro x
    obtain ⟨y, hy⟩ := hφ x
    have h := hij.hasImageIn y
    change BanachSpectrum.comap i.toBoundedRingHom
      (BanachSpectrum.comap j.toBoundedRingHom y) ∈ V at h
    rw [hy] at h
    exact h
  obtain ⟨ψ, hψ, huniq⟩ := hij.2.2 R (φ.comp i) hφ'
  refine ⟨ψ, ?_, ?_⟩
  · apply hi.hom_ext R
    rw [BoundedAlgHom.comp_assoc]
    exact hψ
  · intro ψ' hψ'
    apply huniq ψ'
    rw [← BoundedAlgHom.comp_assoc, hψ']

namespace Domain

variable (U : Domain K A)

/-- The supplied inclusion restriction represents its actual spectral
image over the containing domain algebra, without an injectivity input. -/
theorem represents_relative (V : Domain K A) (f : V ⟶ U) :
    Represents K f.restriction (Set.range f.spectrumMap) := by
  apply U.represents.of_comp
  rw [f.comp_baseMap]
  exact V.represents

/-- Regard an existing contained ambient domain as a full domain over the
containing domain's actual algebra. Its locus is the actual spectral image. -/
def relative (V : Domain K A) (f : V ⟶ U) : Domain K U.algebra where
  algebra := V.algebra
  baseMap := f.restriction
  locus := Set.range f.spectrumMap
  represents := U.represents_relative V f

@[simp]
theorem relative_algebra (V : Domain K A) (f : V ⟶ U) :
    (U.relative V f).algebra = V.algebra := rfl

@[simp]
theorem relative_baseMap (V : Domain K A) (f : V ⟶ U) :
    (U.relative V f).baseMap = f.restriction := rfl

@[simp]
theorem relative_locus (V : Domain K A) (f : V ⟶ U) :
    (U.relative V f).locus = Set.range f.spectrumMap := rfl

theorem relative_baseMap_comp (V : Domain K A) (f : V ⟶ U) :
    (U.relative V f).baseMap.comp U.baseMap = V.baseMap := f.comp_baseMap

/-- The new locus maps onto exactly the original ambient locus. -/
theorem image_relative_locus (V : Domain K A) (f : V ⟶ U) :
    U.spectrumMap '' (U.relative V f).locus = V.locus := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    rw [f.spectrumMap_over_base]
    exact V.represents.hasImageIn y
  · intro hx
    obtain ⟨y, hy⟩ := V.represents.2.1.symm ▸ hx
    exact ⟨f.spectrumMap y, ⟨y, rfl⟩, (f.spectrumMap_over_base y).trans hy⟩

theorem relative_locus_subset_preimage (V : Domain K A) (f : V ⟶ U) :
    (U.relative V f).locus ⊆ U.spectrumMap ⁻¹' V.locus := by
  rintro _ ⟨y, rfl⟩
  change U.spectrumMap (f.spectrumMap y) ∈ V.locus
  rw [f.spectrumMap_over_base]
  exact V.represents.hasImageIn y

/-- Identifying this image with the full inverse image requires only the
injectivity of the particular containing domain's structural spectrum map. -/
theorem relative_locus_eq_preimage_of_injective
    (hU : Function.Injective U.spectrumMap) (V : Domain K A) (f : V ⟶ U) :
    (U.relative V f).locus = U.spectrumMap ⁻¹' V.locus := by
  apply Set.Subset.antisymm (U.relative_locus_subset_preimage V f)
  intro x hx
  obtain ⟨y, hy⟩ := V.represents.2.1.symm ▸ hx
  exact ⟨y, hU ((f.spectrumMap_over_base y).trans hy)⟩

/-- Commuting ambient inclusion triangles retain the entire bounded
restriction after passing to the containing domain's algebra. -/
def relativeFunctor : Over U ⥤ Domain K U.algebra where
  obj V := U.relative V.left V.hom
  map f := ⟨f.left.restriction, congrArg Inclusion.restriction f.w⟩
  map_id _ := Inclusion.ext rfl
  map_comp _ _ := Inclusion.ext rfl

@[simp]
theorem relativeFunctor_map_restriction
    {V W : Over U} (f : V ⟶ W) :
    (U.relativeFunctor.map f).restriction = f.left.restriction := rfl

/-- A relative bounded inclusion gives the original ambient inclusion and
its whole commuting triangle, not just an inclusion of spectrum images. -/
def fullyFaithfulRelativeFunctor : U.relativeFunctor.FullyFaithful where
  preimage {V W} f := by
    let r : BoundedAlgHom K W.left.algebra V.left.algebra := f.restriction
    have hr : r.comp W.hom.restriction = V.hom.restriction := f.comp_baseMap
    refine Over.homMk (⟨r, ?_⟩ : V.left ⟶ W.left) ?_
    · rw [← W.hom.comp_baseMap, ← BoundedAlgHom.comp_assoc, hr,
        V.hom.comp_baseMap]
    · apply Inclusion.ext
      exact hr
  map_preimage _ := Inclusion.ext rfl
  preimage_map _ := by
    apply Over.OverMorphism.ext
    apply Inclusion.ext
    rfl

instance : U.relativeFunctor.Full := U.fullyFaithfulRelativeFunctor.full

instance : U.relativeFunctor.Faithful := U.fullyFaithfulRelativeFunctor.faithful

theorem relativeFunctor_comp_toAffinoidSpace :
    U.relativeFunctor ⋙ toAffinoidSpace K U.algebra =
      Over.forget U ⋙ toAffinoidSpace K A := rfl

theorem relativeFunctor_comp_toTopologicalSpace :
    U.relativeFunctor ⋙ toTopologicalSpace K U.algebra =
      Over.forget U ⋙ toTopologicalSpace K A := rfl

/-- Nested ambient inclusions give an actual relative inclusion with the
original bounded restriction. -/
def relativeInclusion {V W : Domain K A} (g : W ⟶ V) (f : V ⟶ U) :
    U.relative W (g ≫ f) ⟶ U.relative V f where
  restriction := g.restriction
  comp_baseMap := rfl

@[simp]
theorem relativeInclusion_restriction {V W : Domain K A}
    (g : W ⟶ V) (f : V ⟶ U) :
    (U.relativeInclusion g f).restriction = g.restriction := rfl

/-- Repeated passage along a nested pair of actual inclusions is literally
the direct relative representation, including its bounded structural map. -/
theorem relative_relative {V W : Domain K A} (g : W ⟶ V) (f : V ⟶ U) :
    (U.relative V f).relative (U.relative W (g ≫ f)) (U.relativeInclusion g f) =
      V.relative W g := rfl

end Domain
end Langlands.Analytic.PresentedAffinoidAlgebra

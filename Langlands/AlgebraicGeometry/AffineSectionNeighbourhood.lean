import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Affine neighbourhoods of a section -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (e : Y ⟶ X)

/-- Affine source and base neighbourhoods on which a section restricts. -/
structure AffineSectionNeighbourhood (y : Y) where
  base : Scheme.{u}
  total : Scheme.{u}
  baseι : base ⟶ Y
  totalι : total ⟶ X
  hom : total ⟶ base
  sectionMap : base ⟶ total
  [affine_base : IsAffine base]
  [affine_total : IsAffine total]
  [open_baseι : IsOpenImmersion baseι]
  [open_totalι : IsOpenImmersion totalι]
  mem_base : y ∈ Set.range baseι
  comm : totalι ≫ f = hom ≫ baseι
  section_comp : sectionMap ≫ totalι = baseι ≫ e
  section_hom : sectionMap ≫ hom = 𝟙 base

attribute [instance] AffineSectionNeighbourhood.affine_base
  AffineSectionNeighbourhood.affine_total AffineSectionNeighbourhood.open_baseι
  AffineSectionNeighbourhood.open_totalι

/-- Shrinking affine neighbourhoods of a base point and its section point
gives an affine neighbourhood with a genuine restricted section. -/
def affineSectionNeighbourhood (he : e ≫ f = 𝟙 Y) (y : Y) :
    AffineSectionNeighbourhood f e y := by
  refine Classical.choice ?_
  obtain ⟨U, hU, hyU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
  have hey : e y ∈ f ⁻¹ᵁ U := by
    change f (e y) ∈ U
    simpa [← Scheme.Hom.comp_apply, he] using hyU
  obtain ⟨V, hV, heyV, hVU⟩ := exists_isAffineOpen_mem_and_subset hey
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have hVU' : V ≤ f ⁻¹ᵁ U := hVU
  let fV : V.toScheme ⟶ U.toScheme := f.resLE U V hVU'
  let eU : U.toScheme ⟶ X := U.ι ≫ e
  have hyV : (⟨y, hyU⟩ : U) ∈ eU ⁻¹ᵁ V := heyV
  obtain ⟨T, hT, hyT, hTV⟩ := exists_isAffineOpen_mem_and_subset hyV
  let : IsAffine T.toScheme := hT
  let j : T.toScheme ⟶ Y := T.ι ≫ U.ι
  let a : T.toScheme ⟶ V.toScheme :=
    IsOpenImmersion.lift V.ι (j ≫ e) (by
      rintro _ ⟨t, rfl⟩
      exact ⟨⟨(j ≫ e) t, hTV t.property⟩, rfl⟩)
  have ha : a ≫ V.ι = j ≫ e := IsOpenImmersion.lift_fac _ _ _
  have haf : a ≫ fV = T.ι := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc]
    change a ≫ (f.resLE U V hVU' ≫ U.ι) = T.ι ≫ U.ι
    rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, ha]
    simp [j, Category.assoc, he]
  let W : Scheme.{u} := pullback fV T.ι
  let k : W ⟶ X := pullback.fst fV T.ι ≫ V.ι
  let p : W ⟶ T.toScheme := pullback.snd fV T.ι
  let s : T.toScheme ⟶ W := pullback.lift a (𝟙 _) (by simpa using haf)
  refine
    ⟨{
      base := T.toScheme
      total := W
      baseι := j
      totalι := k
      hom := p
      sectionMap := s
      mem_base := ⟨⟨⟨y, hyU⟩, hyT⟩, rfl⟩
      comm := ?_
      section_comp := ?_
      section_hom := ?_ }⟩
  · dsimp [k, p, j]
    rw [Category.assoc, ← Scheme.Hom.resLE_comp_ι f hVU', ← Category.assoc,
      pullback.condition, Category.assoc]
  · dsimp [s, k]
    rw [← Category.assoc, pullback.lift_fst]
    exact ha
  · exact pullback.lift_snd _ _ _

namespace AffineSectionNeighbourhood

variable {f e} {y : Y} (N : AffineSectionNeighbourhood f e y)

/-- Properties local at the source and stable under base change restrict
to the neighbourhood morphism. -/
theorem property_hom (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P] [P.IsStableUnderBaseChange] (hf : P f) :
    P N.hom := by
  apply P.of_postcomp N.hom N.baseι (inferInstance : IsOpenImmersion N.baseι)
  rw [← N.comm]
  exact IsZariskiLocalAtSource.comp hf N.totalι

instance [Smooth f] : Smooth N.hom := by
  let : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth) (Q := RingHom.Smooth)
  exact N.property_hom @Smooth inferInstance

instance [LocallyOfFinitePresentation f] : LocallyOfFinitePresentation N.hom := by
  let : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @LocallyOfFinitePresentation) (Q := RingHom.FinitePresentation)
  exact N.property_hom @LocallyOfFinitePresentation inferInstance

instance : QuasiCompact N.hom := inferInstance

instance : QuasiSeparated N.hom := inferInstance

end AffineSectionNeighbourhood

end Langlands.AlgebraicGeometry

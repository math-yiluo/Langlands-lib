import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent

/-! # Immersions descend under surjective étale base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ImmersionEtaleDescent

variable {X Y U P : Scheme.{u}}

/-- The canonical open neighbourhood in which a locally closed image is closed,
constructed before any scheme-theoretic immersion property is available. -/
def rangeNeighbourhood (f : X ⟶ Y) (h : IsLocallyClosed (Set.range f)) : Y.Opens :=
  ⟨coborder (Set.range f), h.isOpen_coborder⟩

/-- Immersion of a morphism reflects along any surjective étale target base
change, expressed by a supplied cartesian square. -/
theorem isImmersion_of_isPullback
    {a : P ⟶ X} {b : P ⟶ U} {f : X ⟶ Y} {p : U ⟶ Y}
    (h : IsPullback a b f p) [Etale p] [Surjective p] [IsImmersion b] :
    IsImmersion f := by
  have hrange : Set.range b = p ⁻¹' Set.range f := by
    simpa using Scheme.image_preimage_eq_of_isPullback h Set.univ
  have hloc : IsLocallyClosed (Set.range f) := by
    apply isLocallyClosed_iff_isOpen_coborder.mpr
    rw [← (p.isOpenMap.isQuotientMap p.continuous p.surjective).isOpen_preimage]
    have hc : p ⁻¹' coborder (Set.range f) = coborder (p ⁻¹' Set.range f) := by
      simp only [coborder, Set.preimage_compl, Set.preimage_sdiff,
        p.isOpenMap.preimage_closure_eq_closure_preimage p.continuous]
    rw [hc, ← hrange]
    exact b.isLocallyClosed_range.isOpen_coborder
  let W := rangeNeighbourhood f hloc
  let fW : X ⟶ W := IsOpenImmersion.lift W.ι f (by
    rw [Scheme.Opens.range_ι]
    change Set.range f ⊆ coborder (Set.range f)
    exact subset_coborder)
  have hfW : fW ≫ W.ι = f := IsOpenImmersion.lift_fac _ _ _
  have hclosed : IsClosed (Set.range fW) := by
    have he : W.ι ⁻¹' Set.range f = Set.range fW := by
      rw [← hfW]
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.preimage_image_eq _ W.ι.isOpenEmbedding.injective]
    rw [← he]
    exact isClosed_preimage_val_coborder
  let pW := p ∣_ W
  have : Surjective pW :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (isPullback_morphismRestrict p W).flip inferInstance
  let k := pullback.snd fW pW
  have houter : IsPullback (pullback.fst fW pW)
      (k ≫ (p ⁻¹ᵁ W).ι) f p := by
    have ht := (IsPullback.of_hasPullback fW pW).paste_vert
      (isPullback_morphismRestrict p W)
    rwa [hfW] at ht
  let e := houter.isoIsPullback _ _ h
  have hek : e.hom ≫ b = k ≫ (p ⁻¹ᵁ W).ι :=
    houter.isoIsPullback_hom_snd _ _ h
  have : IsImmersion (k ≫ (p ⁻¹ᵁ W).ι) := by
    rw [← hek]
    infer_instance
  have : IsImmersion k := IsImmersion.of_comp k (p ⁻¹ᵁ W).ι
  have hk : IsClosed (Set.range k) := by
    have he : Set.range k = pW ⁻¹' Set.range fW := by
      simpa only [k, Set.preimage_univ, Set.image_univ] using
        Scheme.image_preimage_eq_of_isPullback
          (IsPullback.of_hasPullback fW pW) Set.univ
    rw [he]
    exact hclosed.preimage pW.continuous
  have : IsClosedImmersion k := IsClosedImmersion.of_isPreimmersion k hk
  have : IsClosedImmersion fW :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @IsClosedImmersion) (Q := @Etale ⊓ @Surjective)
      (IsPullback.of_hasPullback fW pW).flip ⟨inferInstance, inferInstance⟩ inferInstance
  rw [← hfW]
  infer_instance

end Langlands.AlgebraicGeometry.ImmersionEtaleDescent

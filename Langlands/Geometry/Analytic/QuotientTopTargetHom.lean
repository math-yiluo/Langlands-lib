import Langlands.Geometry.Analytic.RefiningTopTargetExtension

/-! # Global strong maps to greatest-chart targets compute quotient Homs -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation.SourceCategory

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : SaturatedAtlasPresentation.{u, v, w} K}
  (t : B.presentation.atlas.Index)
  (ht : ∀ j, Set.range (B.presentation.atlas.chart j) ⊆
    Set.range (B.presentation.atlas.chart t))

/-- Extending a complete numerator on a refining original source gives
exactly its original source-quotient class. -/
theorem strongFunctor_map_extendTop (P : A.presentation.atlas.RefiningSelection)
    (g : A.refiningSubpresentation P ⟶ B) :
    strongFunctor.map (g.extendTop t ht : A ⟶ B) = sourceHomι P g := by
  rw [strongFunctor_map_eq_ι P,
    refiningSubatlasInclusion_comp_eq_restrictSubatlasSource]
  exact congrArg (sourceHomι P) (g.extendTop_restrictSubatlasSource t ht)

include t ht in
/-- Every actual quotient arrow to a greatest-chart target is the image
of a global complete strong map on its unchanged original source. -/
theorem strongFunctor_map_surjective_of_top :
    Function.Surjective (fun f : A ⟶ B => strongFunctor.map f) := by
  intro F
  change SourceHomQuotient A B at F
  refine Quotient.inductionOn F ?_
  rintro ⟨P, g⟩
  exact ⟨g.extendTop t ht, strongFunctor_map_extendTop t ht P g⟩

/-- The actual strong Hom and source-quotient Hom are equivalent whenever
the target has a greatest original chart. -/
def topTargetHomEquiv : (A ⟶ B) ≃ (ofPresentation A ⟶ ofPresentation B) :=
  Equiv.ofBijective (fun f => strongFunctor.map f)
    ⟨strongFunctor_map_injective, strongFunctor_map_surjective_of_top t ht⟩

@[simp]
theorem topTargetHomEquiv_apply (f : A ⟶ B) :
    topTargetHomEquiv t ht f = strongFunctor.map f := rfl

/-- The recovered global strong map represents precisely the input arrow. -/
@[simp]
theorem strongFunctor_map_topTargetHomEquiv_symm
    (F : ofPresentation A ⟶ ofPresentation B) :
    strongFunctor.map ((topTargetHomEquiv t ht).symm F) = F :=
  (topTargetHomEquiv t ht).apply_symm_apply F

/-- On every actual numerator the inverse is the constructed strong
extension, including all admissible bounded algebra pullbacks. -/
@[simp]
theorem topTargetHomEquiv_symm_ι (P : A.presentation.atlas.RefiningSelection)
    (g : A.refiningSubpresentation P ⟶ B) :
    (topTargetHomEquiv t ht).symm (sourceHomι P g) = g.extendTop t ht := by
  apply strongFunctor_map_injective
  exact (strongFunctor_map_topTargetHomEquiv_symm t ht _).trans
    (strongFunctor_map_extendTop t ht P g).symm

/-- Any greatest-chart choice gives the same Hom equivalence, since its
forward map is the fixed original strong-map functor. -/
theorem topTargetHomEquiv_eq (t' : B.presentation.atlas.Index)
    (ht' : ∀ j, Set.range (B.presentation.atlas.chart j) ⊆
      Set.range (B.presentation.atlas.chart t')) :
    topTargetHomEquiv (A := A) t ht = topTargetHomEquiv t' ht' := by
  apply Equiv.ext
  intro f
  rfl

/-- Recovery preserves the full continuous map carried by the quotient. -/
theorem topTargetHomEquiv_symm_spaceMap
    (F : ofPresentation A ⟶ ofPresentation B) :
    TopCat.ofHom ((topTargetHomEquiv t ht).symm F).baseMap = spaceFunctor.map F := by
  exact (spaceFunctor_map_strong ((topTargetHomEquiv t ht).symm F)).symm.trans
    (congrArg (fun q : ofPresentation A ⟶ ofPresentation B => spaceFunctor.map q)
      (strongFunctor_map_topTargetHomEquiv_symm t ht F))

/-- Inverse recovery commutes with precomposition by an arbitrary global
complete strong source map; no greatest chart in that source is needed. -/
theorem topTargetHomEquiv_symm_precomp (f : C ⟶ A)
    (F : ofPresentation A ⟶ ofPresentation B) :
    (topTargetHomEquiv t ht).symm (strongFunctor.map f ≫ F) =
      f ≫ (topTargetHomEquiv t ht).symm F := by
  apply strongFunctor_map_injective (A := C) (B := B)
  exact (strongFunctor_map_topTargetHomEquiv_symm t ht _).trans
    ((congrArg (fun q : ofPresentation A ⟶ ofPresentation B => strongFunctor.map f ≫ q)
      (strongFunctor_map_topTargetHomEquiv_symm t ht F).symm).trans
        (strongFunctor.map_comp f ((topTargetHomEquiv t ht).symm F)).symm)

variable (s : C.presentation.atlas.Index)
  (hs : ∀ j, Set.range (C.presentation.atlas.chart j) ⊆
    Set.range (C.presentation.atlas.chart s))

/-- Inverse recovery commutes with postcomposition by any global complete
strong target map between greatest-chart targets. -/
theorem topTargetHomEquiv_symm_postcomp
    (F : ofPresentation A ⟶ ofPresentation B) (g : B ⟶ C) :
    (topTargetHomEquiv s hs).symm (F ≫ strongFunctor.map g) =
      (topTargetHomEquiv t ht).symm F ≫ g := by
  apply strongFunctor_map_injective (A := A) (B := C)
  exact (strongFunctor_map_topTargetHomEquiv_symm s hs _).trans
    ((congrArg (fun q : ofPresentation A ⟶ ofPresentation B => q ≫ strongFunctor.map g)
      (strongFunctor_map_topTargetHomEquiv_symm t ht F).symm).trans
        (strongFunctor.map_comp ((topTargetHomEquiv t ht).symm F) g).symm)

/-- The inverse computes actual strong composition for arbitrary quotient
arrows whose intermediate and final targets have greatest charts. -/
theorem topTargetHomEquiv_symm_comp
    (F : ofPresentation A ⟶ ofPresentation B)
    (G : ofPresentation B ⟶ ofPresentation C) :
    (topTargetHomEquiv s hs).symm (F ≫ G) =
      (topTargetHomEquiv t ht).symm F ≫ (topTargetHomEquiv s hs).symm G := by
  apply strongFunctor_map_injective (A := A) (B := C)
  exact (strongFunctor_map_topTargetHomEquiv_symm s hs _).trans
    ((congrArg₂ (fun (q : ofPresentation A ⟶ ofPresentation B)
      (r : ofPresentation B ⟶ ofPresentation C) => q ≫ r)
      (strongFunctor_map_topTargetHomEquiv_symm t ht F).symm
      (strongFunctor_map_topTargetHomEquiv_symm s hs G).symm).trans
        (strongFunctor.map_comp ((topTargetHomEquiv t ht).symm F)
          ((topTargetHomEquiv s hs).symm G)).symm)

end Langlands.Analytic.SaturatedAtlasPresentation.SourceCategory

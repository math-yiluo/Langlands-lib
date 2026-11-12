import Langlands.Representation.Compact.CompactBlockDecompositionStatements
import Langlands.Representation.Compact.CompactPartExhaustion
import Langlands.Representation.CompactCoefficient.AdmissibleComplement
import Langlands.Representation.Category.ConstituentSerre

/-! # Compact irreducibles and the semisimple compact subcategory -/

noncomputable section

universe u v

open CategoryTheory MeasureTheory

namespace Langlands.Renard.CompactRepresentation

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- Dual projectivity gives injectivity of a compact irreducible, with independent
universes for the group and the representation carriers. -/
theorem injective_of_irreducible_compactCoefficients (μ : Measure G) [μ.IsHaarMeasure]
    (τ : SmoothRep.{0, u, v} ℂ G) (hirr : τ.IsIrreducible)
    (hc : HasCompactSmoothDualCoefficients τ.representation) : Injective τ := by
  have hcof : ∀ K : OpenSubgroup G,
      ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hLK, hL, -⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ K
    exact ⟨L, hL, hLK⟩
  have ha := CompactSplitting.isAdmissible_of_compactCoefficients μ hcof
    τ.representation τ.isSmooth hirr hc
  let dual (A : SmoothRep.{0, u, v} ℂ G) : SmoothRep.{0, u, v} ℂ G :=
    SmoothRep.of (smoothContragredient A.representation)
      (isSmooth_smoothContragredient A.representation)
  have hdirr : (dual τ).IsIrreducible :=
    CompactSplitting.isIrreducible_smoothContragredient hcof τ.representation ha hirr
  have hdc : HasCompactSmoothDualCoefficients (dual τ).representation :=
    CompactSplitting.hasCompactSmoothDualCoefficients_smoothContragredient
      hcof τ.representation ha hc
  let : Projective (dual τ) :=
    CompactCoefficient.projective_of_hasCompactSmoothDualCoefficients (dual τ) hdirr hdc
  have hb := CompactSplitting.smoothBidual_bijective_of_compact_cofinal
    hcof τ.representation ha
  refine ⟨fun {X Y} f i hi => ?_⟩
  let q : dual Y ⟶ dual X := SmoothRep.ofHom (contragredientMap (SmoothRep.hom i))
  let fd : dual τ ⟶ dual X := SmoothRep.ofHom (contragredientMap (SmoothRep.hom f))
  let : Epi q := (SmoothRep.epi_iff_surjective q).mpr
    (contragredientMap_surjective_of_injective_of_compact_cofinal hcof
      X.isSmooth Y.isSmooth (SmoothRep.hom i) ((SmoothRep.mono_iff_injective i).mp hi))
  let t : dual τ ⟶ dual Y := Projective.factorThru fd q
  have ht : t ≫ q = fd := Projective.factorThru_comp fd q
  obtain ⟨r, hr⟩ := (contragredientMap_bijective_of_bidual Y.isSmooth τ.isSmooth hb).2
    (SmoothRep.hom t)
  change contragredientMap r = SmoothRep.hom t at hr
  refine ⟨SmoothRep.ofHom r, ?_⟩
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply (contragredientMap_bijective_of_bidual X.isSmooth τ.isSmooth hb).1
  change contragredientMap (r.comp (SmoothRep.hom i)) = contragredientMap (SmoothRep.hom f)
  rw [contragredientMap_comp, hr]
  exact congrArg SmoothRep.hom ht

/-- Renard IV.1.6: compact irreducibles are projective and injective in the
ambient smooth category. -/
theorem compactProjectiveInjective : CompactProjectiveInjectiveStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ _ μ _ _ _ τ hirr hc
  exact ⟨CompactCoefficient.projective_of_hasCompactSmoothDualCoefficients τ hirr hc,
    injective_of_irreducible_compactCoefficients μ τ hirr hc⟩

/-- Renard IV.1.6: the compact constituent subcategory is semisimple, with
projective and injective simple objects. -/
theorem compactPartSemisimple : CompactPartSemisimpleStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ _ μ _ _ _
  constructor
  · intro A hA
    exact CompactCoefficientSemisimplicity.isSemisimpleRepresentation_of_compactCoefficients
      μ A.representation A.isSmooth
      (compactCoefficients_of_compact_irreducible_subquotients A hA)
  · intro A hA hirr
    have hc := compactCoefficients_of_compact_irreducible_subquotients A hA
    let P : ObjectProperty (SmoothRep.{0, u, v} ℂ G) :=
      fun B => HasCompactSmoothDualCoefficients B.representation
    change Projective (C := (SmoothRep.irreducibleSubquotientsProperty P).FullSubcategory)
      ⟨A, hA⟩ ∧ Injective (C := (SmoothRep.irreducibleSubquotientsProperty P).FullSubcategory)
      ⟨A, hA⟩
    exact ⟨(SmoothRep.irreducibleSubquotientsProperty P).ι.projective_of_map_projective
      (CompactCoefficient.projective_of_hasCompactSmoothDualCoefficients A hirr hc),
      (SmoothRep.irreducibleSubquotientsProperty P).ι.injective_of_map_injective
        (injective_of_irreducible_compactCoefficients μ A hirr hc)⟩

end Langlands.Renard.CompactRepresentation

import Langlands.AlgebraicGeometry.AlgebraicSpace.FinitePresentationChartSquares
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasSchemeCompatibilityProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyUniqueness

/-! # Structural finiteness recovered from a represented algebraic space -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The diagonal in the slice product is the scheme diagonal through the
canonical comparison of that product with the scheme fibre product. -/
def schemeDiagonalArrowIso (U : Over S) :
    Arrow.mk (prod.lift (𝟙 U) (𝟙 U)).left ≅
      Arrow.mk (pullback.diagonal U.hom) :=
  Arrow.isoMk (Iso.refl _) (Over.prodLeftIsoPullback U U) (by
    apply pullback.hom_ext
    · simp only [Arrow.mk_hom, Category.assoc, Over.prodLeftIsoPullback_hom_fst,
        pullback.diagonal_fst, Iso.refl_hom, Category.id_comp]
      change 𝟙 _ = ((prod.lift (𝟙 U) (𝟙 U)) ≫ prod.fst).left
      simp
    · simp only [Arrow.mk_hom, Category.assoc, Over.prodLeftIsoPullback_hom_snd,
        pullback.diagonal_snd, Iso.refl_hom, Category.id_comp]
      change 𝟙 _ = ((prod.lift (𝟙 U) (𝟙 U)) ≫ prod.snd).left
      simp)

/-- The space diagonal of a represented scheme is quasi-compact exactly
when the structure morphism of that scheme is quasi-separated. -/
theorem isQuasiSeparated_schemeToSpace_iff (U : Over S) :
    IsQuasiSeparated ((schemeToSpace S).obj U) ↔ QuasiSeparated U.hom := by
  constructor
  · intro hU
    have hqc : QuasiCompact (prod.lift (𝟙 U) (𝟙 U)).left :=
      relative_diagonal_property_chart_pairing @QuasiCompact hU (𝟙 U) (𝟙 U)
        (𝟙 _) (𝟙 _) (by
          simpa using (IsPullback.of_horiz_isIso
            (fst := 𝟙 ((schemeYoneda S).obj U)) (snd := 𝟙 _)
            (f := 𝟙 _) (g := 𝟙 _) ⟨by simp⟩))
    exact ⟨(MorphismProperty.arrow_mk_iso_iff @QuasiCompact
      (schemeDiagonalArrowIso U)).mp hqc⟩
  · intro hU
    let := hU
    exact isQuasiSeparated_schemeToSpace U

/-- Over an affine base the finite-presentation atlas condition on a
represented scheme is exactly LFP and QC of its actual structure map. -/
theorem finitePresentationAtlas_schemeToSpace_iff [IsAffine S] (U : Over S) :
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u})
        ((schemeToSpace S).obj U) ↔
      LocallyOfFinitePresentation U.hom ∧ QuasiCompact U.hom := by
  constructor
  · intro hU
    have hlfp : LocallyOfFinitePresentation U.hom :=
      (locallyOfFinitePresentationOverBase_schemeToSpace_iff U).mp
        (hU.mono inf_le_left)
    obtain ⟨W, a, ha, hs, _, hWqc⟩ := hU
    let := hWqc
    have : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace W.hom
    obtain ⟨f, _, hfS⟩ := exists_etale_surjective_of_represented_atlas a ha hs
    have : CompactSpace U.left :=
      Function.Surjective.compactSpace f.left.continuous hfS.surj
    exact ⟨hlfp, inferInstance⟩
  · intro h
    exact HasAtlasProperty.of_scheme
      (P := @LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) U h

/-- A scheme representing a quasi-separated space with a finite-presentation
atlas over an affine base has all three actual scheme finiteness properties. -/
theorem schemeFiniteness_of_presheafIso [IsAffine S] (X : AlgebraicSpace S)
    (hXqs : IsQuasiSeparated X)
    (hXfp : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (U : Over S) (e : X.presheaf ≅ (schemeYoneda S).obj U) :
    LocallyOfFinitePresentation U.hom ∧ QuasiCompact U.hom ∧ QuasiSeparated U.hom := by
  have hUqs : IsQuasiSeparated ((schemeToSpace S).obj U) :=
    relative_diag_of_iso @QuasiCompact e hXqs
  obtain ⟨hlfp, hqc⟩ := (finitePresentationAtlas_schemeToSpace_iff U).mp
    (hXfp.of_iso e)
  exact ⟨hlfp, hqc, (isQuasiSeparated_schemeToSpace_iff U).mp hUqs⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace

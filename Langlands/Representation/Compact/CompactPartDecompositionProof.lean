import Langlands.Representation.Compact.CompactIsotypicSplittingProof
import Langlands.Representation.Compact.CompactPartExhaustion
import Langlands.Representation.Compact.ProjectorCofan

/-! # Decomposition of the compact subcategory into compact isotypic parts -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MeasureTheory
open Langlands.CompactCoefficientClass

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.1.7: every compact-part object is the coproduct of its actual
compact-isotypic parts, within the compact full subcategory. -/
theorem compactPartDecomposition : CompactPartDecompositionStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ _ μ _ _ _
  constructor
  · intro A
    let e (c : CompactCoefficientClass.{u, v} G) := blockProjector μ c A.obj
    have hid (c : CompactCoefficientClass.{u, v} G) (x : A.obj) : e c (e c x) = e c x :=
      blockProjector_idempotent μ c A.obj x
    have horth (c d : CompactCoefficientClass.{u, v} G) (hcd : c ≠ d) (x : A.obj) :
        e c (e d x) = 0 := blockProjector_orthogonal μ hcd A.obj x
    have hspan : (⨆ c, (e c).range) = ⊤ := by
      simp only [e, blockProjector_range]
      exact totalIsotypic_eq_top_of_compact_irreducible_subquotients A.obj A.property
    let hf := SmoothRep.finiteSupport_projectors_of_iSup_range_eq_top A.obj e horth hspan
    have hsum := SmoothRep.finsum_projectors_eq_self_of_iSup_range_eq_top
      A.obj e hf hid horth hspan
    have hcomp (c : CompactCoefficientClass.{u, v} G) :
        compactPart G (SmoothRep.subrepresentation A.obj (e c).range) := by
      intro D hD hDC
      exact A.property D hD (smoothSubquotientTransitivity ℂ G _ _ D hDC
        (SmoothRep.subrepresentation_isSubrepresentation (e c).range).isSubquotient)
    let Y (c : CompactCoefficientClass.{u, v} G) : (compactPart G).FullSubcategory :=
      ⟨SmoothRep.subrepresentation A.obj (e c).range, hcomp c⟩
    let j (c : CompactCoefficientClass.{u, v} G) : Y c ⟶ A :=
      ObjectProperty.homMk (SmoothRep.subtype A.obj (e c).range)
    have hcol := SmoothRep.projectorRangeCofanIsColimit A.obj e hf hid horth hsum
    refine ⟨Y, j, (fun c => isotypicPart_blockProjector_range μ c A.obj), ⟨?_⟩⟩
    refine Cofan.IsColimit.mk _ (fun s => ObjectProperty.homMk
      (hcol.desc (Cofan.mk s.pt.obj (fun c => (s.inj c).hom)))) ?_ ?_
    · intro s c
      apply ObjectProperty.hom_ext
      exact Cofan.IsColimit.fac hcol (fun c => (s.inj c).hom) c
    · intro s m hm
      apply ObjectProperty.hom_ext
      apply Cofan.IsColimit.hom_ext hcol
      intro c
      exact (congrArg InducedCategory.Hom.hom (hm c)).trans
        (Cofan.IsColimit.fac hcol (fun c => (s.inj c).hom) c).symm
  · intro c d hcd A B hA hB f
    apply ObjectProperty.hom_ext
    exact hom_eq_zero_of_isotypicPart_ne μ hcd hA hB f.hom

end Langlands.Renard.CompactRepresentation

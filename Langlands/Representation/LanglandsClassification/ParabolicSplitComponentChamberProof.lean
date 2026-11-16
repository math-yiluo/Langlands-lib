import Langlands.Representation.LanglandsClassification.ParabolicChamberStatements
import Langlands.Representation.LanglandsClassification.ParabolicChamberLinearAlgebraProof
import Langlands.Representation.LanglandsClassification.ParabolicSplitComponentTransport
import Langlands.Representation.LanglandsClassification.ParabolicSplitComponentCorootCones
import Langlands.GroupScheme.Rational.StandardLeviCentralDirectionsProof
import Langlands.GroupScheme.Rational.StandardLeviRealDecompositionProof
import Langlands.GroupScheme.Rational.RelativeFundamentalWeightProof

/-! # Split-component chamber comparison from ambient linear algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

open RealTorusSpace

/-- Transport the ambient chamber theorem to each actual standard-Levi split component. -/
theorem parabolicSplitComponentChamber_of_linearAlgebra
    (hLA : ParabolicChamberLinearAlgebraStatement.{u})
    (hDec : StandardLeviRealDecompositionStatement.{u})
    (hFW : RelativeFundamentalWeightStatement.{u}) :
    ParabolicSplitComponentChamberStatement.{u} := by
  intro k _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  intro ν hν D J hJ L j hj hrepr A a ha f hf
  obtain ⟨-, f', hf', -, hinj, hrange, -⟩ :=
    (standardLeviCentralDirections.2 k G hG T i hi ν hν J hJ L j hj hrepr).2 A a ha
  have he : f' = f := eq_of_groupHom_comp_eq i j hf' hf
  subst f'
  have hA : IsSplitTorus A.toGrp := ha.1.1.1
  have hT : IsSplitTorus T.toGrp := hi.1.1
  have hLAJ := hLA k G hG T i hi ν hν D J hJ
  have hcomp := (hDec k G hG T i hi ν hν D).2.2.2 J J (Set.Subset.refl J) hJ
  have hfw := hFW k G hG T i hi ν hν D
  have hbij := splitComponent_restrict_bijOn (D := D) hA hT hinj hrange hcomp.1
  have hroot : ∀ α ∈ simpleRelativeRoots i ν \ J, ∃ y, y ∈ D.projectedRoots J {α} :=
    fun α hα => (hLAJ.1 α hα).1.exists
  have hcoroot : ∀ α ∈ simpleRelativeRoots i ν \ J, ∃ v, v ∈ D.projectedCoroots J {α} :=
    fun α hα => (hLAJ.1 α hα).2.exists
  have hsep := splitComponent_root_injective hA hT hrange hbij hroot hLAJ.2.1
  obtain ⟨b, hb, -, -, hopenDesc, hclosedDesc⟩ := hLAJ.2.2.1
  obtain ⟨bV, hbV⟩ := hLAJ.2.2.2.1
  have hopen := splitComponent_openChamber_eq hbij hrange hcoroot
  have hclosed := splitComponent_closedChamber_eq hbij hrange hcoroot
  have hlift : ∀ α ∈ simpleRelativeRoots i ν \ J,
      ∃ w : V A, cocharacterMapReal f w ∈ D.projectedCoroots J {α} := by
    intro α hα
    obtain ⟨v, hv⟩ := hcoroot α hα
    obtain ⟨w, hw⟩ := (show v ∈ (cocharacterMapReal f).range from hrange ▸ hv.1)
    exact ⟨w, hw.symm ▸ hv⟩
  have hfin : (simpleRelativeRoots i ν).Finite := by
    have h := (standardLeviCentralDirections.1 k G hG T i hi ν hν
      (simpleRelativeRoots i ν) (Set.Subset.refl _)).1
    exact Set.toFinite _
  refine ⟨hbij, restrict_image_parabolicRoots hA hT hrange hroot, hsep,
    splitComponent_coroot_existsUnique hinj hrange (fun α hα => (hLAJ.1 α hα).2) hsep,
    splitComponent_fundamentalCoweight_existsUnique hJ hinj hrange
      (fun α hα => ⟨bV ⟨α, hα⟩, hbV ⟨α, hα⟩⟩) hfw.2.2.2.2,
    hopen, hclosed, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hopen, restrictedCorootChamber_eq_image_openFace]
    exact splitComponent_image_weight_description (0 < ·) (fun α => (b α : Vstar T))
      hb hfw.2.2.2.1 hopenDesc
  · rw [hclosed, restrictedClosedCorootChamber_eq_image]
    exact splitComponent_image_weight_description (0 ≤ ·) (fun α => (b α : Vstar T))
      hb hfw.2.2.2.1 hclosedDesc
  · ext v
    exact splitComponent_corootCombination_iff hinj hrange hcomp.2.1 hlift hsep (0 < ·) v
  · ext v
    change cocharacterMapReal f v ∈
      projectedCorootNonnegCone i D J (simpleRelativeRoots i ν \ J) ↔ _
    rw [projectedCorootNonnegCone_iff_family (hfin.subset Set.sdiff_subset)]
    exact splitComponent_corootCombination_iff hinj hrange hcomp.2.1 hlift hsep (0 ≤ ·) v
  · intro hfin'
    exact ⟨splitComponent_image_rootPositiveCone hA hT hrange hbij hfin',
      splitComponent_image_rootNonnegCone hA hT hrange hbij hfin'⟩

/-- Renard V.3.14–V.3.15 on each compatible standard-Levi split component. -/
theorem parabolicSplitComponentChamber : ParabolicSplitComponentChamberStatement.{u} :=
  parabolicSplitComponentChamber_of_linearAlgebra
    parabolicChamberLinearAlgebra standardLeviRealDecomposition relativeFundamentalWeight

end Langlands.GroupScheme

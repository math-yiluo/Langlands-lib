import Langlands.Cohomology.SmoothGodementComparison.Statement
import Langlands.Cohomology.AcyclicResolution.Comparison

/-!
# The degree-zero smooth Godement comparison map

For a smooth equivariant module sheaf `F`, an injective resolution `I` of `F` and an
augmentation-compatible cochain map `φ` from the smooth Godement complex of `F` to `I`, the
degree-zero comparison map from compactly supported smooth Godement cohomology to derived
compact sections is the composite of the published identifications of both sides with compact
sections. This proves `SmoothGodementComparisonZeroStatement`.
-/

noncomputable section

namespace Langlands.Cohomology.SmoothGodementComparison

open CategoryTheory CategoryTheory.Limits Langlands.Sheaf.Equivariant

universe u

/-- In degree zero, the comparison map induced by an augmentation-compatible lift is the
composite of the identifications of both sides with compact sections. -/
theorem smoothGodementComparisonZero (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
    [HasStableNeighbourhoods G X] : SmoothGodementComparisonZeroStatement R G X := by
  intro F I φ hφ
  have hT := AcyclicResolution.toRightDerivedZero_eq_comparison
    (smoothSheafCompactSections R G X)
    (CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
      (Godement.smoothCoaugmentation R G X) F) I φ hφ
  have hc : AcyclicResolution.toCyclesZero (smoothSheafCompactSections R G X)
      (CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
        (Godement.smoothCoaugmentation R G X) F) =
      (EquivariantGodementCohomology.cyclesIso (Godement.smoothZeroFunctor R G X)
        (Godement.smoothCoaugmentation R G X) (smoothSheafCompactSections R G X) F).hom := by
    rw [← cancel_mono (HomologicalComplex.iCycles _ 0), AcyclicResolution.toCyclesZero_iCycles,
      CokernelComplex.augmentationMap_f_zero]
    exact (EquivariantGodementCohomology.cyclesIso_hom_iCycles _ _ _ F).symm
  change comparisonMap R G X I φ 0 =
    (EquivariantGodementCohomology.homologyIso (Godement.smoothZeroFunctor R G X)
        (Godement.smoothCoaugmentation R G X) (smoothSheafCompactSections R G X) F).inv ≫
      (smoothSheafCompactSections R G X).toRightDerivedZero.app F
  rw [hT, hc, EquivariantGodementCohomology.homologyIso, Iso.trans_inv, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact (Iso.inv_hom_id_assoc _ _).symm

end Langlands.Cohomology.SmoothGodementComparison

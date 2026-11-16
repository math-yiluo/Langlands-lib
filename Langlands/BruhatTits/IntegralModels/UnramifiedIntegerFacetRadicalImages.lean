import Langlands.BruhatTits.IntegralModels.UnramifiedIntegerFacetParabolicBijection
import Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationProof
import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentParabolicImage
import Langlands.BruhatTits.IntegralModels.UnramifiedRadicalConjugation
import Langlands.BruhatTits.IntegralModels.DepthZeroCompactOpen

/-! # Actual incident radical images and the full integer-facet parabolic bijection -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels.IntegerFacetModelData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
  [IsAffineHom G.X.hom]
  (E : UnramifiedZeroDatum F G) (C : MaximalUnramified.BuildingData F G)
  (M : IntegerFacetModelData C (fixedFieldIntegers F))
  (hsource : ∀ J : C.BuildingFacet,
    (M.model J).neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer J.val)
  (Fc : C.BuildingFacet) (Q : SpecialFibreQuotientData (M.model Fc))

include hsource in
/-- The actual target radical preimage is integral in every incident source,
and the actual neutral special-fibre image is parabolic. -/
theorem unramifiedIntegerFacet_positivePoints_le_and_isParabolic
    (hQ : Q.IsReductiveQuotient) (J : C.IncidentFacets Fc) :
    Q.positivePoints ≤ (M.model J.val).neutral.integralPoints ∧
      (M.morphism Fc J.val J.property).HasParabolicSpecialFibreImage := by
  obtain ⟨g, Fa, Ca, hFaCa, hFc, hJ⟩ := J.property
  have hCa : AffineRootSystem.IsFacet C.affineRoots Ca := by
    obtain ⟨a, ha, _⟩ := hFaCa.2
    exact ⟨a, ha⟩
  have hneFa : Fa.Nonempty := by
    obtain ⟨a, ha⟩ := hFaCa.1
    exact ha ▸ ⟨a, AffineRootSystem.mem_facet_self _ _⟩
  have hneCa : Ca.Nonempty := by
    obtain ⟨a, ha⟩ := hCa
    exact ha ▸ ⟨a, AffineRootSystem.mem_facet_self _ _⟩
  have hsingle : ∃ a : C.Apartment,
      Fa ⊆ AffineRootSystem.facet C.affineRoots a := by
    obtain ⟨a, ha⟩ := hFaCa.1
    exact ⟨a, by rw [ha]⟩
  let f := G.innerIso g⁻¹
  let N := (M.model Fc).transport f
  let N' := (M.model J.val).transport f
  let Q' := Q.transport f
  let φ := (M.morphism Fc J.val J.property).transport f
  have hN : N.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Fa) := by
    apply IntegralModel.integralPoints_transport_innerIso_same_zeroDatum C E g Fa
    rw [hsource Fc, hFc]
    rfl
  have hN' : N'.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ca) := by
    apply IntegralModel.integralPoints_transport_innerIso_same_zeroDatum C E g Ca
    rw [hsource J.val, hJ]
    rfl
  have hQ' : Q'.IsReductiveQuotient := (Q.isReductiveQuotient_transport_iff f).mpr hQ
  let : Smooth N.neutral.group.X.hom := N.neutral_smooth
  let : Smooth N'.neutral.group.X.hom := N'.neutral_smooth
  let : ConnectedSpace N.neutral.specialFibre.X.left :=
    N.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres N.neutral_connectedFibres
  obtain ⟨H, _, hH, hgenerate⟩ := unramifiedUpstairsRadicalRootGeneration F G C E
  have hgen := hgenerate Fa hneFa hsingle N.neutral N.neutral_smooth hN
    Q'.radical Q'.radicalInclusion hQ'.1
  have hpos : Q'.positivePoints ≤ N'.neutral.integralPoints :=
    unramifiedIncidentReductionPreimage_le_integralPoints C E Fa Ca hCa hFaCa
      hneFa (Set.Subset.refl _) (Set.Subset.refl _) H hH
      N.neutral N'.neutral hN' Q'.radicalInclusion hgen.le
  have hpar : IsParabolicSubgroup (SchematicImage.inclusion φ.neutral.specialFibreMap) :=
    unramifiedIncidentImage_isParabolic_of_rootGeneration C E N.neutral N'.neutral
      Fa Ca hN hN' φ.neutral hCa hFaCa hneFa hneCa
      (Set.Subset.refl _) (Set.Subset.refl _)
      Q'.radicalInclusion hQ'.1 H hH hgen.le
  constructor
  · change (Q.transport f).positivePoints ≤
      ((M.model J.val).neutral.transport f).integralPoints at hpos
    rw [Q.transport_positivePoints, IntegralModel.transport_integralPoints,
      Subgroup.map_le_map_iff_of_injective (rationalPoints_map_injective_of_iso f)] at hpos
    exact hpos
  · exact hpar

include hsource in
/-- Characterized actual full-facet neutral models have the complete original
facet-parabolic order bijection at every valid supplied reductive quotient. -/
theorem hasUnramifiedIntegerFacetParabolicOrderBijection_of_zeroFixers
    (hQ : Q.IsReductiveQuotient) :
    M.HasFacetParabolicOrderBijection Fc Q := by
  apply M.hasUnramifiedIntegerFacetParabolicOrderBijection E C hsource Fc Q hQ
  · intro J
    exact Q.congruenceSubgroup_le_positivePoints.trans
      (M.unramifiedIntegerFacet_positivePoints_le_and_isParabolic E C hsource Fc Q hQ J).1
  · intro J
    exact (M.unramifiedIntegerFacet_positivePoints_le_and_isParabolic E C hsource Fc Q hQ J).2

/-- The actual full integer-facet correspondence, retaining only the model
family, its full neutral characterization and validity of the chosen quotient. -/
def UnramifiedIntegerFacetRadicalImagesStatement : Prop :=
  (∀ J : C.BuildingFacet,
    (M.model J).neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer J.val) →
  Q.IsReductiveQuotient →
  (∀ J : C.IncidentFacets Fc,
    Q.positivePoints ≤ (M.model J.val).neutral.integralPoints ∧
      (M.morphism Fc J.val J.property).HasParabolicSpecialFibreImage) ∧
    M.HasFacetParabolicOrderBijection Fc Q

theorem unramifiedIntegerFacetRadicalImages :
    M.UnramifiedIntegerFacetRadicalImagesStatement E C Fc Q := by
  intro hs hQ
  exact ⟨fun J => M.unramifiedIntegerFacet_positivePoints_le_and_isParabolic
      E C hs Fc Q hQ J,
    M.hasUnramifiedIntegerFacetParabolicOrderBijection_of_zeroFixers E C hs Fc Q hQ⟩

end Langlands.BruhatTits.IntegralModels.IntegerFacetModelData

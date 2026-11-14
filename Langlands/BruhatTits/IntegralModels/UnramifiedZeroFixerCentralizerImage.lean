import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerResidueRoots
import Langlands.BruhatTits.IntegralModels.IntegralTorusCentralizer
import Langlands.Geometry.Building.IntegerBuildingFacetOrder
import Langlands.GroupScheme.IntegralModel.FixedFieldExtension
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof
import Langlands.GroupScheme.IntegralModel.SmoothIntersection
import Langlands.GroupScheme.SchematicImage
import Langlands.GroupScheme.Absolute.ParabolicTransport

/-! # The full residue centralizer lies in zero-fixer comparison images -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    (B : IntegerValuationBuildingData v G)

/-- An actual centralizer point fixing one apartment point fixes every apartment subset. -/
theorem map_centralizer_mem_pointwiseFixer_of_smul_eq
    (z : rationalPoints B.centralizer.Z) (x : B.Apartment)
    (hx : rationalPoints.map B.centralizer.j z • B.apartmentMap x = B.apartmentMap x)
    (Ω : Set B.Apartment) :
    rationalPoints.map B.centralizer.j z ∈ B.pointwiseFixer (B.apartmentMap '' Ω) := by
  have h := B.apartmentMap_injective
    ((B.centralizer_smul_apartmentMap z x).symm.trans hx)
  have hv : (Submodule.Quotient.mk (B.translation z).toAdd : TranslationSpace B.i) = 0 :=
    vadd_right_cancel x (h.trans (zero_vadd _ x).symm)
  apply B.apartment.mem_pointwiseFixer.mpr
  rintro y ⟨w, _, rfl⟩
  rw [B.centralizer_smul_apartmentMap, hv, zero_vadd]

/-- For nonempty apartment subsets, the full fixer has the same centralizer preimage. -/
theorem comap_pointwiseFixer_centralizer_eq
    (Ω Ω' : Set B.Apartment) (hne : Ω.Nonempty) (hne' : Ω'.Nonempty) :
    (B.pointwiseFixer (B.apartmentMap '' Ω)).comap (rationalPoints.map B.centralizer.j) =
      (B.pointwiseFixer (B.apartmentMap '' Ω')).comap (rationalPoints.map B.centralizer.j) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨x, hx⟩ := hne
    exact B.map_centralizer_mem_pointwiseFixer_of_smul_eq z x
      (B.apartment.mem_pointwiseFixer.mp hz _ ⟨x, hx, rfl⟩) Ω'
  · intro z hz
    obtain ⟨x, hx⟩ := hne'
    exact B.map_centralizer_mem_pointwiseFixer_of_smul_eq z x
      (B.apartment.mem_pointwiseFixer.mp hz _ ⟨x, hx, rfl⟩) Ω

end Langlands.Geometry.Building.IntegerValuationBuildingData

namespace Langlands.BruhatTits.IntegralModels

namespace IntegralSplitTorusData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {G Z : GroupScheme (Spec (CommRingCat.of K))}
    {i : S.toGrp ⟶ G} {N : IntegralModel R K G}
    (A : IntegralSplitTorusData N i) [Smooth N.group.X.hom]
    (j : Z ⟶ G) (hj : (torusCentralizer i).IsRepresentedBy j)

/-- The constructed centralizer's actual residue inclusion represents the full residue
centralizer of the actual special torus, on every scheme test. -/
theorem centralizerModelMap_specialFibre_isCentralizer :
    (torusCentralizer (T := A.specialFibreTorus) A.specialFibreInclusion).IsRepresentedBy
      (A.centralizerModelMap j hj).specialFibreMap := by
  have hp := A.centralizer_properties.2.2.baseChange (IntegralModel.residueBaseMap R)
  rw [← torusCentralizer_baseChange] at hp
  exact hp

end IntegralSplitTorusData

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (N M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    [Smooth N.group.X.hom] (Ω Ω' : Set C.Apartment)
    (hN : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hM : M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))

/-- The actual integral centralizer inside the supplied smooth target zero-fixer model. -/
def unramifiedZeroFixerCentralizerModel :
    IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) C.centralizer.Z :=
  (unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN).centralizerModel
    C.centralizer.j C.centralizer.isRepresentedBy

/-- Its original generic centralizer inclusion extends to a closed integral inclusion. -/
def unramifiedZeroFixerCentralizerModelMap :
    (unramifiedZeroFixerCentralizerModel C E N Ω hN).Hom N C.centralizer.j :=
  (unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN).centralizerModelMap
    C.centralizer.j C.centralizer.isRepresentedBy

/-- The actual target centralizer lifts into any second model defined by the same zero
subgroup, as soon as the target apartment subset is nonempty. -/
def unramifiedZeroFixerCentralizerLift (hne : Ω.Nonempty) :
    (unramifiedZeroFixerCentralizerModel C E N Ω hN).Hom M C.centralizer.j := by
  apply Classical.choice
  apply IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F
    C.centralizer.Z G C.centralizer.j
    (unramifiedZeroFixerCentralizerModel C E N Ω hN) M
    ((unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN).centralizerModel_isSmooth
      C.centralizer.j C.centralizer.isRepresentedBy)
  intro z hz
  have hzN := (unramifiedZeroFixerCentralizerModelMap C E N Ω hN).map_mem_integralPoints hz
  rw [hN] at hzN
  rw [hM]
  refine ⟨hzN.1, ?_⟩
  obtain ⟨x, hx⟩ := hne
  exact C.map_centralizer_mem_pointwiseFixer_of_smul_eq z x
    (C.apartment.mem_pointwiseFixer.mp hzN.2 _ ⟨x, hx, rfl⟩) Ω'

/-- Generic rigidity forces the lifted centralizer's composite to be its original inclusion. -/
theorem unramifiedZeroFixerCentralizerLift_comp (hne : Ω.Nonempty)
    (φ : M.Hom N (𝟙 G)) :
    (unramifiedZeroFixerCentralizerLift C E N M Ω Ω' hN hM hne).hom ≫ φ.hom =
      (unramifiedZeroFixerCentralizerModelMap C E N Ω hN).hom := by
  let c : (unramifiedZeroFixerCentralizerModel C E N Ω hN).Hom N C.centralizer.j :=
    { hom := (unramifiedZeroFixerCentralizerLift C E N M Ω Ω' hN hM hne).hom ≫ φ.hom
      generic_comm := by
        simpa only [IntegralModel.Hom.comp, Category.comp_id] using
          ((unramifiedZeroFixerCentralizerLift C E N M Ω Ω' hN hM hne).comp φ).generic_comm }
  exact c.hom_eq (unramifiedZeroFixerCentralizerModelMap C E N Ω hN)

/-- The full residue centralizer inclusion factors through every such comparison map. -/
theorem unramifiedZeroFixerCentralizerLift_specialFibre_comp (hne : Ω.Nonempty)
    (φ : M.Hom N (𝟙 G)) :
    (unramifiedZeroFixerCentralizerLift C E N M Ω Ω' hN hM hne).specialFibreMap ≫
        φ.specialFibreMap =
      (unramifiedZeroFixerCentralizerModelMap C E N Ω hN).specialFibreMap := by
  simpa only [IntegralModel.Hom.specialFibreMap, Functor.map_comp] using
    congrArg ((GroupScheme.baseChange (IntegralModel.residueBaseMap (fixedFieldIntegers F))).map)
      (unramifiedZeroFixerCentralizerLift_comp C E N M Ω Ω' hN hM hne φ)

private instance specialFibre_affine
    (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G) :
    IsAffineHom P.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd P.group.X.hom
    (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
  exact MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom P.group.X.hom))

include hM

/-- The actual full residue centralizer lies in the actual closed schematic comparison
image, with inclusion on every scheme test. -/
theorem unramifiedZeroFixer_specialCentralizer_le_image (hne : Ω.Nonempty)
    (φ : M.Hom N (𝟙 G)) [QuasiCompact φ.specialFibreMap.hom.hom.left] :
    torusCentralizer (T := (unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN).specialFibreTorus)
        (unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN).specialFibreInclusion ≤
      SubgroupFunctor.range (SchematicImage.inclusion φ.specialFibreMap) := by
  have hrep := IntegralSplitTorusData.centralizerModelMap_specialFibre_isCentralizer
    (unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN)
    C.centralizer.j C.centralizer.isRepresentedBy
  rw [← hrep.2]
  apply SubgroupFunctor.range_le_of_factor
    ((unramifiedZeroFixerCentralizerLift C E N M Ω Ω' hN hM hne).specialFibreMap ≫
      SchematicImage.projection φ.specialFibreMap)
  rw [Category.assoc, SchematicImage.projection_inclusion]
  exact unramifiedZeroFixerCentralizerLift_specialFibre_comp C E N M Ω Ω' hN hM hne φ

end Unramified

end Langlands.BruhatTits.IntegralModels

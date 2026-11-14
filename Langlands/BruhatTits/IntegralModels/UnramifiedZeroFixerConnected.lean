import Langlands.BruhatTits.IntegralModels.UnramifiedSingleFacetReduction
import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralZeroAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerRoots
import Langlands.BruhatTits.IntegralModels.ConnectedFactorization
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriConnectedImageProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelAssembly
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof
import Langlands.GroupScheme.IntegralModel.GenericRigidity
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.GroupScheme.GeometricConnectedness

/-! # Connectedness of characterized maximal-unramified zero-fixer models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)

section Neutral

variable (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (Ω : Set C.Apartment)
    (hN : D.full.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))

include hN in
/-- The whole-apartment zero fixer lies in the neutral model, using the
connected smooth source of the norm-defined torus Iwahori subgroup. -/
theorem unramifiedWholeApartmentZeroFixer_le_neutral :
    E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Set.univ) ≤
      D.neutral.integralPoints := by
  let E' := UnramifiedZeroDatum.withApartmentTorus C E
  obtain ⟨S, W, n, hW, hWgc, hWpts⟩ :=
    unramifiedTorusIwahoriConnectedImage F E'.T E'.L E'.isSplitTorus
  change W.integralPoints.map (rationalPoints.map n) = E'.torusIwahori at hWpts
  have hcomp : rationalPoints.map (n ≫ E'.i) =
      (rationalPoints.map E'.i).comp (rationalPoints.map n) := by
    ext g
    rfl
  have hWimage :
      W.integralPoints.map (rationalPoints.map (n ≫ E'.i)) =
        E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Set.univ) := by
    rw [hcomp, ← Subgroup.map_map, hWpts]
    exact (wholeApartmentZeroFixer_eq_apartmentTorusIwahori C E).symm
  have hle : W.integralPoints.map (rationalPoints.map (n ≫ E'.i)) ≤
      D.full.integralPoints := by
    rw [hWimage, hN]
    exact inf_le_inf_left _ (C.apartment.pointwiseFixer_image_anti (Set.subset_univ Ω))
  obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le
    IntegralModel.smoothHomExtension F hW rfl hle
  let : GeometricallyConnected W.group.X.hom := hWgc
  rw [← hWimage]
  exact D.map_integralPoints_le_neutral φ

include hN in
/-- Every root fixer lies in the neutral model through its actual connected
integral root model; no boundedness of the apartment set is needed. -/
theorem unramifiedZeroSharpFixer_le_neutral :
    C.sharpFixer Ω ≤ D.neutral.integralPoints := by
  let : Smooth D.full.group.X.hom := D.full_smooth
  let A := unramifiedZeroFixerIntegralSplitTorusData C E D.full Ω hN
  apply iSup_le
  intro a
  let : GeometricallyConnected (A.rootModel a a.2.1).group.X.hom :=
    IntegralModel.SplitRoot.model_hasGeometricallyConnectedFibres D.full A.isSplit
      A.inclusion (A.integralCharacter a) (A.integralCharacter_ne_zero a.2.1)
  have h := D.map_integralPoints_le_neutral (A.rootModelMap a a.2.1)
  change (A.rootModel a a.2.1).integralPoints.map
    (rationalPoints.map (A.rootInclusion a a.2.1)) ≤ D.neutral.integralPoints at h
  rw [unramifiedZeroFixerRootModel_integralPoints_eq C E D.full Ω hN a] at h
  exact h

end Neutral

/-- For a singleton zero fixer, all integral points lie in the relative
identity component, so the full model has connected fibres. -/
theorem unramifiedSingletonZeroFixer_hasConnectedFibres
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    (hSmooth : N.IsSmooth) (x : C.Apartment)
    (hN : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x})) :
    N.HasConnectedFibres := by
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let : Smooth G.X.hom := C.isConnectedReductive.smooth
  let : ConnectedSpace G.X.left := C.isConnectedReductive.connectedSpace
  let : GeometricallyConnected G.X.hom := G.geometricallyConnected_of_connected
  obtain ⟨D, hD, _⟩ := N.exists_relativeComponentModelData hSmooth
  subst N
  have hgen := E.wholeApartmentZeroFixer_sup_sharpFixer_eq_of_simplyConnectedNormalizer
    C MaximalUnramified.simplyConnectedNormalizerAffineWeyl
    (Set.singleton_nonempty x) (fun f => by simp)
  have hle : D.full.integralPoints ≤ D.neutral.integralPoints := by
    rw [hN, hgen]
    exact sup_le
      (unramifiedWholeApartmentZeroFixer_le_neutral C E D {x} hN)
      (unramifiedZeroSharpFixer_le_neutral C E D {x} hN)
  obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le
    IntegralModel.smoothHomExtension F hSmooth
    (n := 𝟙 G) (by
      ext g
      simp only [Subgroup.mem_map, rationalPoints.map_apply, Grp.id_hom_hom,
        Category.comp_id, exists_eq_right])
    hle
  let e := IntegralModel.Iso.ofHoms (f := CategoryTheory.Iso.refl G) φ D.inclusion
  exact connectedFibres_of_iso e.iso D.neutral_connectedFibres

/-- Characterized smooth zero-fixer models have connected fibres on every
nonempty subset of a single facet, even when the facet is unbounded. -/
theorem unramifiedZeroFixer_hasConnectedFibres
    {Ω : Set C.Apartment} (hΩ : Ω.Nonempty)
    (hfacet : ∃ x : C.Apartment, Ω ⊆ AffineRootSystem.facet C.affineRoots x)
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    (hSmooth : N.IsSmooth)
    (hN : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)) :
    N.HasConnectedFibres := by
  obtain ⟨x, hx⟩ := hΩ
  obtain ⟨y, hsub⟩ := hfacet
  have hsingle := hN.trans
    (unramifiedZeroFixer_eq_singleton_of_subset_facet C E
      (AffineRootSystem.isFacet_facet C.affineRoots y) hx hsub)
  exact unramifiedSingletonZeroFixer_hasConnectedFibres C E N hSmooth x hsingle

/-- Connectedness of the actual full special fibre of every characterized
smooth model on the nonempty single-facet domain. -/
def UnramifiedZeroFixerConnectedStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (Ω : Set C.Apartment), Ω.Nonempty →
    (∃ x : C.Apartment, Ω ⊆ AffineRootSystem.facet C.affineRoots x) →
    ∀ (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G),
      N.IsSmooth →
      N.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) →
      N.HasConnectedSpecialFibre

/-- The full special fibre is connected without an additional geometric
premise on the supplied characterized smooth model. -/
theorem unramifiedZeroFixerConnected : UnramifiedZeroFixerConnectedStatement.{u} := by
  intro F _ _ _ _ G _ C E Ω hΩ hfacet N hSmooth hN
  exact N.hasConnectedSpecialFibre_of_hasConnectedFibres
    (unramifiedZeroFixer_hasConnectedFibres C E hΩ hfacet N hSmooth hN)

end Langlands.BruhatTits.IntegralModels

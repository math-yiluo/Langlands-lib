import Langlands.BruhatTits.IntegralModels.UnramifiedIntegralRoots
import Langlands.BruhatTits.IntegralModels.ConnectedFactorization
import Langlands.GroupScheme.IntegralModel.RelativeComponentConstruction
import Langlands.GroupScheme.RelativeParabolicNormalizerReduction

/-! # Actual root models inside the neutral component of a full fixer model -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

section General

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G H : GroupScheme (Spec (CommRingCat.of K))}
    (D : RelativeComponentModelData R K G)

namespace RelativeComponentModelData

variable {M : IntegralModel R K H} [GeometricallyConnected M.group.X.hom]
    {f : H ⟶ G}

/-- The actual compatible model map from a geometrically connected model
to the neutral component of the supplied ambient model. -/
def factorConnectedModelHom (φ : M.Hom D.full f) : M.Hom D.neutral f where
  hom := RelativeIdentityComponent.factor φ.hom D.isRelativeComponent
  generic_comm := by
    have hi := D.inclusion.generic_comm
    rw [Category.comp_id] at hi
    rw [← hi, ← Category.assoc, ← Functor.map_comp,
      RelativeIdentityComponent.factor_comp, φ.generic_comm]

@[simp]
theorem factorConnectedModelHom_comp (φ : M.Hom D.full f) :
    (D.factorConnectedModelHom φ).hom ≫ D.inclusion.hom = φ.hom :=
  RelativeIdentityComponent.factor_comp φ.hom D.isRelativeComponent

theorem factorConnectedModelHom_isClosedSubgroup (φ : M.Hom D.full f)
    (hφ : IsClosedSubgroup φ.hom) :
    IsClosedSubgroup (D.factorConnectedModelHom φ).hom := by
  apply D.isRelativeComponent.isClosedSubgroup_of_comp
  rw [D.factorConnectedModelHom_comp]
  exact hφ

end RelativeComponentModelData

namespace IntegralSplitTorusData

variable {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {i : S.toGrp ⟶ G} (A : IntegralSplitTorusData D.full i)

/-- The same actual integral split torus, now mapped compatibly into the
neutral model by geometric connectedness. -/
def factorNeutral : IntegralSplitTorusData D.neutral i := by
  let : GeometricallyConnected A.torus.toGrp.X.hom :=
    A.isSplit.isReductive.geometricallyConnected
  refine
    { torus := A.torus
      isSplit := A.isSplit
      inclusion := RelativeIdentityComponent.factor A.inclusion D.isRelativeComponent
      genericIso := A.genericIso
      generic_comm := ?_ }
  have hi := D.inclusion.generic_comm
  rw [Category.comp_id] at hi
  change (GroupScheme.baseChange (Spec.algebraMap R K)).map
      (RelativeIdentityComponent.factor A.inclusion D.isRelativeComponent) ≫
        D.neutral.genericIso.hom = _
  rw [← hi, ← Category.assoc, ← Functor.map_comp,
    RelativeIdentityComponent.factor_comp]
  exact A.generic_comm

theorem factorNeutral_isClosedSubgroup (hA : IsClosedSubgroup A.inclusion) :
    IsClosedSubgroup (A.factorNeutral D).inclusion := by
  let : GeometricallyConnected A.torus.toGrp.X.hom :=
    A.isSplit.isReductive.geometricallyConnected
  apply D.isRelativeComponent.isClosedSubgroup_of_comp
  change IsClosedSubgroup
    (RelativeIdentityComponent.factor A.inclusion D.isRelativeComponent ≫ D.inclusion.hom)
  rw [RelativeIdentityComponent.factor_comp]
  exact hA

variable [Smooth D.full.group.X.hom]

/-- The actual constructed root model maps compatibly into the neutral model,
with its original generic root representative. -/
def rootModelNeutralMap (a : characterLattice S) (ha : a ≠ 0) :
    (A.rootModel a ha).Hom D.neutral (A.rootInclusion a ha) := by
  let : GeometricallyConnected (A.rootModel a ha).group.X.hom :=
    IntegralModel.SplitRoot.model_hasGeometricallyConnectedFibres D.full A.isSplit
      A.inclusion (A.integralCharacter a) (A.integralCharacter_ne_zero ha)
  exact D.factorConnectedModelHom (A.rootModelMap a ha)

theorem rootModelNeutralMap_isClosedSubgroup (a : characterLattice S) (ha : a ≠ 0) :
    IsClosedSubgroup (A.rootModelNeutralMap D a ha).hom := by
  let : GeometricallyConnected (A.rootModel a ha).group.X.hom :=
    IntegralModel.SplitRoot.model_hasGeometricallyConnectedFibres D.full A.isSplit
      A.inclusion (A.integralCharacter a) (A.integralCharacter_ne_zero ha)
  exact D.factorConnectedModelHom_isClosedSubgroup (A.rootModelMap a ha)
    (A.rootModelMap_isClosedSubgroup a ha)

include A in
/-- Passing from the full model to its neutral component preserves the
intersection with every nonzero actual root subgroup. -/
theorem rootGroupPoints_inf_neutral_eq_full (a : characterLattice S) (ha : a ≠ 0) :
    rootGroupPoints i a ⊓ D.neutral.integralPoints =
      rootGroupPoints i a ⊓ D.full.integralPoints := by
  apply le_antisymm
  · exact inf_le_inf_left _ (by
      rw [← D.neutralPoints_eq]
      exact D.neutralPoints_le_full)
  · apply le_inf inf_le_left
    have hmap :
        (A.rootModel a ha).integralPoints.map (rationalPoints.map (A.rootInclusion a ha)) ≤
          D.neutral.integralPoints := by
      rintro _ ⟨g, hg, rfl⟩
      exact (A.rootModelNeutralMap D a ha).map_mem_integralPoints hg
    rw [A.rootModel_integralPoints_eq a ha, inf_comm] at hmap
    exact hmap

end IntegralSplitTorusData

end General

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G)
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (Ω : Set C.Apartment)
    (hN : D.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω))

include hN in
/-- The neutral model has exactly the actual root fixer as its intersection
with each relative root group. No boundedness or torus-Iwahori premise is needed. -/
theorem rootGroupPoints_inf_unramifiedNeutral_eq_rootFixer (a : relativeRoots C.i) :
    rootGroupPoints C.i a ⊓ D.neutral.integralPoints = C.apartment.rootFixer a Ω := by
  let : Smooth D.full.group.X.hom := D.full_smooth
  let A := unramifiedIntegralSplitTorusData C D.full Ω hN
  rw [A.rootGroupPoints_inf_neutral_eq_full D a a.2.1, hN]
  exact C.apartment.rootGroupPoints_inf_oneFixer_eq_rootFixer
    C.isConnectedReductive C.isMaximalSplitTorus (MaximalUnramified.valuation F) a Ω

include hN in
/-- Every actual sharp-fixer generator, and hence their generated subgroup,
already belongs to the neutral model. -/
theorem unramifiedSharpFixer_le_neutral :
    C.sharpFixer Ω ≤ D.neutral.integralPoints := by
  apply iSup_le
  intro a
  rw [← rootGroupPoints_inf_unramifiedNeutral_eq_rootFixer C D Ω hN a]
  exact inf_le_right

include hN in
/-- For a bounded nonempty apartment set, the neutral model's actual root
intersection has the same exact filtration level as the full model. -/
theorem rootGroupPoints_inf_unramifiedNeutral_eq_filtration
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (a : relativeRoots C.i) (x : C.Apartment) :
    rootGroupPoints C.i a ⊓ D.neutral.integralPoints =
      C.apartment.filtration x a (C.apartment.rootFixerDepth a x Ω) := by
  rw [rootGroupPoints_inf_unramifiedNeutral_eq_rootFixer C D Ω hN a]
  exact C.apartment.rootFixer_eq_filtration_of_bounded a x hne hb

end Unramified

end Langlands.BruhatTits.IntegralModels

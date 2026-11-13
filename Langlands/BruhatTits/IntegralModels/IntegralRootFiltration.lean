import Langlands.BruhatTits.IntegralModels.RootFiltrationModel
import Langlands.GroupScheme.IntegralModel.SplitRoot
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.Geometry.Building.GenericRootFixerIntersection

/-! # Integral root-filtration models from a compatible integral split torus -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {i : S.toGrp ⟶ G}

/-- An actual integral split torus mapped into the ambient model, with its
specified generic identification and commuting inclusion square. Existence
of these data is not asserted. -/
structure IntegralSplitTorusData (N : IntegralModel R K G) (i : S.toGrp ⟶ G) where
  torus : CommGroupScheme (Spec (CommRingCat.of R))
  isSplit : IsSplitTorus torus.toGrp
  inclusion : torus.toGrp ⟶ N.group
  genericIso : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj torus ≅ S
  generic_comm :
    N.genericHom inclusion = CommGroupScheme.groupHom genericIso.hom ≫ i

namespace IntegralSplitTorusData

variable {N : IntegralModel R K G} (A : IntegralSplitTorusData N i)

/-- The actual integral character obtained by the split-torus lattice
base-change equivalence and the supplied generic torus isomorphism. -/
def integralCharacter (a : characterLattice S) : characterLattice A.torus :=
  (characterLattice.baseChangeEquiv (Spec.algebraMap R K) A.torus A.isSplit).symm
    ((characterLattice.congr A.genericIso).symm a)

@[simp] theorem generic_integralCharacter (a : characterLattice S) :
    characterLattice.congr A.genericIso
      (characterLattice.baseChange (Spec.algebraMap R K) A.torus
        (A.integralCharacter a)) = a := by
  change characterLattice.congr A.genericIso
    (characterLattice.baseChangeEquiv (Spec.algebraMap R K) A.torus A.isSplit
      ((characterLattice.baseChangeEquiv (Spec.algebraMap R K) A.torus A.isSplit).symm
        ((characterLattice.congr A.genericIso).symm a))) = a
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

theorem integralCharacter_ne_zero {a : characterLattice S} (ha : a ≠ 0) :
    A.integralCharacter a ≠ 0 := by
  intro h
  have h' := A.generic_integralCharacter a
  rw [h, map_zero, map_zero] at h'
  exact ha h'.symm

/-- The full root functor constructed over the integral torus has exactly
the prescribed generic root functor, on every test scheme. -/
theorem generic_rootFunctor_eq (a : characterLattice S) :
    RelativeRoot.subgroup (N.genericHom A.inclusion)
      (characterLattice.baseChange (Spec.algebraMap R K) A.torus
        (A.integralCharacter a)) = RelativeRoot.subgroup i a := by
  have h := RelativeRoot.subgroup_comap_of_transport A.genericIso (Iso.refl G)
    (i := N.genericHom A.inclusion) (j := i)
    (by simpa only [Iso.refl_hom, Category.comp_id] using A.generic_comm)
    (characterLattice.baseChange (Spec.algebraMap R K) A.torus
      (A.integralCharacter a))
  simpa only [Iso.refl_hom, SubgroupFunctor.comap_id,
    A.generic_integralCharacter] using h.symm

variable [Smooth N.group.X.hom]

/-- The actual generic root representative produced from the integral torus. -/
def rootGroup (a : characterLattice S) (ha : a ≠ 0) :
    GroupScheme (Spec (CommRingCat.of K)) :=
  IntegralModel.SplitRoot.genericGroup N A.isSplit A.inclusion
    (A.integralCharacter a) (A.integralCharacter_ne_zero ha)

/-- Its actual generic inclusion into `G`. -/
def rootInclusion (a : characterLattice S) (ha : a ≠ 0) :
    A.rootGroup a ha ⟶ G :=
  IntegralModel.SplitRoot.genericHom N A.isSplit A.inclusion
    (A.integralCharacter a) (A.integralCharacter_ne_zero ha)

theorem rootInclusion_isRootSubgroup (a : characterLattice S) (ha : a ≠ 0) :
    (RelativeRoot.subgroup i a).IsRepresentedBy (A.rootInclusion a ha) := by
  rw [← A.generic_rootFunctor_eq a]
  exact IntegralModel.SplitRoot.isRepresentedBy_genericHom
    N A.isSplit A.inclusion (A.integralCharacter a) (A.integralCharacter_ne_zero ha)

/-- The smooth affine integral model of the constructed generic root group. -/
def rootModel (a : characterLattice S) (ha : a ≠ 0) :
    IntegralModel R K (A.rootGroup a ha) :=
  IntegralModel.SplitRoot.model N A.isSplit A.inclusion
    (A.integralCharacter a) (A.integralCharacter_ne_zero ha)

/-- The actual compatible integral map from the root model to the ambient model. -/
def rootModelMap (a : characterLattice S) (ha : a ≠ 0) :
    (A.rootModel a ha).Hom N (A.rootInclusion a ha) :=
  IntegralModel.SplitRoot.inclusion N A.isSplit A.inclusion
    (A.integralCharacter a) (A.integralCharacter_ne_zero ha)

theorem rootModelMap_isClosedSubgroup (a : characterLattice S) (ha : a ≠ 0) :
    IsClosedSubgroup (A.rootModelMap a ha).hom :=
  IntegralModel.SplitRoot.inclusion_isClosedSubgroup
    N A.isSplit A.inclusion (A.integralCharacter a) (A.integralCharacter_ne_zero ha)

/-- The constructed integral point image is exactly the intersection with
the intrinsic rational root subgroup. -/
theorem rootModel_integralPoints_eq (a : characterLattice S) (ha : a ≠ 0) :
    (A.rootModel a ha).integralPoints.map (rationalPoints.map (A.rootInclusion a ha)) =
      N.integralPoints ⊓ rootGroupPoints i a := by
  have h := IntegralModel.SplitRoot.map_integralPoints_eq
    N A.isSplit A.inclusion (A.integralCharacter a) (A.integralCharacter_ne_zero ha)
  rw [A.generic_rootFunctor_eq a] at h
  exact h

variable [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : Kˣ → ℝ}
    (C : KPApartmentData i ω)

/-- If the ambient model has the full one-fixer as integral points, its
constructed root model has the exact prescribed bounded-set filtration image. -/
theorem rootModel_integralPoints_eq_filtration
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    (x : C.Apartment) (a : relativeRoots i) (Ω : Set C.Apartment)
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (hN : N.integralPoints =
      characterValuationKernel v G ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)) :
    (A.rootModel a a.2.1).integralPoints.map
        (rationalPoints.map (A.rootInclusion a a.2.1)) =
      C.filtration x a (C.rootFixerDepth a x Ω) := by
  rw [A.rootModel_integralPoints_eq a a.2.1, hN, inf_comm]
  exact C.rootGroupPoints_inf_oneFixer_eq_filtration_of_bounded hG hi v a x hne hb

/-- The actual root-filtration model required by the parahoric construction,
with full generic root identity and no supplied filtration-image premise. -/
def rootFiltrationModelData
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    (x : C.Apartment) (a : relativeRoots i) (Ω : Set C.Apartment)
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (hN : N.integralPoints =
      characterValuationKernel v G ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)) :
    RootFiltrationModelData R K C x a (C.rootFixerDepth a x Ω) where
  rootGroup := A.rootGroup a a.2.1
  inclusion := A.rootInclusion a a.2.1
  isRootSubgroup := A.rootInclusion_isRootSubgroup a a.2.1
  model := A.rootModel a a.2.1
  smooth := IntegralModel.SplitRoot.model_isSmooth
    N A.isSplit A.inclusion (A.integralCharacter a) (A.integralCharacter_ne_zero a.2.1)
  geometricallyConnected := IntegralModel.SplitRoot.model_hasGeometricallyConnectedFibres
    N A.isSplit A.inclusion (A.integralCharacter a) (A.integralCharacter_ne_zero a.2.1)
  integralPoints_eq :=
    A.rootModel_integralPoints_eq_filtration C hG hi v x a Ω hne hb hN

/-- The constructed filtration model maps into the ambient model by the
actual integral closed inclusion. -/
def rootFiltrationModelMap
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    (x : C.Apartment) (a : relativeRoots i) (Ω : Set C.Apartment)
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (hN : N.integralPoints =
      characterValuationKernel v G ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)) :
    (A.rootFiltrationModelData C hG hi v x a Ω hne hb hN).model.Hom N
      (A.rootFiltrationModelData C hG hi v x a Ω hne hb hN).inclusion :=
  A.rootModelMap a a.2.1

end IntegralSplitTorusData

end Langlands.BruhatTits.IntegralModels

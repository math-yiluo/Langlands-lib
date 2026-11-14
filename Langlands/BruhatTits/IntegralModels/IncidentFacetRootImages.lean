import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentRootImage
import Langlands.BruhatTits.IntegralModels.IncidentRootReductiveQuotient
import Langlands.Geometry.Building.IncidentFacetRootFiltration
import Langlands.Geometry.Building.IntegerValuationChamberBounded

/-! # Actual root images for nonnegative incident-facet roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- A nonnegative root on the displacement from a face to an incident facet
has equal actual root fixers on arbitrary nonempty subsets containing those points. -/
theorem rootFixer_eq_of_incidentFacetSubsets_of_nonneg
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    {Fa Fa' Ω Ω' : Set D.Apartment}
    (hFa' : AffineRootSystem.IsFacet D.affineRoots Fa')
    (hface : AffineRootSystem.IsFaceOf D.affineRoots Fa Fa')
    (hsub : Ω ⊆ Fa) (hsub' : Ω' ⊆ Fa')
    {x y : D.Apartment} (hx : x ∈ Ω) (hy : y ∈ Ω')
    (a : relativeRoots i) (ha : 0 ≤ rootForm i a (y -ᵥ x)) :
    D.rootFixer a Ω' = D.rootFixer a Ω := by
  rw [D.rootFixer_eq_of_nonempty_subset_facet hAS4 hFa' ⟨y, hy⟩ hsub' a,
    D.rootFixer_eq_of_nonempty_subset_facet hAS4 hface.1 ⟨x, hx⟩ hsub a]
  exact (D.rootFixer_eq_of_incidentFacets_of_nonneg hAS4 hFa' hface
    (hsub' hy) (hsub hx) a ha).symm

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.BruhatTits.IntegralModels.RootFiltrationModelData

private theorem facetComparisonIso_comp
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] {ω : Kˣ → ℝ}
    {C : KPApartmentData i ω} {x : C.Apartment} {a : relativeRoots i} {r s : ℝ}
    (U : RootFiltrationModelData R K C x a r)
    (V : RootFiltrationModelData R K C x a s)
    (e : U.model.Iso V.model (U.genericIso V))
    {N N' : IntegralModel R K G}
    (j : U.model.Hom N U.inclusion) (k : V.model.Hom N' V.inclusion)
    (ψ : N.Hom N' (𝟙 G)) :
    e.iso.hom ≫ k.hom = j.hom ≫ ψ.hom := by
  apply IntegralModel.hom_eq_of_generic
  apply (cancel_mono N'.genericIso.hom).mp
  simp only [Functor.map_comp, Category.assoc, k.generic_comm,
    ψ.generic_comm, Category.comp_id]
  rw [← Category.assoc, e.generic_comm, Category.assoc,
    U.genericIso_hom_comp V, ← j.generic_comm]

end Langlands.BruhatTits.IntegralModels.RootFiltrationModelData

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

section EqualRootFixers

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    {source target :
      RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G}
    (φ : RelativeComponentModelHom source target)
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (T : IntegralTorusData source C.S C.i) (hT : IsSplitTorus T.torus.toGrp)
    (Ω Ω' : Set C.Apartment)
    (hsource : source.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))
    (htarget : target.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hne : Ω.Nonempty) (hne' : Ω'.Nonempty)
    (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (hb' : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω'))

private instance sourceNeutral_smooth : Smooth source.neutral.group.X.hom :=
  source.neutral_smooth

private instance targetNeutral_smooth : Smooth target.neutral.group.X.hom :=
  target.neutral_smooth

include hsource htarget hne hne' hb hb'

/-- Equality of actual root fixer subgroups makes the canonical integral root
map an isomorphism, without requiring equal real root-fixer depths. -/
theorem integralRootMap_isIso_of_rootFixer_eq
    (x : C.Apartment) (a : relativeRoots C.i)
    (hfixer : C.apartment.rootFixer a Ω' = C.apartment.rootFixer a Ω) :
    IsIso (φ.integralRootMap T hT a a.2.1) := by
  let A := T.toIntegralSplitTorusData hT
  let B := (φ.mapIntegralTorus T).toIntegralSplitTorusData hT
  let U := A.unramifiedZeroRootFiltrationModelData C E Ω' hsource hne' hb' x a
  let V := B.unramifiedZeroRootFiltrationModelData C E Ω htarget hne hb x a
  let e := U.unramifiedModelIsoOfFiltrationEq V (by
    rw [← C.apartment.rootFixer_eq_filtration_of_bounded a x hne' hb',
      ← C.apartment.rootFixer_eq_filtration_of_bounded a x hne hb]
    exact hfixer)
  have he :
      e.iso.hom ≫ (B.rootModelMap a a.2.1).hom =
        (A.rootModelMap a a.2.1).hom ≫ φ.neutral.hom := by
    exact U.facetComparisonIso_comp V e (A.rootModelMap a a.2.1)
      (B.rootModelMap a a.2.1) φ.neutral
  have hmap : φ.integralRootMap T hT a a.2.1 = e.iso.hom := by
    apply (B.rootModelMap_isRepresentedBy a a.2.1).hom_ext
    have hcomp :
        φ.integralRootMap T hT a a.2.1 ≫ (B.rootModelMap a a.2.1).hom =
          (A.rootModelMap a a.2.1).hom ≫ φ.neutral.hom :=
      φ.integralRootMap_comp T hT a a.2.1
    exact hcomp.trans he.symm
  rw [hmap]
  infer_instance

/-- Equality of actual root fixer subgroups also makes the actual residue
root map an isomorphism on every scheme test. -/
theorem residueRootMap_isIso_of_rootFixer_eq
    (x : C.Apartment) (a : relativeRoots C.i)
    (hfixer : C.apartment.rootFixer a Ω' = C.apartment.rootFixer a Ω) :
    IsIso (φ.residueRootMap T hT a a.2.1) := by
  let : IsIso (φ.integralRootMap T hT a a.2.1) :=
    φ.integralRootMap_isIso_of_rootFixer_eq C E T hT Ω Ω'
      hsource htarget hne hne' hb hb' x a hfixer
  exact (GroupScheme.baseChange (IntegralModel.residueBaseMap
    (fixedFieldIntegers F))).map_isIso _

end EqualRootFixers

section IncidentFacets

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    {source target :
      RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G}
    (φ : RelativeComponentModelHom source target)
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (T : IntegralTorusData source C.S C.i) (hT : IsSplitTorus T.torus.toGrp)
    (Ωf Ωf' Ω Ω' : Set C.Apartment)
    (hface : AffineRootSystem.IsFaceOf C.affineRoots Ωf Ωf')
    (hsub : Ω ⊆ Ωf) (hsub' : Ω' ⊆ Ωf')
    (hsource : source.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))
    (htarget : target.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))

include hface hsub hsub' hsource htarget

/-- At incident facet subsets, every root nonnegative on the actual
cocharacter displacement has an invertible canonical integral root map. -/
theorem integralRootMap_isIso_of_incidentFacets_of_nonneg
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω')
    (a : relativeRoots C.i) (ha : 0 ≤ RealTorusSpace.eval C.S a v) :
    IsIso (φ.integralRootMap T hT a a.2.1) := by
  have hΩf := hface.1
  have hΩf' : AffineRootSystem.IsFacet C.affineRoots Ωf' :=
    ⟨hface.2.choose, hface.2.choose_spec.1⟩
  have hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω) :=
    fun f => (C.isBoundedApartmentSubset_of_isFacet
      (MaximalUnramified.exists_order_ne_zero F) hΩf f).mono (Set.image_mono hsub)
  have hb' : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω') :=
    fun f => (C.isBoundedApartmentSubset_of_isFacet
      (MaximalUnramified.exists_order_ne_zero F) hΩf' f).mono (Set.image_mono hsub')
  apply φ.integralRootMap_isIso_of_rootFixer_eq C E T hT Ω Ω'
    hsource htarget ⟨x, hx⟩ ⟨_, hv⟩ hb hb' x a
  apply C.apartment.rootFixer_eq_of_incidentFacetSubsets_of_nonneg
    C.affineRoot_mem_or_two_smul_mem hΩf' hface hsub hsub' hx hv a
  simpa only [vadd_vsub, rootForm_mk] using ha

/-- The actual residue root map is invertible for every nonnegative root
on the displacement between the two incident facet subsets. -/
theorem residueRootMap_isIso_of_incidentFacets_of_nonneg
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω')
    (a : relativeRoots C.i) (ha : 0 ≤ RealTorusSpace.eval C.S a v) :
    IsIso (φ.residueRootMap T hT a a.2.1) := by
  let : IsIso (φ.integralRootMap T hT a a.2.1) :=
    φ.integralRootMap_isIso_of_incidentFacets_of_nonneg C E T hT
      Ωf Ωf' Ω Ω' hface hsub hsub' hsource htarget x hx v hv a ha
  exact (GroupScheme.baseChange (IntegralModel.residueBaseMap
    (fixedFieldIntegers F))).map_isIso _

/-- Package the canonical integral root map as an isomorphism for a
nonnegative root on the actual incident-facet displacement. -/
def integralRootIsoOfIncidentFacetsNonneg
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω')
    (a : relativeRoots C.i) (ha : 0 ≤ RealTorusSpace.eval C.S a v) :
    ((T.toIntegralSplitTorusData hT).rootModel a a.2.1).group ≅
      (((φ.mapIntegralTorus T).toIntegralSplitTorusData hT).rootModel a a.2.1).group := by
  let : IsIso (φ.integralRootMap T hT a a.2.1) :=
    φ.integralRootMap_isIso_of_incidentFacets_of_nonneg C E T hT
      Ωf Ωf' Ω Ω' hface hsub hsub' hsource htarget x hx v hv a ha
  exact asIso (φ.integralRootMap T hT a a.2.1)

@[simp] theorem integralRootIsoOfIncidentFacetsNonneg_hom
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω')
    (a : relativeRoots C.i) (ha : 0 ≤ RealTorusSpace.eval C.S a v) :
    (φ.integralRootIsoOfIncidentFacetsNonneg C E T hT
      Ωf Ωf' Ω Ω' hface hsub hsub' hsource htarget x hx v hv a ha).hom =
        φ.integralRootMap T hT a a.2.1 := rfl

variable (Q : SpecialFibreQuotientData target) (hQ : Q.IsReductiveQuotient)

include hQ

/-- For a nonnegative incident-facet root, the full kernel of the original
source-root composite into the target reductive quotient is smooth. -/
theorem rootTargetReductiveQuotientMap_smooth_kernel_of_incidentFacets_of_nonneg
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω')
    (a : relativeRoots C.i) (ha : 0 ≤ RealTorusSpace.eval C.S a v) :
    Smooth (kernel (φ.rootTargetReductiveQuotientMap T hT Q a a.2.1)).X.hom := by
  let : IsIso (φ.residueRootMap T hT a a.2.1) :=
    φ.residueRootMap_isIso_of_incidentFacets_of_nonneg C E T hT
      Ωf Ωf' Ω Ω' hface hsub hsub' hsource htarget x hx v hv a ha
  exact φ.rootTargetReductiveQuotientMap_smooth_kernel_of_isIso T hT Q hQ a a.2.1

/-- For a nonnegative incident-facet root, the original differential has
the entire target positive cyclic root-weight span as its range. -/
theorem rootTargetReductiveQuotientMap_lie_range_of_incidentFacets_of_nonneg
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω')
    (a : relativeRoots C.i) (ha : 0 ≤ RealTorusSpace.eval C.S a v) :
    LinearMap.range (Lie.targetMapLinear
      (φ.rootTargetReductiveQuotientMap T hT Q a a.2.1)
      (IsLocalRing.ResidueField (fixedFieldIntegers F))) =
        RelativeRoot.semigroupWeightSpan
          (AutomorphicAction.conjugation (φ.quotientTorusInclusion Q T))
          (RelativeRoot.cyclicTail (T.characterSpecialization hT a) 1) := by
  let : IsIso (φ.residueRootMap T hT a a.2.1) :=
    φ.residueRootMap_isIso_of_incidentFacets_of_nonneg C E T hT
      Ωf Ωf' Ω Ω' hface hsub hsub' hsource htarget x hx v hv a ha
  exact φ.rootTargetReductiveQuotientMap_lie_range_of_isIso T hT Q hQ a a.2.1

/-- For a nonnegative incident-facet root, the actual schematic root image
has the entire target positive cyclic Lie range. -/
theorem rootTargetReductiveQuotientImage_lie_range_of_incidentFacets_of_nonneg
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω')
    (a : relativeRoots C.i) (ha : 0 ≤ RealTorusSpace.eval C.S a v) :
    LinearMap.range (Lie.targetMapLinear
      (SchematicImage.inclusion (φ.rootTargetReductiveQuotientMap T hT Q a a.2.1))
      (IsLocalRing.ResidueField (fixedFieldIntegers F))) =
        RelativeRoot.semigroupWeightSpan
          (AutomorphicAction.conjugation (φ.quotientTorusInclusion Q T))
          (RelativeRoot.cyclicTail (T.characterSpecialization hT a) 1) := by
  let : IsIso (φ.residueRootMap T hT a a.2.1) :=
    φ.residueRootMap_isIso_of_incidentFacets_of_nonneg C E T hT
      Ωf Ωf' Ω Ω' hface hsub hsub' hsource htarget x hx v hv a ha
  exact φ.rootTargetReductiveQuotientImage_lie_range_of_isIso T hT Q hQ a a.2.1

end IncidentFacets

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

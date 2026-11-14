import Langlands.BruhatTits.IntegralModels.SpecialFibreImageRecovery
import Langlands.Geometry.Building.GenericVertexApartmentRigidity
import Langlands.Geometry.Building.ChamberParahoricConstancy
import Langlands.Geometry.Building.IntegerValuationSharpCoverImage
import Langlands.Geometry.Building.IntegerBuildingFacetPartition
import Langlands.Geometry.Building.BuildingFacetIncidence

/-! # Recovering apartment facets from zero fixers and actual model images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- A sharp fixer of a nonempty subset of one facet fixing a nonempty subset
of another forces the latter facet to be a face of the former. -/
theorem isFaceOf_of_sharpFixer_le_pointwiseFixer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    {Fa Ca Ω Ω' : Set D.Apartment}
    (hFa : AffineRootSystem.IsFacet D.affineRoots Fa)
    (hCa : AffineRootSystem.IsFacet D.affineRoots Ca)
    (hne : Ω.Nonempty) (hΩ : Ω ⊆ Fa)
    (hne' : Ω'.Nonempty) (hΩ' : Ω' ⊆ Ca)
    (hle : D.sharpFixer Ω ≤ D.pointwiseFixer (D.apartmentMap '' Ω')) :
    AffineRootSystem.IsFaceOf D.affineRoots Ca Fa := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ := hne'
  have hcl : y ∈ AffineRootSystem.facetClosure D.affineRoots x := by
    apply D.mem_facetClosure_of_fixed_by_sharpFixer hG hi
    intro g hg
    have hgFa : g ∈ D.sharpFixer Fa := by
      rwa [D.sharpFixer_eq_singleton_of_isFacet hAS4 hFa (hΩ hx)]
    exact D.mem_pointwiseFixer.mp
      (hle (D.sharpFixer_anti hΩ hgFa)) _ ⟨y, hy, rfl⟩
  have hFx : AffineRootSystem.facet D.affineRoots x = Fa :=
    (AffineRootSystem.isFacet_facet D.affineRoots x).eq_of_mem_mem hFa
      (AffineRootSystem.mem_facet_self _ _) (hΩ hx)
  have hCy : AffineRootSystem.facet D.affineRoots y = Ca :=
    (AffineRootSystem.isFacet_facet D.affineRoots y).eq_of_mem_mem hCa
      (AffineRootSystem.mem_facet_self _ _) (hΩ' hy)
  exact ⟨hCa, x, hFx, hCy ▸ AffineRootSystem.facet_subset_facetClosure_iff.mpr hcl⟩

end KPApartmentData

namespace UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  [IsAffineHom H.X.hom]
  (E : UnramifiedZeroDatum F H) (C : MaximalUnramified.BuildingData F H)

/-- Actual zero-fixer containment reflects apartment facet incidence, even
when each fixer is characterized using only a nonempty facet subset. -/
theorem isFaceOf_of_zeroFixer_le
    {Fa Ca Ω Ω' : Set C.Apartment}
    (hFa : AffineRootSystem.IsFacet C.affineRoots Fa)
    (hCa : AffineRootSystem.IsFacet C.affineRoots Ca)
    (hne : Ω.Nonempty) (hΩ : Ω ⊆ Fa)
    (hne' : Ω'.Nonempty) (hΩ' : Ω' ⊆ Ca)
    (hle : E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) ≤
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω')) :
    AffineRootSystem.IsFaceOf C.affineRoots Ca Fa := by
  apply C.apartment.isFaceOf_of_sharpFixer_le_pointwiseFixer
    C.isConnectedReductive C.isMaximalSplitTorus C.affineRoot_mem_or_two_smul_mem
    hFa hCa hne hΩ hne' hΩ'
  exact (le_inf (E.sharpFixer_le_zeroPoints C Ω)
    (C.sharpFixer_le_pointwiseFixer Ω)).trans (hle.trans inf_le_right)

/-- Equality of actual zero fixers on nonempty subsets recovers their full
apartment facets. -/
theorem facet_eq_of_zeroFixer_eq
    {Fa Ca Ω Ω' : Set C.Apartment}
    (hFa : AffineRootSystem.IsFacet C.affineRoots Fa)
    (hCa : AffineRootSystem.IsFacet C.affineRoots Ca)
    (hne : Ω.Nonempty) (hΩ : Ω ⊆ Fa)
    (hne' : Ω'.Nonempty) (hΩ' : Ω' ⊆ Ca)
    (heq : E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω')) :
    Fa = Ca :=
  (E.isFaceOf_of_zeroFixer_le C hCa hFa hne' hΩ' hne hΩ heq.ge).antisymm
    (E.isFaceOf_of_zeroFixer_le C hFa hCa hne hΩ hne' hΩ' heq.le)

/-- The actual zero-fixer subgroup faithfully encodes every full facet of
the displayed maximal-unramified apartment. -/
def facetZeroFixerEmbedding :
    {Fa : Set C.Apartment // AffineRootSystem.IsFacet C.affineRoots Fa} ↪
      Subgroup (rationalPoints H) where
  toFun Fa := E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Fa.val)
  inj' := by
    intro Fa Ca heq
    apply Subtype.ext
    obtain ⟨x, hx⟩ := Fa.property
    obtain ⟨y, hy⟩ := Ca.property
    apply E.facet_eq_of_zeroFixer_eq C Fa.property Ca.property
      (hx ▸ ⟨x, AffineRootSystem.mem_facet_self _ _⟩) (Set.Subset.refl _)
      (hy ▸ ⟨y, AffineRootSystem.mem_facet_self _ _⟩) (Set.Subset.refl _) heq

@[simp] theorem facetZeroFixerEmbedding_apply
    (Fa : {Fa : Set C.Apartment // AffineRootSystem.IsFacet C.affineRoots Fa}) :
    E.facetZeroFixerEmbedding C Fa =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Fa.val) :=
  rfl

end UnramifiedZeroDatum
end Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

open Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  [IsAffineHom H.X.hom]
  (E : UnramifiedZeroDatum F H) (C : MaximalUnramified.BuildingData F H)
  {R : Type u} [CommRing R] [IsDomain R]
  [Algebra R (UnramifiedClosure F)] [IsFractionRing R (UnramifiedClosure F)]
  [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
  {source₁ source₂ target : RelativeComponentModelData R (UnramifiedClosure F) H}
  (φ : RelativeComponentModelHom source₁ target)
  (ψ : RelativeComponentModelHom source₂ target)
  {Fa Ca Ω Ω' : Set C.Apartment}

/-- All-test actual special-fibre image containment reflects apartment facet
incidence for models characterized by the corresponding zero fixers. -/
theorem isFaceOf_of_unramifiedSpecialFibreImage_le
    (hFa : AffineRootSystem.IsFacet C.affineRoots Fa)
    (hCa : AffineRootSystem.IsFacet C.affineRoots Ca)
    (hne : Ω.Nonempty) (hΩ : Ω ⊆ Fa)
    (hne' : Ω'.Nonempty) (hΩ' : Ω' ⊆ Ca)
    (hsource₁ : source₁.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hsource₂ : source₂.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))
    (hker₁ : target.neutral.congruenceSubgroup ≤ source₁.neutral.integralPoints)
    (hker₂ : target.neutral.congruenceSubgroup ≤ source₂.neutral.integralPoints)
    (hle : SubgroupFunctor.range φ.specialFibreImageInclusion ≤
      SubgroupFunctor.range ψ.specialFibreImageInclusion) :
    AffineRootSystem.IsFaceOf C.affineRoots Ca Fa := by
  apply E.isFaceOf_of_zeroFixer_le C hFa hCa hne hΩ hne' hΩ'
  rw [← hsource₁, ← hsource₂]
  exact (φ.specialFibreImage_le_iff_integralPoints_le ψ hker₁ hker₂).mp hle

/-- Equality of the all-test actual special-fibre images recovers the full
apartment facets under the same characterization and congruence hypotheses. -/
theorem facet_eq_of_unramifiedSpecialFibreImage_eq
    (hFa : AffineRootSystem.IsFacet C.affineRoots Fa)
    (hCa : AffineRootSystem.IsFacet C.affineRoots Ca)
    (hne : Ω.Nonempty) (hΩ : Ω ⊆ Fa)
    (hne' : Ω'.Nonempty) (hΩ' : Ω' ⊆ Ca)
    (hsource₁ : source₁.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hsource₂ : source₂.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))
    (hker₁ : target.neutral.congruenceSubgroup ≤ source₁.neutral.integralPoints)
    (hker₂ : target.neutral.congruenceSubgroup ≤ source₂.neutral.integralPoints)
    (heq : SubgroupFunctor.range φ.specialFibreImageInclusion =
      SubgroupFunctor.range ψ.specialFibreImageInclusion) :
    Fa = Ca := by
  apply E.facet_eq_of_zeroFixer_eq C hFa hCa hne hΩ hne' hΩ'
  rw [← hsource₁, ← hsource₂]
  exact (φ.specialFibreImage_eq_iff_integralPoints_eq ψ hker₁ hker₂).mp heq

end Langlands.BruhatTits.IntegralModels

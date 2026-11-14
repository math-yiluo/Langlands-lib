import Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentRadicalImage
import Langlands.Geometry.Building.IntegerValuationNormalizerSharpReduction
import Langlands.Geometry.Building.UnramifiedSimplyConnectedNormalizerAffineWeylProof

/-! # Reduction of upstairs radical generation to singleton apartment sets -/

set_option maxHeartbeats 1600000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Sharp fixers on nonempty subsets of a facet agree with the fixer of any
one point of that subset. This uses AS4 over an arbitrary field. -/
theorem sharpFixer_eq_singleton_of_subset_facet
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    {Ω Fa : Set D.Apartment} (hFa : AffineRootSystem.IsFacet D.affineRoots Fa)
    {x : D.Apartment} (hx : x ∈ Ω) (hsub : Ω ⊆ Fa) :
    D.sharpFixer Ω = D.sharpFixer {x} := by
  unfold sharpFixer
  congr 1
  funext a
  exact (D.rootFixer_eq_of_nonempty_subset_facet hAS4 hFa ⟨x, hx⟩ hsub a).trans
    (D.rootFixer_eq_of_nonempty_subset_facet hAS4 hFa
      (Set.singleton_nonempty x) (Set.singleton_subset_iff.mpr (hsub hx)) a).symm

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)

/-- The zero subgroup's pointwise fixer is constant on every nonempty subset
of one facet; no boundedness of the facet is used. -/
theorem unramifiedZeroFixer_eq_singleton_of_subset_facet
    {Ω Fa : Set C.Apartment} (hFa : AffineRootSystem.IsFacet C.affineRoots Fa)
    {x : C.Apartment} (hx : x ∈ Ω) (hsub : Ω ⊆ Fa) :
    E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}) := by
  have hs := E.wholeApartmentZeroFixer_sup_sharpFixer_eq_of_simplyConnectedNormalizer
    C MaximalUnramified.simplyConnectedNormalizerAffineWeyl
    (Set.singleton_nonempty x) (fun f => by simp)
  have hsharp : C.sharpFixer Ω = C.sharpFixer {x} :=
    C.apartment.sharpFixer_eq_singleton_of_subset_facet
    C.affineRoot_mem_or_two_smul_mem hFa hx hsub
  apply le_antisymm
  · exact inf_le_inf_left _ (C.apartment.pointwiseFixer_image_anti
      (Set.singleton_subset_iff.mpr hx))
  · rw [hs, ← hsharp]
    exact sup_le
      (inf_le_inf_left _ (C.apartment.pointwiseFixer_image_anti (Set.subset_univ Ω)))
      (le_inf (E.sharpFixer_le_zeroPoints C Ω)
        (C.apartment.sharpFixer_le_pointwiseFixer_image Ω))

/-- The radical-generation problem restricted to singleton apartment subsets.
The common subgroup still precedes all points and all characterized models. -/
def UnramifiedUpstairsSingletonRadicalRootGenerationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G),
    ∃ H : Subgroup (rationalPoints G),
      H ≤ (rationalPoints.map C.centralizer.j).range ∧
      H ≤ E.zeroPoints ⊓ C.pointwiseFixer (Set.range C.apartmentMap) ∧
      ∀ (x : C.Apartment)
        (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G),
        N.IsSmooth →
        N.integralPoints =
          E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}) →
      ∀ (U : GroupScheme
          (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
        (i : U ⟶ N.specialFibre), IsUnipotentRadical i →
        ((rationalPoints.map i).range.comap N.reduction).map N.integralPointMap =
          H ⊔ ⨆ a : relativeRoots C.i, C.apartment.rootFixerPlus a {x}

/-- The singleton formula implies the original formula on every nonempty
subset of one facet, retaining the same common subgroup and actual model. -/
theorem unramifiedUpstairsRadicalRootGeneration_of_singleton
    (h : UnramifiedUpstairsSingletonRadicalRootGenerationStatement.{u}) :
    UnramifiedUpstairsRadicalRootGenerationStatement.{u} := by
  intro F _ _ _ _ G _ C E
  obtain ⟨H, hHcentralizer, hHfixer, hH⟩ := h F G C E
  refine ⟨H, hHcentralizer, hHfixer, ?_⟩
  intro Ω hΩ hfacet N hN hpoints U i hi
  obtain ⟨x, hx⟩ := hΩ
  obtain ⟨y, hsub⟩ := hfacet
  have hFa := AffineRootSystem.isFacet_facet C.affineRoots y
  have hsingle : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}) :=
    hpoints.trans (unramifiedZeroFixer_eq_singleton_of_subset_facet C E hFa hx hsub)
  have hroot (a : relativeRoots C.i) :
      C.apartment.rootFixerPlus a Ω = C.apartment.rootFixerPlus a {x} :=
    (C.apartment.rootFixerPlus_eq_of_nonempty_subset_facet
      C.affineRoot_mem_or_two_smul_mem hFa ⟨x, hx⟩ hsub a).trans
      (C.apartment.rootFixerPlus_eq_of_nonempty_subset_facet
        C.affineRoot_mem_or_two_smul_mem hFa (Set.singleton_nonempty x)
        (Set.singleton_subset_iff.mpr (hsub hx)) a).symm
  simp_rw [hroot]
  exact hH x N hN hsingle U i hi

end Langlands.BruhatTits.IntegralModels

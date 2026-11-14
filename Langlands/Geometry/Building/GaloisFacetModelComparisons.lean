import Langlands.Geometry.Building.GaloisIncidentFacets
import Langlands.Geometry.Building.UnramifiedFixedPointStabilizer
import Langlands.BruhatTits.IntegralModels.IntegerFacetModelMorphisms
import Langlands.BruhatTits.IntegralModels.RelativeComponentCoefficientComparison
import Langlands.GroupScheme.IntegralModel.SemilinearExtension

/-! # Actual coefficient comparisons for supplied integer-facet models -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  [Field K] [Algebra R K] [IsFractionRing R K]
  (k : Type u) [Field k] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  (P Q : IntegralModel R K (baseChanged k K G))
  (σ : K ≃ₐ[k] K)
  (a : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R)) [IsIso a]
  (hσ : galoisBaseMap k K σ ≫ Spec.algebraMap R K = Spec.algebraMap R K ≫ a)

/-- Covariance of the original point images constructs an actual coefficient
isomorphism between two supplied smooth models over a strictly Henselian DVR. -/
def galoisTwistIsoOfCovariance
    (hP : P.IsSmooth) (hQ : Q.IsSmooth)
    (hpoints : ∀ g : rationalPoints (baseChanged k K G),
      rationalConjugate k K G σ g ∈ Q.integralPoints ↔ g ∈ P.integralPoints) :
    (P.twist a (galoisBaseMap k K σ) hσ).Iso Q (galoisDescentIso k K G σ) := by
  let W := P.twist a (galoisBaseMap k K σ) hσ
  have hforward : ∀ g ∈ W.integralPoints,
      rationalPoints.map (galoisDescentIso k K G σ).hom g ∈ Q.integralPoints := by
    rintro g ⟨x, hx⟩
    obtain ⟨y, hy⟩ := baseChangeSectionHom_surjective a P.group x
    have h := twist_integralPointMap_galoisIso k G P σ a hσ y
    rw [hy, hx] at h
    exact h.symm ▸ (hpoints (P.integralPointMap y)).mpr ⟨y, rfl⟩
  have hback : ∀ g ∈ Q.integralPoints,
      rationalPoints.map (galoisDescentIso k K G σ).inv g ∈ W.integralPoints := by
    intro g hg
    have hp : rationalConjugate k K G σ.symm g ∈ P.integralPoints :=
      (hpoints _).mp (by simpa only [rationalConjugate_symm_apply] using hg)
    obtain ⟨x, hx⟩ := hp
    refine ⟨baseChangeSectionHom a P.group x, ?_⟩
    apply rationalPoints.map_iso_injective (galoisDescentIso k K G σ)
    rw [twist_integralPointMap_galoisIso, hx, rationalConjugate_symm_apply,
      rationalPoints.map_iso_inv_hom]
  exact Iso.ofHoms
    (Classical.choice (smoothHomExtension R K _ _ _ W Q
      (P.isSmooth_twist a (galoisBaseMap k K σ) hσ hP) hforward))
    (Classical.choice (smoothHomExtension R K _ _ _ Q W hQ hback))

end Langlands.GroupScheme.IntegralModel

namespace Langlands.Geometry.Building.KPApartmentData

open Langlands.BruhatTits.IntegralModels

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)
  [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left]
  {v : Valuation K (WithZero (Multiplicative ℤ))}
  (D : KPApartmentData
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i)
    (IntegerValuation.order v))
  (hD : GaloisStable k K i D)
  (hG : IsConnectedReductive (baseChanged k K G))
  (hi : IsMaximalSplitTorus
    (T := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i))
  (C : CentralizerDatum
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i))
  (h6 : IntegerValuation.IsOmegaCompatible v D C)

private instance coefficientComparison_extendedAffine :
    IsAffineHom (baseChanged k K G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

local notation "act" => galoisBuildingFacetAction k K i D hD hG hi C h6
local notation "rho" => galoisQuotientAction k K i D hD

include hG hi C h6

/-- The original pointwise facet fixers follow actual coefficient transport,
with preservation and reflection on the original rational-point group. -/
theorem rationalConjugate_mem_pointwiseFixer_galois_iff
    (σ : K ≃ₐ[k] K) (F : (integerBuildingData D hG hi C h6).BuildingFacet)
    (g : rationalPoints (baseChanged k K G)) :
    rationalConjugate k K G σ g ∈ (integerBuildingData D hG hi C h6).pointwiseFixer (act σ F).val ↔
      g ∈ (integerBuildingData D hG hi C h6).pointwiseFixer F.val := by
  rw [(integerBuildingData D hG hi C h6).apartment.mem_pointwiseFixer, (integerBuildingData D hG hi C h6).apartment.mem_pointwiseFixer,
    galoisBuildingFacetAction_val]
  constructor
  · intro h y hy
    exact (galoisQuotientAction_smul_eq_iff k K i D hD σ g y).mp
      (h (rho σ y) ⟨y, hy, rfl⟩)
  · rintro h y ⟨z, hz, rfl⟩
    exact (galoisQuotientAction_smul_eq_iff k K i D hD σ g z).mpr (h z hz)

variable (R : Type u) [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]
  (M : IntegerFacetModelData (K := K) (G := baseChanged k K G) (v := v)
    (integerBuildingData D hG hi C h6) R)
  (hpoints : ∀ F : (integerBuildingData D hG hi C h6).BuildingFacet,
    (M.model F).full.integralPoints =
    characterValuationKernel v (baseChanged k K G) ⊓ (integerBuildingData D hG hi C h6).pointwiseFixer F.val)

include hpoints

/-- Exact fixer-point descriptions give covariance of full model images;
no coefficient model comparison is assumed. -/
theorem full_integralPoints_galois_iff
    (σ : K ≃ₐ[k] K) (hv : ∀ x : K, v (σ x) = v x)
    (F : (integerBuildingData D hG hi C h6).BuildingFacet) (g : rationalPoints (baseChanged k K G)) :
    rationalConjugate k K G σ g ∈ (M.model (act σ F)).full.integralPoints ↔
      g ∈ (M.model F).full.integralPoints := by
  rw [hpoints, hpoints, Subgroup.mem_inf, Subgroup.mem_inf,
    rationalConjugate_mem_characterValuationKernel_iff k K G v σ hv,
    rationalConjugate_mem_pointwiseFixer_galois_iff k K i D hD hG hi C h6]

variable [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  (σ : K ≃ₐ[k] K) (hv : ∀ x : K, v (σ x) = v x)
  (a : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R)) [IsIso a]
  (hσ : galoisBaseMap k K σ ≫ Spec.algebraMap R K = Spec.algebraMap R K ≫ a)

/-- Construct the actual full-model coefficient comparison at every original
facet by the proved strict smooth extension theorem in both directions. -/
def fullModelGaloisTwistIso (F : (integerBuildingData D hG hi C h6).BuildingFacet) :
    ((M.model F).full.twist a (galoisBaseMap k K σ) hσ).Iso
      (M.model (act σ F)).full (galoisDescentIso k K G σ) :=
  IntegralModel.galoisTwistIsoOfCovariance k G (M.model F).full
    (M.model (act σ F)).full σ a hσ
    (M.model F).full_smooth (M.model (act σ F)).full_smooth
    (full_integralPoints_galois_iff k K i D hD hG hi C h6 R M hpoints σ hv F)

/-- Restriction constructs the actual neutral coefficient comparison. -/
def neutralModelGaloisTwistIso (F : (integerBuildingData D hG hi C h6).BuildingFacet) :
    ((M.model F).neutral.twist a (galoisBaseMap k K σ) hσ).Iso
      (M.model (act σ F)).neutral (galoisDescentIso k K G σ) :=
  (M.model F).neutralTwistIso (M.model (act σ F)) a (galoisBaseMap k K σ) hσ
    (galoisDescentIso k K G σ)
    (fullModelGaloisTwistIso k K i D hD hG hi C h6 R M hpoints σ hv a hσ F)

/-- Original neutral incidence maps commute with the constructed comparisons. -/
theorem neutralModelGaloisTwistIso_naturality
    (F E : (integerBuildingData D hG hi C h6).BuildingFacet) (hFE : (integerBuildingData D hG hi C h6).FacetPrecedes F E) :
    (neutralModelGaloisTwistIso k K i D hD hG hi C h6 R M hpoints σ hv a hσ E).iso.hom ≫
        (M.morphism (act σ F) (act σ E)
          (facetPrecedes_galoisBuildingFacetAction k K i D hD hG hi C h6 σ hFE)).neutral.hom =
      (GroupScheme.baseChange a).map (M.morphism F E hFE).neutral.hom ≫
        (neutralModelGaloisTwistIso k K i D hD hG hi C h6 R M hpoints σ hv a hσ F).iso.hom :=
  IntegralModel.twist_comparison_naturality _ _ _ _ a (galoisBaseMap k K σ) hσ
    (galoisDescentIso k K G σ) _ _ _ _

variable
  (r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
    Spec (CommRingCat.of (IsLocalRing.ResidueField R)))
  (hra : r ≫ IntegralModel.residueBaseMap R = IntegralModel.residueBaseMap R ≫ a)

/-- Specialization constructs the actual residue coefficient comparison. -/
def neutralResidueGaloisIso (F : (integerBuildingData D hG hi C h6).BuildingFacet) :
    (GroupScheme.baseChange r).obj (M.model F).neutral.specialFibre ≅
      (M.model (act σ F)).neutral.specialFibre :=
  IntegralModel.Iso.residueTwistIso (M.model F).neutral (M.model (act σ F)).neutral
    a (galoisBaseMap k K σ) hσ (galoisDescentIso k K G σ)
    (neutralModelGaloisTwistIso k K i D hD hG hi C h6 R M hpoints σ hv a hσ F) r hra

/-- The original residue incidence maps satisfy the coefficient square. -/
theorem neutralResidueGaloisIso_naturality
    (F E : (integerBuildingData D hG hi C h6).BuildingFacet) (hFE : (integerBuildingData D hG hi C h6).FacetPrecedes F E) :
    (neutralResidueGaloisIso k K i D hD hG hi C h6 R M hpoints σ hv a hσ r hra E).hom ≫
        (M.morphism (act σ F) (act σ E)
          (facetPrecedes_galoisBuildingFacetAction k K i D hD hG hi C h6 σ hFE)).neutralSpecialFibreMap =
      (GroupScheme.baseChange r).map (M.morphism F E hFE).neutralSpecialFibreMap ≫
        (neutralResidueGaloisIso k K i D hD hG hi C h6 R M hpoints σ hv a hσ r hra F).hom :=
  IntegralModel.residue_twist_comparison_naturality _ _ _ _ a (galoisBaseMap k K σ)
    hσ (galoisDescentIso k K G σ) _ _ _ _ r hra

/-- Actual models with full fixer-point descriptions admit actual full and
neutral coefficient comparisons, without supplied comparison isomorphisms. -/
def GaloisFacetModelComparisonsStatement : Prop :=
  ∀ F : (integerBuildingData D hG hi C h6).BuildingFacet,
    Nonempty (((M.model F).full.twist a (galoisBaseMap k K σ) hσ).Iso
      (M.model (act σ F)).full (galoisDescentIso k K G σ)) ∧
    Nonempty (((M.model F).neutral.twist a (galoisBaseMap k K σ) hσ).Iso
      (M.model (act σ F)).neutral (galoisDescentIso k K G σ))

include hv in
/-- The comparison assertion follows from actual point covariance. -/
theorem galoisFacetModelComparisons :
    GaloisFacetModelComparisonsStatement k K i D hD hG hi C h6 R M σ a hσ := by
  intro F
  exact ⟨⟨fullModelGaloisTwistIso k K i D hD hG hi C h6 R M hpoints σ hv a hσ F⟩,
    ⟨neutralModelGaloisTwistIso k K i D hD hG hi C h6 R M hpoints σ hv a hσ F⟩⟩

end Langlands.Geometry.Building.KPApartmentData

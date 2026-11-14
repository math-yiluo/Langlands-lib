import Langlands.Geometry.Building.GaloisFacetModelComparisons
import Langlands.Geometry.Building.GaloisFacetImageNaturality

/-! # Actual residue coefficient comparisons at a Gamma-facet -/

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

variable (R : Type u) [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]
  (M : IntegerFacetModelData (K := K) (G := baseChanged k K G) (v := v)
    (integerBuildingData D hG hi C h6) R)
  (hpoints : ∀ F : (integerBuildingData D hG hi C h6).BuildingFacet,
    (M.model F).full.integralPoints =
    characterValuationKernel v (baseChanged k K G) ⊓ (integerBuildingData D hG hi C h6).pointwiseFixer F.val)

variable [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  (E : GaloisFacet k K i D hD hG hi C h6)
  (hv : ∀ (σ : K ≃ₐ[k] K) (x : K), v (σ x) = v x)
  (a : (K ≃ₐ[k] K) → (Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R)))
  [∀ σ, IsIso (a σ)]
  (hσ : ∀ σ, galoisBaseMap k K σ ≫ Spec.algebraMap R K =
    Spec.algebraMap R K ≫ a σ)
  (f : Type u) [Field f] [Algebra f (IsLocalRing.ResidueField R)]
  (residueAction : (K ≃ₐ[k] K) →*
    (IsLocalRing.ResidueField R ≃ₐ[f] IsLocalRing.ResidueField R))
  (hra : ∀ σ, galoisBaseMap f (IsLocalRing.ResidueField R) (residueAction σ) ≫
    IntegralModel.residueBaseMap R = IntegralModel.residueBaseMap R ≫ a σ)

local notation "L" => IsLocalRing.ResidueField R
local notation "incAct" => galoisIncidentFacetAction k K i D hD hG hi C h6 E

omit [IsDiscreteValuationRing R] [IsSepClosed (IsLocalRing.ResidueField R)] in
private theorem neutralSpecialFibreMap_comp_eqToHom
    {E₁ E₂ F : (integerBuildingData D hG hi C h6).BuildingFacet}
    (h : E₁ = E₂)
    (h₁ : (integerBuildingData D hG hi C h6).FacetPrecedes E₁ F)
    (h₂ : (integerBuildingData D hG hi C h6).FacetPrecedes E₂ F) :
    (M.morphism E₁ F h₁).neutralSpecialFibreMap ≫
        eqToHom (congrArg (fun E => (M.model E).neutral.specialFibre) h) =
      (M.morphism E₂ F h₂).neutralSpecialFibreMap := by
  subst E₂
  simp

/-- The actual translated incident-facet model has a residue coefficient
comparison constructed from its full integral-point image. -/
def incidentResidueGaloisIso (σ : K ≃ₐ[k] K)
    (F : (integerBuildingData D hG hi C h6).IncidentFacets E.val) :
    (GroupScheme.baseChange (galoisBaseMap f L (residueAction σ))).obj
        (M.model F.val).neutral.specialFibre ≅
      (M.model (incAct σ F).val).neutral.specialFibre :=
  neutralResidueGaloisIso k K i D hD hG hi C h6 R M hpoints σ (hv σ) (a σ)
    (hσ σ) (galoisBaseMap f L (residueAction σ)) (hra σ) F.val

/-- Galois invariance of the original Gamma-facet closes its constructed
residue comparison back into its own special fibre. -/
def fixedFacetResidueGaloisIso (σ : K ≃ₐ[k] K) :
    (GroupScheme.baseChange (galoisBaseMap f L (residueAction σ))).obj
        (M.model E.val).neutral.specialFibre ≅ (M.model E.val).neutral.specialFibre :=
  neutralResidueGaloisIso k K i D hD hG hi C h6 R M hpoints σ (hv σ) (a σ)
    (hσ σ) (galoisBaseMap f L (residueAction σ)) (hra σ) E.val ≪≫
      eqToIso (congrArg (fun F => (M.model F).neutral.specialFibre)
        (galoisBuildingFacetAction_galoisFacet k K i D hD hG hi C h6 E σ))

/-- The original incidence morphisms commute with these constructed source
and target comparisons at a Gamma-facet. -/
theorem incidentResidueGaloisIso_naturality (σ : K ≃ₐ[k] K)
    (F : (integerBuildingData D hG hi C h6).IncidentFacets E.val) :
    (incidentResidueGaloisIso k K i D hD hG hi C h6 R M hpoints E hv a hσ f
      residueAction hra σ F).hom ≫
        (M.morphism E.val (incAct σ F).val (incAct σ F).property).neutralSpecialFibreMap =
      (GroupScheme.baseChange (galoisBaseMap f L (residueAction σ))).map
          (M.morphism E.val F.val F.property).neutralSpecialFibreMap ≫
        (fixedFacetResidueGaloisIso k K i D hD hG hi C h6 R M hpoints E hv a hσ f
          residueAction hra σ).hom := by
  have h := neutralResidueGaloisIso_naturality k K i D hD hG hi C h6 R M hpoints
    σ (hv σ) (a σ) (hσ σ) (galoisBaseMap f L (residueAction σ)) (hra σ)
    E.val F.val F.property
  dsimp only [incidentResidueGaloisIso, fixedFacetResidueGaloisIso, Iso.trans_hom,
    eqToIso.hom]
  change _ ≫ _ = _ ≫ _ ≫ _
  rw [← Category.assoc, ← h, Category.assoc,
    neutralSpecialFibreMap_comp_eqToHom k K i D hG hi C h6 R M
      (galoisBuildingFacetAction_galoisFacet k K i D hD hG hi C h6 E σ)
      (facetPrecedes_galoisBuildingFacetAction k K i D hD hG hi C h6 σ F.property)
      (incAct σ F).property]
  rfl

variable
  (Q : SpecialFibreQuotientData (R := R) (K := K) (G := baseChanged k K G)
    (M.model (K := K) (G := baseChanged k K G) (v := v) E.val))
  (H : GroupScheme (Spec (CommRingCat.of f))) [IsAffineHom H.X.hom]
  (e : Q.quotient ≅ baseChanged f (IsLocalRing.ResidueField R) H)

/-- The remaining quotient obligation, now expressed using the actual target
comparison constructed from integral points. It supplies no model comparison
isomorphism or incidence square. -/
def FixedFacetResidueQuotientSquare : Prop :=
  ∀ σ : K ≃ₐ[k] K,
    (fixedFacetResidueGaloisIso k K i D hD hG hi C h6 R M hpoints E hv a hσ f
      residueAction hra σ).hom ≫ Q.projection ≫ e.hom =
      (GroupScheme.baseChange (galoisBaseMap f L (residueAction σ))).map
          (Q.projection ≫ e.hom) ≫
        (descentBaseChangeIso (algebraBaseMap f L)
          (galoisBaseMap f L (residueAction σ))
          (galoisBaseMap_over f L (residueAction σ)) H).hom

/-- Full integral-point descriptions construct every coefficient comparison
field except the explicitly separate quotient square. -/
def residueCoefficientComparisonsOfQuotientSquare
    (hquot : FixedFacetResidueQuotientSquare k K i D hD hG hi C h6 R M hpoints E
      hv a hσ f residueAction hra Q H e) :
    ResidueCoefficientComparisonData k K i D hD hG hi C h6 R E M Q f H e
      residueAction where
  sourceIso := incidentResidueGaloisIso k K i D hD hG hi C h6 R M hpoints E hv a hσ
    f residueAction hra
  targetIso := fixedFacetResidueGaloisIso k K i D hD hG hi C h6 R M hpoints E hv a hσ
    f residueAction hra
  map_comm := incidentResidueGaloisIso_naturality k K i D hD hG hi C h6 R M hpoints
    E hv a hσ f residueAction hra
  quotient_comm := hquot

/-- Only quotient compatibility remains to get the actual all-test residue
image covariance from the full fixer-point descriptions. -/
theorem hasGaloisResidueImageCompatibility_of_quotientSquare
    (hquot : FixedFacetResidueQuotientSquare k K i D hD hG hi C h6 R M hpoints E
      hv a hσ f residueAction hra Q H e) :
    HasGaloisResidueImageCompatibility k K i D hD hG hi C h6 R E M Q f H e
      residueAction :=
  hasGaloisResidueImageCompatibility_of_coefficientComparisons
    k K i D hD hG hi C h6 R E M Q f H e residueAction
    (residueCoefficientComparisonsOfQuotientSquare k K i D hD hG hi C h6 R M
      hpoints E hv a hσ f residueAction hra Q H e hquot)

/-- The constructed actual residue comparisons and incidence squares reduce
image covariance to the separate quotient square. -/
def GaloisFacetResidueComparisonsStatement : Prop :=
  FixedFacetResidueQuotientSquare k K i D hD hG hi C h6 R M hpoints E hv a hσ f
    residueAction hra Q H e →
      Nonempty (ResidueCoefficientComparisonData k K i D hD hG hi C h6 R E M Q f H e
        residueAction) ∧
      HasGaloisResidueImageCompatibility k K i D hD hG hi C h6 R E M Q f H e
        residueAction

/-- The residue comparison assertion uses the actual constructed maps. -/
theorem galoisFacetResidueComparisons :
    GaloisFacetResidueComparisonsStatement k K i D hD hG hi C h6 R M hpoints E hv a
      hσ f residueAction hra Q H e := by
  intro hquot
  exact ⟨⟨residueCoefficientComparisonsOfQuotientSquare k K i D hD hG hi C h6 R M
    hpoints E hv a hσ f residueAction hra Q H e hquot⟩,
    hasGaloisResidueImageCompatibility_of_quotientSquare k K i D hD hG hi C h6 R M
      hpoints E hv a hσ f residueAction hra Q H e hquot⟩

end Langlands.Geometry.Building.KPApartmentData

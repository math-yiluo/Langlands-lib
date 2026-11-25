import Langlands.Geometry.Building.IntegralModelSplitTorusApartment
import Langlands.GroupScheme.Torus.UnipotentQuotientMaximalSplit
import Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelTorus

/-! # Apartment containment from bounded generic tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme
open Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [ValuationRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (M : IntegralModel R K G) [Smooth M.group.X.hom]
    [ConnectedSpace
      ((GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj
        M.group).X.left]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (hv : ∀ a : Rˣ, v (algebraMap R K (a : R)) = 1)
    {T₁ T₂ : CommGroupScheme (Spec (CommRingCat.of K))}
    {i₁ : T₁.toGrp ⟶ G} {i₂ : T₂.toGrp ⟶ G}

include hv

/-- Bounded generic maximal split tori are conjugate by an actual model
integral point, with the original generic source tori retained. -/
theorem exists_integralPoint_conjugacy_of_bounded_maximalSplitTori
    (hG : IsConnectedReductive G)
    (hi₁ : IsMaximalSplitTorus i₁) (hi₂ : IsMaximalSplitTorus i₂)
    (hb₁ : (characterValuationKernel v T₁.toGrp).map (rationalPoints.map i₁) ≤
      M.integralPoints)
    (hb₂ : (characterValuationKernel v T₂.toGrp).map (rationalPoints.map i₂) ≤
      M.integralPoints) :
    ∃ g : rationalPoints G, g ∈ M.integralPoints ∧
      ∃ e : T₁ ≅ T₂,
        i₁ ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ i₂ := by
  obtain ⟨U₁, j₁, e₁, hU₁, hj₁, hgen₁⟩ :=
    SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_bounded
      M v hv i₁ hi₁.1.1 hi₁.1.2 hb₁
  obtain ⟨U₂, j₂, e₂, hU₂, hj₂, hgen₂⟩ :=
    SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_bounded
      M v hv i₂ hi₂.1.1 hi₂.1.2 hb₂
  let a₁ : ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj U₁).toGrp ≅
      T₁.toGrp :=
    { hom := CommGroupScheme.groupHom e₁.hom
      inv := CommGroupScheme.groupHom e₁.inv
      hom_inv_id := congrArg CommGroupScheme.groupHom e₁.hom_inv_id
      inv_hom_id := congrArg CommGroupScheme.groupHom e₁.inv_hom_id }
  let a₂ : ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj U₂).toGrp ≅
      T₂.toGrp :=
    { hom := CommGroupScheme.groupHom e₂.hom
      inv := CommGroupScheme.groupHom e₂.inv
      hom_inv_id := congrArg CommGroupScheme.groupHom e₂.hom_inv_id
      inv_hom_id := congrArg CommGroupScheme.groupHom e₂.inv_hom_id }
  have hmax₁ : IsMaximalSplitTorus (M.genericTorusMap U₁ j₁) := by
    rw [hgen₁]
    exact hi₁.iso_comp a₁
  have hmax₂ : IsMaximalSplitTorus (M.genericTorusMap U₂ j₂) := by
    rw [hgen₂]
    exact hi₂.iso_comp a₂
  obtain ⟨g, hg, e, he⟩ :=
    M.exists_integralPoint_genericTorusMap_conjugacy hG hU₁ hU₂ hj₁ hj₂ hmax₁ hmax₂
  let eK := (CommGroupScheme.baseChange (Spec.algebraMap R K)).mapIso e
  refine ⟨g, hg, e₁.symm ≪≫ eK ≪≫ e₂, ?_⟩
  rw [hgen₁, hgen₂] at he
  change i₁ ≫ (G.innerIso g).hom =
    (a₁.inv ≫ CommGroupScheme.groupHom eK.hom) ≫ a₂.hom ≫ i₂
  change (a₁.hom ≫ i₁) ≫ (G.innerIso g).hom =
    CommGroupScheme.groupHom eK.hom ≫ a₂.hom ≫ i₂ at he
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun f => a₁.inv ≫ f) he

end Langlands.GroupScheme.IntegralModel

namespace Langlands.Geometry.Building

variable {R K : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [ValuationRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    (M : IntegralModel R K G) [Smooth M.group.X.hom]
    [ConnectedSpace
      ((GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj
        M.group).X.left]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (hv : ∀ a : Rˣ, v (algebraMap R K (a : R)) = 1)
    {T₁ T₂ : CommGroupScheme (Spec (CommRingCat.of K))}
    {i₁ : T₁.toGrp ⟶ G} {i₂ : T₂.toGrp ⟶ G}

include hv

/-- The second bounded generic torus has an actual conjugate apartment
containing every subset of the first apartment fixed by the model. -/
theorem exists_integralPoint_conjugateApartment_contains_of_bounded
    (hG : IsConnectedReductive G)
    (hi₁ : IsMaximalSplitTorus i₁) (hi₂ : IsMaximalSplitTorus i₂)
    (hb₁ : (characterValuationKernel v T₁.toGrp).map (rationalPoints.map i₁) ≤
      M.integralPoints)
    (hb₂ : (characterValuationKernel v T₂.toGrp).map (rationalPoints.map i₂) ≤
      M.integralPoints) :
    letI := mono_of_isMaximalSplitTorus hi₁
    letI := mono_of_isMaximalSplitTorus hi₂
    ∀ {ω : Kˣ → ℝ} (D : KPApartmentData i₁ ω) (Y : Set D.ReducedBuilding),
      Y ⊆ Set.range D.apartmentMap →
      M.integralPoints ≤ D.pointwiseFixer Y →
      ∃ g : rationalPoints G, g ∈ M.integralPoints ∧
        ∃ (e : T₁ ≅ T₂)
          (he : i₁ ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ i₂),
          (∀ y ∈ Y, ∃ x : D.Apartment, y = g • D.apartmentMap x) ∧
            Y ⊆ Set.range (D.conjugateApartmentMap e g he) := by
  have := mono_of_isMaximalSplitTorus hi₁
  have := mono_of_isMaximalSplitTorus hi₂
  intro ω D Y hY hfix
  obtain ⟨g, hg, e, he⟩ :=
    M.exists_integralPoint_conjugacy_of_bounded_maximalSplitTori v hv hG hi₁ hi₂ hb₁ hb₂
  have hgfix := D.mem_pointwiseFixer.mp (hfix hg)
  refine ⟨g, hg, e, he, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx⟩ := hY hy
    exact ⟨x, (hgfix y hy).symm.trans (congrArg (fun z => g • z) hx.symm)⟩
  · intro y hy
    obtain ⟨x, hx⟩ := hY hy
    refine ⟨D.apartmentTransportEquiv e (G.innerIso g) he x, ?_⟩
    rw [D.conjugateApartmentMap_transport, hx, hgfix y hy]

end Langlands.Geometry.Building

namespace Langlands.Geometry.Building

open Langlands.LocalGalois.Separable
open Langlands.BruhatTits.IntegralModels

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom H.X.hom]

private local instance : HenselianLocalRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsHenselian F

private local instance : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra

private local instance : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).isAlgClosed

private local instance : IsDiscreteValuationRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)

/-- The actual apartment unit bound supplies the first bounded generic torus
over the maximal unramified field. The second torus and its bound are supplied. -/
theorem exists_integralPoint_conjugateApartment_contains_of_unramified_bounded
    (C : MaximalUnramified.BuildingData F H) (E : UnramifiedZeroDatum F H)
    (Ω : Set C.Apartment)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H)
    [Smooth M.group.X.hom] [ConnectedSpace M.specialFibre.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    {i : T.toGrp ⟶ H} (hi : IsMaximalSplitTorus i)
    (hpts : E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) ≤ M.integralPoints)
    (hb : (characterValuationKernel (MaximalUnramified.valuation F) T.toGrp).map
      (rationalPoints.map i) ≤ M.integralPoints)
    (hfix : M.integralPoints ≤ C.pointwiseFixer (C.apartmentMap '' Ω)) :
    letI := mono_of_isMaximalSplitTorus hi
    ∃ g : rationalPoints H, g ∈ M.integralPoints ∧
      ∃ (e : C.S ≅ T)
        (he : C.i ≫ (H.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ i),
        (∀ y ∈ C.apartmentMap '' Ω, ∃ x : C.Apartment, y = g • C.apartmentMap x) ∧
          C.apartmentMap '' Ω ⊆ Set.range (C.apartment.conjugateApartmentMap e g he) := by
  have := mono_of_isMaximalSplitTorus hi
  have : ConnectedSpace
      ((GroupScheme.baseChange (Spec.algebraMap (fixedFieldIntegers F)
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj M.group).X.left := by
    change ConnectedSpace M.specialFibre.X.left
    infer_instance
  exact exists_integralPoint_conjugateApartment_contains_of_bounded
    M (MaximalUnramified.valuation F) (SpecialTorusIntegralModel.valuation_units_eq_one F)
    C.isConnectedReductive C.isMaximalSplitTorus hi
    ((map_characterValuationKernel_le_zeroPoints_inf_pointwiseFixer C E Ω).trans hpts)
    hb C.apartment (C.apartmentMap '' Ω)
    (by rintro _ ⟨x, _, rfl⟩; exact ⟨x, rfl⟩) hfix

end Unramified

/-- Bounded generic maximal split tori give containment in an actual conjugate
apartment, retaining the original generic source tori. -/
def BoundedTorusApartmentStatement : Prop :=
  ∀ (R K Γ₀ : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [ValuationRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] [Field K]
    [Algebra R K] [IsFractionRing R K] [LinearOrderedCommGroupWithZero Γ₀]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    (M : IntegralModel R K G) [Smooth M.group.X.hom]
    [ConnectedSpace M.specialFibre.X.left]
    (v : Valuation K Γ₀) (_ : ∀ a : Rˣ, v (algebraMap R K (a : R)) = 1)
    (T₁ T₂ : CommGroupScheme (Spec (CommRingCat.of K)))
    (i₁ : T₁.toGrp ⟶ G) (i₂ : T₂.toGrp ⟶ G)
    (_ : IsConnectedReductive G)
    (hi₁ : IsMaximalSplitTorus i₁) (hi₂ : IsMaximalSplitTorus i₂),
    (characterValuationKernel v T₁.toGrp).map (rationalPoints.map i₁) ≤ M.integralPoints →
    (characterValuationKernel v T₂.toGrp).map (rationalPoints.map i₂) ≤ M.integralPoints →
    letI := mono_of_isMaximalSplitTorus hi₁
    letI := mono_of_isMaximalSplitTorus hi₂
    ∀ (ω : Kˣ → ℝ) (D : KPApartmentData i₁ ω) (Y : Set D.ReducedBuilding),
      Y ⊆ Set.range D.apartmentMap →
      M.integralPoints ≤ D.pointwiseFixer Y →
      ∃ g : rationalPoints G, g ∈ M.integralPoints ∧
        ∃ (e : T₁ ≅ T₂)
          (he : i₁ ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ i₂),
          (∀ y ∈ Y, ∃ x : D.Apartment, y = g • D.apartmentMap x) ∧
            Y ⊆ Set.range (D.conjugateApartmentMap e g he)

/-- Construct closed integral split extensions, apply integral conjugacy, and
transport the same fixed subset through the resulting original-source map. -/
theorem boundedTorusApartment : BoundedTorusApartmentStatement.{u} := by
  intro R K Γ₀ _ _ _ _ _ _ _ _ _ _ G _ M _ _ v hv T₁ T₂ i₁ i₂ hG hi₁ hi₂ hb₁ hb₂ ω
  have : ConnectedSpace
      ((GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj
        M.group).X.left := by
    change ConnectedSpace M.specialFibre.X.left
    infer_instance
  exact exists_integralPoint_conjugateApartment_contains_of_bounded M v hv hG hi₁ hi₂ hb₁ hb₂

end Langlands.Geometry.Building

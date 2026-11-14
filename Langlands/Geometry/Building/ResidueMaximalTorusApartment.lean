import Langlands.Geometry.Building.IntegralModelSplitTorusApartment
import Langlands.GroupScheme.Torus.UnipotentQuotientMaximalSplit
import Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelTorus

/-! # Generic maximality and apartments from a maximal residue torus -/

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
    {T : CommGroupScheme (Spec (CommRingCat.of K))} {i : T.toGrp ⟶ G}
    {U : CommGroupScheme (Spec (CommRingCat.of R))} (j : U.toGrp ⟶ M.group)

include hv

/-- A supplied integral split torus maximal on the actual residue fibre has
maximal split generic fibre, and is integrally conjugate to the bounded
generic maximal split torus with its original source retained. -/
theorem exists_integralPoint_conjugacy_of_bounded_residueMaximal
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hb : (characterValuationKernel v T.toGrp).map (rationalPoints.map i) ≤
      M.integralPoints)
    (hU : IsSplitTorus U.toGrp)
    (hres : IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj U)
      ((GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).map j)) :
    IsMaximalSplitTorus (M.genericTorusMap U j) ∧
      ∃ g : rationalPoints G, g ∈ M.integralPoints ∧
        ∃ e : T ≅ (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj U,
          i ≫ (G.innerIso g).hom =
            CommGroupScheme.groupHom e.hom ≫ M.genericTorusMap U j := by
  obtain ⟨U₁, j₁, e₁, hU₁, hj₁, hgen₁⟩ :=
    SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_bounded
      M v hv i hi.1.1 hi.1.2 hb
  let a₁ : ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj U₁).toGrp ≅
      T.toGrp :=
    { hom := CommGroupScheme.groupHom e₁.hom
      inv := CommGroupScheme.groupHom e₁.inv
      hom_inv_id := congrArg CommGroupScheme.groupHom e₁.hom_inv_id
      inv_hom_id := congrArg CommGroupScheme.groupHom e₁.inv_hom_id }
  have hmax₁ : IsMaximalSplitTorus (M.genericTorusMap U₁ j₁) := by
    rw [hgen₁]
    exact hi.iso_comp a₁
  have hres₁ := isMaximalTorus_specialFibre_of_generic hG M hU₁ hj₁ hmax₁
  obtain ⟨gR, eR, heR⟩ := exists_henselian_splitTorus_conjugacy j₁ j hU₁ hU
    inferInstance IsLocalRing.residue_surjective hres₁ hres
  let g := M.integralPointMap gR
  let eK := (CommGroupScheme.baseChange (Spec.algebraMap R K)).mapIso eR
  let e := e₁.symm ≪≫ eK
  have he : i ≫ (G.innerIso g).hom =
      CommGroupScheme.groupHom e.hom ≫ M.genericTorusMap U j := by
    have h := M.genericTorusMap_conjugation gR eR heR
    rw [hgen₁] at h
    change i ≫ (G.innerIso g).hom =
      (a₁.inv ≫ CommGroupScheme.groupHom eK.hom) ≫ M.genericTorusMap U j
    change (a₁.hom ≫ i) ≫ (G.innerIso g).hom =
      CommGroupScheme.groupHom eK.hom ≫ M.genericTorusMap U j at h
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun f => a₁.inv ≫ f) h
  let a : T.toGrp ≅ ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj U).toGrp :=
    { hom := CommGroupScheme.groupHom e.hom
      inv := CommGroupScheme.groupHom e.inv
      hom_inv_id := congrArg CommGroupScheme.groupHom e.hom_inv_id
      inv_hom_id := congrArg CommGroupScheme.groupHom e.inv_hom_id }
  have hconj : SubgroupConjugate i (M.genericTorusMap U j) := ⟨g, a, he⟩
  exact ⟨hconj.isMaximalSplitTorus_iff.mp hi, g, ⟨gR, rfl⟩, e, he⟩

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
    {T : CommGroupScheme (Spec (CommRingCat.of K))} {i : T.toGrp ⟶ G}
    {U : CommGroupScheme (Spec (CommRingCat.of R))} (j : U.toGrp ⟶ M.group)

include hv

/-- Residue maximality supplies generic maximality and actual conjugate
apartment containment, with no generic maximality or bound assumed for j. -/
theorem exists_conjugateApartment_contains_of_bounded_residueMaximal
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hb : (characterValuationKernel v T.toGrp).map (rationalPoints.map i) ≤
      M.integralPoints)
    (hU : IsSplitTorus U.toGrp)
    (hres : IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj U)
      ((GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).map j)) :
    ∃ hmax : IsMaximalSplitTorus (M.genericTorusMap U j),
      letI := mono_of_isMaximalSplitTorus hi
      letI := mono_of_isMaximalSplitTorus hmax
      ∀ {ω : Kˣ → ℝ} (D : KPApartmentData i ω) (Y : Set D.ReducedBuilding),
        Y ⊆ Set.range D.apartmentMap →
        M.integralPoints ≤ D.pointwiseFixer Y →
        ∃ g : rationalPoints G, g ∈ M.integralPoints ∧
          ∃ (e : T ≅ (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj U)
            (he : i ≫ (G.innerIso g).hom =
              CommGroupScheme.groupHom e.hom ≫ M.genericTorusMap U j),
            (∀ y ∈ Y, ∃ x : D.Apartment, y = g • D.apartmentMap x) ∧
              Y ⊆ Set.range (D.conjugateApartmentMap e g he) := by
  obtain ⟨hmax, g, hg, e, he⟩ :=
    M.exists_integralPoint_conjugacy_of_bounded_residueMaximal v hv j hG hi hb hU hres
  refine ⟨hmax, ?_⟩
  have := mono_of_isMaximalSplitTorus hi
  have := mono_of_isMaximalSplitTorus hmax
  intro ω D Y hY hfix
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

local instance : HenselianLocalRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsHenselian F

local instance : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra

local instance : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).isAlgClosed

local instance : IsDiscreteValuationRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)

/-- An actual unramified apartment bound and a supplied residue-maximal
integral split torus give generic maximality and apartment containment. -/
theorem exists_conjugateApartment_contains_of_unramified_residueMaximal
    (C : MaximalUnramified.BuildingData F H) (E : UnramifiedZeroDatum F H)
    (Ω : Set C.Apartment)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H)
    [Smooth M.group.X.hom] [ConnectedSpace M.specialFibre.X.left]
    {U : CommGroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F)))}
    (j : U.toGrp ⟶ M.group) (hU : IsSplitTorus U.toGrp)
    (hres : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap (fixedFieldIntegers F)
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj U)
      ((GroupScheme.baseChange (Spec.algebraMap (fixedFieldIntegers F)
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).map j))
    (hpts : E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) ≤ M.integralPoints)
    (hfix : M.integralPoints ≤ C.pointwiseFixer (C.apartmentMap '' Ω)) :
    ∃ hmax : IsMaximalSplitTorus (M.genericTorusMap U j),
      letI := mono_of_isMaximalSplitTorus hmax
      ∃ g : rationalPoints H, g ∈ M.integralPoints ∧
        ∃ (e : C.S ≅ (CommGroupScheme.baseChange
            (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).obj U)
          (he : C.i ≫ (H.innerIso g).hom =
            CommGroupScheme.groupHom e.hom ≫ M.genericTorusMap U j),
          (∀ y ∈ C.apartmentMap '' Ω, ∃ x : C.Apartment, y = g • C.apartmentMap x) ∧
            C.apartmentMap '' Ω ⊆ Set.range (C.apartment.conjugateApartmentMap e g he) := by
  have : ConnectedSpace
      ((GroupScheme.baseChange (Spec.algebraMap (fixedFieldIntegers F)
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj M.group).X.left := by
    change ConnectedSpace M.specialFibre.X.left
    infer_instance
  obtain ⟨hmax, hapt⟩ := exists_conjugateApartment_contains_of_bounded_residueMaximal
    M (MaximalUnramified.valuation F) (SpecialTorusIntegralModel.valuation_units_eq_one F)
    j C.isConnectedReductive C.isMaximalSplitTorus
    ((map_characterValuationKernel_le_zeroPoints_inf_pointwiseFixer C E Ω).trans hpts)
    hU hres
  refine ⟨hmax, ?_⟩
  have := mono_of_isMaximalSplitTorus hmax
  exact hapt C.apartment (C.apartmentMap '' Ω)
    (by rintro _ ⟨x, _, rfl⟩; exact ⟨x, rfl⟩) hfix

end Unramified

/-- A maximal actual residue map of an integral split torus gives maximal
split generic fibre and apartment containment from one bounded generic torus. -/
def ResidueMaximalTorusApartmentStatement : Prop :=
  ∀ (R K Γ₀ : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [ValuationRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] [Field K]
    [Algebra R K] [IsFractionRing R K] [LinearOrderedCommGroupWithZero Γ₀]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    (M : IntegralModel R K G) [Smooth M.group.X.hom]
    [ConnectedSpace M.specialFibre.X.left]
    (v : Valuation K Γ₀) (_ : ∀ a : Rˣ, v (algebraMap R K (a : R)) = 1)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G)
    (U : CommGroupScheme (Spec (CommRingCat.of R))) (j : U.toGrp ⟶ M.group)
    (_ : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    (characterValuationKernel v T.toGrp).map (rationalPoints.map i) ≤ M.integralPoints →
    IsSplitTorus U.toGrp →
    IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj U)
      ((GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).map j) →
    ∃ hmax : IsMaximalSplitTorus (M.genericTorusMap U j),
      letI := mono_of_isMaximalSplitTorus hi
      letI := mono_of_isMaximalSplitTorus hmax
      ∀ (ω : Kˣ → ℝ) (D : KPApartmentData i ω) (Y : Set D.ReducedBuilding),
        Y ⊆ Set.range D.apartmentMap →
        M.integralPoints ≤ D.pointwiseFixer Y →
        ∃ g : rationalPoints G, g ∈ M.integralPoints ∧
          ∃ (e : T ≅ (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj U)
            (he : i ≫ (G.innerIso g).hom =
              CommGroupScheme.groupHom e.hom ≫ M.genericTorusMap U j),
            (∀ y ∈ Y, ∃ x : D.Apartment, y = g • D.apartmentMap x) ∧
              Y ⊆ Set.range (D.conjugateApartmentMap e g he)

/-- Extend the bounded torus, conjugate its maximal residue fibre to the
supplied one, and transport generic maximality and the actual apartment. -/
theorem residueMaximalTorusApartment : ResidueMaximalTorusApartmentStatement.{u} := by
  intro R K Γ₀ _ _ _ _ _ _ _ _ _ _ G _ M _ _ v hv T i U j hG hi hb hU hres
  have : ConnectedSpace
      ((GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj
        M.group).X.left := by
    change ConnectedSpace M.specialFibre.X.left
    infer_instance
  obtain ⟨hmax, hapt⟩ :=
    exists_conjugateApartment_contains_of_bounded_residueMaximal M v hv j hG hi hb hU hres
  exact ⟨hmax, fun ω => hapt⟩

end Langlands.Geometry.Building

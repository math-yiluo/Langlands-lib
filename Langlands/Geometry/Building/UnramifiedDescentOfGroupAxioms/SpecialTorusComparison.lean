import Langlands.Geometry.Building.UnramifiedDescentOfGroupAxioms.ApartmentIndependence
import Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentProof
import Langlands.Geometry.Building.ConjugateApartmentGaloisComparison
import Langlands.Geometry.Building.TorusUnitFixationTransport
import Langlands.Geometry.Building.IntegerValuationBuildingBasedTransport
import Langlands.Geometry.Building.UnramifiedDescentOfGroupAxiomsStatement
import Langlands.Geometry.Building.SpecialTorusExistenceProof

/-! # Fixed-apartment and affine-root comparison for every special torus -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.UnramifiedBuildingDescent

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local notation "𝕂" => inertiaFixedField F
local notation "G_K" => baseChanged F 𝕂 G
local notation "b" => algebraBaseMap F 𝕂
local notation "vK" => MaximalUnramified.valuation F

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

omit [IsAffineHom G.X.hom] in
private theorem baseChange_factor {S T : CommGroupScheme (Spec (CommRingCat.of F))}
    {i : S.toGrp ⟶ G} {j : T.toGrp ⟶ G} {f : S ⟶ T}
    (hf : CommGroupScheme.groupHom f ≫ j = i) :
    CommGroupScheme.groupHom ((CommGroupScheme.baseChange b).map f) ≫
      (GroupScheme.baseChange b).map j = (GroupScheme.baseChange b).map i := by
  rw [← hf, Functor.map_comp]
  rfl

set_option maxHeartbeats 10000000 in
/-- A special torus containing the reference split torus gives another chart
of the same fixed apartment, with the cocharacter derivative and root pullback. -/
theorem compareSpecialTorus (B : ValuationBuildingData G)
    (hB : ∃ R : B.PolysimplicialRealization, B.SatisfiesBuildingAxiom R)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
    (f : B.S ⟶ T) (hf : CommGroupScheme.groupHom f ≫ i = B.i)
    (hGK : IsConnectedReductive G_K)
    (hi : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map i))
    [Mono ((GroupScheme.baseChange b).map i).hom.hom.left]
    (A : KPApartmentData (S := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map i) (IntegerValuation.order vK))
    (Z : CentralizerDatum (S := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map i))
    (h6 : IntegerValuation.IsOmegaCompatible vK A Z)
    (hA : KPApartmentData.GaloisStable F 𝕂 i A)
    (H : ReferenceApartmentDescent B (buildingData i hGK hi A Z h6)
      (semilinearData i hGK hi Z h6 hA))
    {U : CommGroupScheme (Spec (CommRingCat.of F))} (j : U.toGrp ⟶ G)
    (f' : B.S ⟶ U) (hf' : CommGroupScheme.groupHom f' ≫ j = B.i)
    (hj : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange b).obj U)
      ((GroupScheme.baseChange b).map j)) :
    let C := buildingData i hGK hi A Z h6
    let Γ := semilinearData i hGK hi Z h6 hA
    ∃ (g : rationalPoints G_K) (t : C.S ≅ (CommGroupScheme.baseChange b).obj U)
      (a : B.Apartment →ᵃ[ℝ] C.Apartment),
      C.i ≫ ((G_K).innerIso g).hom =
        CommGroupScheme.groupHom t.hom ≫ (GroupScheme.baseChange b).map j ∧
      Function.Injective a ∧
      (∀ x, H.embedding (B.apartmentMap x) = C.translatedApartmentMap g (a x)) ∧
      Set.range a = {y | ∀ σ : 𝕂 ≃ₐ[F] 𝕂,
        Γ.action σ (C.translatedApartmentMap g y) = C.translatedApartmentMap g y} ∧
      a.linear.comp (rootAnnihilator B.i).mkQ =
        (rootAnnihilator C.i).mkQ.comp
          ((cocharacterMapReal ((CommGroupScheme.baseChange b).map f' ≫ t.inv)).comp
            (splitCocharacterBaseChange (K := 𝕂) B.S
              B.isMaximalSplitTorus.isSplitSubtorus.1).toLinearMap) ∧
      AffineRootSystem.restrictedRoots a C.affineRoots = B.affineRoots := by
  let C := buildingData i hGK hi A Z h6
  let Γ := semilinearData i hGK hi Z h6 hA
  have : Mono ((GroupScheme.baseChange b).map j).hom.hom.left := mono_of_isMaximalSplitTorus hj
  obtain ⟨g, t₀, ht₀⟩ := (maximalSplitTorusConjugacy 𝕂 G_K hGK).1
    ((CommGroupScheme.baseChange b).obj T) ((CommGroupScheme.baseChange b).obj U)
    ((GroupScheme.baseChange b).map i) ((GroupScheme.baseChange b).map j) hi hj
  let t := CommGroupScheme.isoOfGroupIso t₀
  let p := (G_K).innerIso g
  have ht : (GroupScheme.baseChange b).map i ≫ p.hom =
      CommGroupScheme.groupHom t.hom ≫ (GroupScheme.baseChange b).map j := ht₀
  let A' := A.transport t p ht
  let Z' := Z.basedTransport t p ht
  have h6' : IntegerValuation.IsOmegaCompatible vK A' Z' :=
    h6.transport_basedIso vK Z Z' t p ht
  have hA' : KPApartmentData.GaloisStable F 𝕂 j A' :=
    KPApartmentData.galoisStable_transport_inner F 𝕂 i j t g ht A hA
  let C' := buildingData j hGK hj A' Z' h6'
  let Γ' := semilinearData j hGK hj Z' h6' hA'
  obtain ⟨H'⟩ := referenceApartmentDescent B hB j f' hf' hGK hj A' Z' h6' hA'
  let R : C'.ReducedBuilding ≃ C.ReducedBuilding := A.conjugateReducedBuildingEquiv t g ht
  let r : C.Apartment ≃ᵃ[ℝ] C'.Apartment := A.apartmentTransportAffineEquiv t p ht
  let e : B.ReducedBuilding → C.ReducedBuilding := fun x => R (H'.embedding x)
  let a : B.Apartment →ᵃ[ℝ] C.Apartment := r.symm.toAffineMap.comp H'.apartment
  have he (k : rationalPoints G) (x : B.ReducedBuilding) :
      e (k • x) = rationalExtend F 𝕂 G k • e x := by
    change R (H'.embedding (k • x)) = _
    rw [H'.equivariant]
    exact A.conjugateReducedBuildingEquiv_smul t g ht _ _
  have hr (x : C.Apartment) : R (C'.apartmentMap (r x)) = C.translatedApartmentMap g x :=
    A.conjugateApartmentMap_transport t g ht x
  have ha (x : B.Apartment) : e (B.apartmentMap x) = C.translatedApartmentMap g (a x) := by
    change R (H'.embedding (B.apartmentMap x)) = C.translatedApartmentMap g (a x)
    rw [H'.apartment_compatible]
    have h := hr (a x)
    change R (C'.apartmentMap (r (r.symm (H'.apartment x)))) = _ at h
    rwa [AffineEquiv.apply_symm_apply] at h
  have hR (σ : 𝕂 ≃ₐ[F] 𝕂) (x : C'.ReducedBuilding) :
      Γ.action σ (R x) = R (Γ'.action σ x) := by
    exact (semilinearData_action_apply i hGK hi Z h6 hA σ (R x)).trans
      ((KPApartmentData.conjugateReducedBuildingEquiv_galois F 𝕂 i j t g ht A hA hA' σ x).trans
        (congrArg R (semilinearData_action_apply j hGK hj Z' h6' hA' σ x).symm))
  have hfixed (σ : 𝕂 ≃ₐ[F] 𝕂) (x : B.ReducedBuilding) : Γ.action σ (e x) = e x :=
    (hR σ (H'.embedding x)).trans (congrArg R (H'.fixed σ x))
  have himage (x : B.Apartment) : ∃ w, H.embedding (B.apartmentMap w) = e (B.apartmentMap x) := by
    have hσ (σ : 𝕂 ≃ₐ[F] 𝕂) :
        KPApartmentData.galoisQuotientAction F 𝕂 i A hA σ (e (B.apartmentMap x)) =
          e (B.apartmentMap x) :=
      (semilinearData_action_apply i hGK hi Z h6 hA σ _).symm.trans (hfixed σ _)
    have hu : IsFixedByUnramifiedTorusUnits F B.i (e (B.apartmentMap x)) :=
      (A.isFixedByScalarTorusUnits_conjugateReducedBuildingEquiv_iff t g ht vK B.i
        (H'.embedding (B.apartmentMap x))).mpr (H'.torus_units x)
    obtain ⟨y, _, hy⟩ := unramifiedTorusUnitFixedApartment F G B.isConnectedReductive
      B.S B.i B.isMaximalSplitTorus T i f hf hi A Z h6 hA _ hσ hu
    have hy' : y ∈ Set.range H.apartment := by
      rw [H.apartment_range]
      exact fun σ => (congrArg (Γ.action σ) hy).trans ((hfixed σ _).trans hy.symm)
    obtain ⟨w, hw⟩ := hy'
    exact ⟨w, (H.apartment_compatible w).trans ((congrArg C.apartmentMap hw).trans hy)⟩
  have heq := H.eq_on_apartment_of_affine_chart ((CommGroupScheme.baseChange b).map f) (baseChange_factor hf)
    e g a he ha himage
  refine ⟨g, t, a, ht, r.symm.injective.comp H'.apartment_injective,
    fun x => (heq x).trans (ha x), ?_, ?_, ?_⟩
  · ext x
    have hrange : x ∈ Set.range a ↔ r x ∈ Set.range H'.apartment := by
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨w, (AffineEquiv.apply_symm_apply r (H'.apartment w)).symm⟩
      · rintro ⟨w, hw⟩
        exact ⟨w, (congrArg r.symm hw).trans (AffineEquiv.symm_apply_apply r x)⟩
    rw [hrange, H'.apartment_range]
    change (∀ σ : 𝕂 ≃ₐ[F] 𝕂, Γ'.action σ (C'.apartmentMap (r x)) =
      C'.apartmentMap (r x)) ↔
      ∀ σ : 𝕂 ≃ₐ[F] 𝕂, Γ.action σ (C.translatedApartmentMap g x) = C.translatedApartmentMap g x
    rw [← hr x]
    exact forall_congr' fun σ => by rw [hR]; exact R.injective.eq_iff.symm
  · have hl := apartment_linear_comp_mkQ ((CommGroupScheme.baseChange b).map f') (baseChange_factor hf')
      H'.embedding H'.apartment H'.equivariant H'.apartment_compatible
    apply LinearMap.ext
    intro w
    let wK := splitCocharacterBaseChange (K := 𝕂) B.S B.isMaximalSplitTorus.isSplitSubtorus.1 w
    apply r.linear.injective
    change r.linear (r.linear.symm (H'.apartment.linear ((rootAnnihilator B.i).mkQ w))) =
      r.linear ((rootAnnihilator C.i).mkQ (cocharacterMapReal ((CommGroupScheme.baseChange b).map f' ≫ t.inv) wK))
    rw [LinearEquiv.apply_symm_apply]
    change (H'.apartment.linear.comp (rootAnnihilator B.i).mkQ) w =
      translationSpaceTransportEquiv t p ht
        (Submodule.Quotient.mk (cocharacterMapReal ((CommGroupScheme.baseChange b).map f' ≫ t.inv) wK))
    rw [hl, translationSpaceTransportEquiv_mk]
    change (rootAnnihilator C'.i).mkQ (cocharacterMapReal ((CommGroupScheme.baseChange b).map f') wK) =
      (rootAnnihilator C'.i).mkQ (cocharacterRealCongr t
        (cocharacterMapReal ((CommGroupScheme.baseChange b).map f' ≫ t.inv) wK))
    congr 1
    generalize wK = z
    induction z using TensorProduct.inductionOn with
    | tmul s c => simp [cocharacterMapReal_tmul, Category.assoc]
    | add x y hx hy => simp only [map_add, hx, hy]
  · rw [← H'.roots]
    ext ψ
    have hp (φ : C.Apartment →ᵃ[ℝ] ℝ) :
        (A.affineFunctionalTransportEquiv t p ht φ).comp H'.apartment = φ.comp a := rfl
    constructor
    · rintro ⟨φ, hφ, heq', hne⟩
      exact ⟨A.affineFunctionalTransportEquiv t p ht φ,
        (A.mem_affineRoots_transport_iff t p ht φ).mpr hφ, (hp φ).trans heq', hne⟩
    · rintro ⟨φ', hφ', heq', hne⟩
      obtain ⟨φ, rfl⟩ := (A.affineFunctionalTransportEquiv t p ht).surjective φ'
      exact ⟨φ, (A.mem_affineRoots_transport_iff t p ht φ).mp hφ', (hp φ).symm.trans heq', hne⟩

set_option maxHeartbeats 5000000 in
/-- Transport the reference comparison to every rationally translated lower apartment. -/
theorem hasUnramifiedApartmentComparison (D : KPBuildingDatum G)
    (hB : D.base.SatisfiesBuildingAxiom D.realization)
    {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (i₀ : T₀.toGrp ⟶ G)
    (f₀ : D.base.S ⟶ T₀) (hf₀ : CommGroupScheme.groupHom f₀ ≫ i₀ = D.base.i)
    (hT₀ : IsTorus T₀.toGrp) (hc₀ : IsClosedSubgroup i₀)
    (hGK : IsConnectedReductive G_K)
    (hi₀ : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange b).obj T₀)
      ((GroupScheme.baseChange b).map i₀))
    [Mono ((GroupScheme.baseChange b).map i₀).hom.hom.left]
    (A : KPApartmentData (S := (CommGroupScheme.baseChange b).obj T₀)
      ((GroupScheme.baseChange b).map i₀) (IntegerValuation.order vK))
    (Z : CentralizerDatum (S := (CommGroupScheme.baseChange b).obj T₀)
      ((GroupScheme.baseChange b).map i₀))
    (h6 : IntegerValuation.IsOmegaCompatible vK A Z)
    (hA : KPApartmentData.GaloisStable F 𝕂 i₀ A)
    (H : ReferenceApartmentDescent D.base.toValuationBuildingData
      (buildingData i₀ hGK hi₀ A Z h6) (semilinearData i₀ hGK hi₀ Z h6 hA)) :
    D.HasUnramifiedApartmentComparison (buildingData i₀ hGK hi₀ A Z h6)
      (semilinearData i₀ hGK hi₀ Z h6 hA) H.embedding := by
  let C := buildingData i₀ hGK hi₀ A Z h6
  let Γ := semilinearData i₀ hGK hi₀ Z h6 hA
  intro g
  refine ⟨⟨T₀, i₀ ≫ (G.innerIso g).hom, f₀, hT₀, hc₀.comp_iso _, ?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, hf₀]
  · rw [Functor.map_comp]
    exact hi₀.comp_iso ((GroupScheme.baseChange b).mapIso (G.innerIso g))
  · intro T i f hT
    let j := i ≫ (G.innerIso g⁻¹).hom
    have hf : CommGroupScheme.groupHom f ≫ j = D.base.i := by
      dsimp only [j]
      rw [← Category.assoc, hT.2.2.1, Category.assoc, innerIso_inv_hom,
        Iso.hom_inv_id, Category.comp_id]
    have hj : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange b).obj T) ((GroupScheme.baseChange b).map j) := by
      dsimp only [j]
      rw [Functor.map_comp]
      exact hT.2.2.2.comp_iso ((GroupScheme.baseChange b).mapIso (G.innerIso g⁻¹))
    obtain ⟨k, t, a, ht, hinj, hap, hrange, hlinear, hroots⟩ :=
      compareSpecialTorus D.base.toValuationBuildingData ⟨D.realization, hB⟩
        i₀ f₀ hf₀ hGK hi₀ A Z h6 hA H j f hf hj
    let gK := rationalExtend F 𝕂 G g
    have hcomp : (GroupScheme.baseChange b).map j ≫ ((G_K).innerIso gK).hom = (GroupScheme.baseChange b).map i := by
      have h := congrArg (fun x : T.toGrp ⟶ G => (GroupScheme.baseChange b).map x)
        (show j ≫ (G.innerIso g).hom = i by
          dsimp only [j]
          rw [Category.assoc, innerIso_inv_hom, Iso.inv_hom_id, Category.comp_id])
      rw [Functor.map_comp, baseChange_innerIso_hom, ← rationalExtend_eq_baseChangeBasePoint] at h
      exact h
    have hm (y : C.Apartment) : C.translatedApartmentMap (gK * k) y =
        gK • C.translatedApartmentMap k y := mul_smul _ _ _
    refine ⟨gK * k, t, a, ?_, hinj, ?_, ?_, hlinear, hroots⟩
    · rw [innerIso_mul_hom, ← Category.assoc, ht, Category.assoc, hcomp]
    · intro x
      change H.embedding (g • D.base.apartmentMap x) = C.translatedApartmentMap (gK * k) (a x)
      rw [hm, H.equivariant, hap]
    · rw [hrange]
      ext y
      change (∀ σ : 𝕂 ≃ₐ[F] 𝕂, Γ.action σ (C.translatedApartmentMap k y) =
        C.translatedApartmentMap k y) ↔
        (∀ σ : 𝕂 ≃ₐ[F] 𝕂, Γ.action σ (C.translatedApartmentMap (gK * k) y) =
          C.translatedApartmentMap (gK * k) y)
      have hgK (σ : 𝕂 ≃ₐ[F] 𝕂) : rationalConjugate F 𝕂 G σ gK = gK :=
        rationalConjugate_rationalExtend F 𝕂 G σ g
      simp only [hm, Γ.action_smul, hgK]
      exact forall_congr' fun _ => (MulAction.injective gK).eq_iff.symm

end Langlands.Geometry.Building.UnramifiedBuildingDescent

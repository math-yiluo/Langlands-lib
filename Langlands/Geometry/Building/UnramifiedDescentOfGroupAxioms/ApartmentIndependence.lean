import Langlands.Geometry.Building.UnramifiedDescentOfGroupAxioms.ReferenceApartment
import Langlands.Geometry.Building.ApartmentQuotientSegment
import Langlands.Geometry.Building.DescendedApartmentLinearPart
import Langlands.Geometry.Building.OmegaCompatibleApartmentRigidity

/-! # Uniqueness of the coordinates of a descended apartment -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.UnramifiedBuildingDescent

/-- Closed-segment interpolation at every real parameter gives a real affine map. -/
private def affineMapOfSegments {V P W Q : Type*}
    [AddCommGroup V] [AddCommGroup W] [Module ℝ V] [Module ℝ W]
    [AddTorsor V P] [AddTorsor W Q] (f : P → Q)
    (hf : ∀ (x y : P) (r : ℝ), 0 ≤ r → r ≤ 1 →
      f (AffineMap.lineMap x y r) = AffineMap.lineMap (f x) (f y) r) : P →ᵃ[ℝ] Q := by
  let p : P := Classical.choice inferInstance
  let F' : V → W := fun v => f (v +ᵥ p) -ᵥ f p
  have hzero : F' 0 = 0 := by simp [F']
  have hline (x y : V) (r : ℝ) (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
      F' (AffineMap.lineMap x y r) = AffineMap.lineMap (F' x) (F' y) r := by
    have hv := AffineMap.lineMap_vadd_lineMap x y p p r
    rw [AffineMap.lineMap_same_apply] at hv
    dsimp only [F']
    rw [hv, hf _ _ r h₀ h₁]
    conv_lhs => rw [← AffineMap.lineMap_same_apply (f p) r]
    exact AffineMap.lineMap_vsub_lineMap (f (x +ᵥ p)) (f (y +ᵥ p)) (f p) (f p) r
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  let L₀ := AddMonoidHom.ofMapMidpoint ℝ ℝ F' hzero (fun x y => by
    unfold midpoint
    exact hline x y (⅟2) (by norm_num [invOf_eq_inv]) (by norm_num [invOf_eq_inv]))
  have hsmall (r : ℝ) (v : V) (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
      L₀ (r • v) = r • L₀ v := by
    change F' (r • v) = r • F' v
    have h := hline 0 v r h₀ h₁
    simpa only [AffineMap.lineMap_apply_module', sub_zero, add_zero, hzero] using h
  have hnonneg (r : ℝ) (v : V) (h₀ : 0 ≤ r) : L₀ (r • v) = r • L₀ v := by
    by_cases h₁ : r ≤ 1
    · exact hsmall r v h₀ h₁
    · have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_of_not_ge h₁)
      have h := hsmall r⁻¹ (r • v) (inv_nonneg.mpr h₀)
        (inv_le_one_of_one_le₀ (le_of_not_ge h₁))
      rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at h
      rw [h, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  let L : V →ₗ[ℝ] W :=
    { toFun := L₀
      map_add' := map_add L₀
      map_smul' := fun r v => by
        change L₀ (r • v) = r • L₀ v
        by_cases hr : 0 ≤ r
        · exact hnonneg r v hr
        · have h := congrArg Neg.neg (hnonneg (-r) v (by linarith))
          simpa only [neg_smul, map_neg, neg_neg] using h }
  exact AffineMap.mk' f L p (fun q => by
    change f q = (f ((q -ᵥ p) +ᵥ p) -ᵥ f p) +ᵥ f p
    rw [vsub_vadd, vsub_vadd])

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local notation "𝕂" => inertiaFixedField F
local notation "G_K" => baseChanged F 𝕂 G
local notation "b" => algebraBaseMap F 𝕂

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- Scalar-extension equivariance determines the derivative of an affine map
into a reference chart with a factorization of the maximal split torus. -/
theorem apartment_linear_comp_mkQ
    {B : ValuationBuildingData G} {C : MaximalUnramified.BuildingData F G_K}
    (f : (CommGroupScheme.baseChange b).obj B.S ⟶ C.S)
    (hf : CommGroupScheme.groupHom f ≫ C.i = (GroupScheme.baseChange b).map B.i)
    (e : B.ReducedBuilding → C.ReducedBuilding) (a : B.Apartment →ᵃ[ℝ] C.Apartment)
    (he : ∀ (g : rationalPoints G) (x : B.ReducedBuilding),
      e (g • x) = rationalExtend F 𝕂 G g • e x)
    (ha : ∀ w, e (B.apartmentMap w) = C.apartmentMap (a w)) :
    a.linear.comp (rootAnnihilator (S := B.S) B.i).mkQ =
      (rootAnnihilator (S := C.S) C.i).mkQ.comp ((cocharacterMapReal f).comp
        (splitCocharacterBaseChange (K := 𝕂) B.S B.isMaximalSplitTorus.isSplitSubtorus.1).toLinearMap) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty B.Apartment)
  apply LinearMap.ext
  intro v
  have h := descendedApartment_map_vadd (B := B) (C := C) e a he ha hf v w
  rw [AffineMap.map_vadd] at h
  exact vadd_right_cancel (a w) h

set_option maxHeartbeats 5000000 in
/-- An equivariant apartment lift given in another chart of the same upper building
agrees with the reference lift whenever its image lies in the reference fixed apartment.
Interpolation makes the comparison affine, and valuation rigidity determines its origin. -/
theorem ReferenceApartmentDescent.eq_on_apartment_of_affine_chart
    {B : ValuationBuildingData G} {C : MaximalUnramified.BuildingData F G_K}
    {Γ : MaximalUnramified.SemilinearApartmentData (G := G) C}
    (H : ReferenceApartmentDescent B C Γ)
    (f : (CommGroupScheme.baseChange b).obj B.S ⟶ C.S)
    (hf : CommGroupScheme.groupHom f ≫ C.i = (GroupScheme.baseChange b).map B.i)
    (e : B.ReducedBuilding → C.ReducedBuilding) (g : rationalPoints G_K)
    (a : B.Apartment →ᵃ[ℝ] C.Apartment)
    (he : ∀ (k : rationalPoints G) (x : B.ReducedBuilding),
      e (k • x) = rationalExtend F 𝕂 G k • e x)
    (ha : ∀ w, e (B.apartmentMap w) = g • C.apartmentMap (a w))
    (himage : ∀ w, ∃ x, H.embedding (B.apartmentMap x) = e (B.apartmentMap w)) :
    ∀ w, H.embedding (B.apartmentMap w) = e (B.apartmentMap w) := by
  classical
  choose h hh using himage
  have hc (x : B.Apartment) :
      g • C.apartmentMap (a x) = C.apartmentMap (H.apartment (h x)) := by
    rw [← ha x, ← H.apartment_compatible, hh x]
  have hseg (x y : B.Apartment) (r : ℝ) (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
      h (AffineMap.lineMap x y r) = AffineMap.lineMap (h x) (h y) r := by
    apply H.apartment_injective
    apply maximalUnramifiedApartmentInjective F G_K C
    rw [← hc, a.apply_lineMap, H.apartment.apply_lineMap]
    exact C.apartment.smul_apartmentMap_lineMap_of_two_eq C.isConnectedReductive
      C.isMaximalSplitTorus g _ _ _ _ (hc x) (hc y) h₀ h₁
  let A := affineMapOfSegments h hseg
  have hA (w : B.Apartment) : A w = h w := rfl
  let a' := H.apartment.comp A
  have ha' (w : B.Apartment) : e (B.apartmentMap w) = C.apartmentMap (a' w) := by
    change _ = C.apartmentMap (H.apartment (A w))
    rw [hA, ← H.apartment_compatible, hh]
  have hlinear : A.linear = LinearMap.id := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (rootAnnihilator (S := B.S) B.i) v
    apply H.apartment.linear_injective_iff.mpr H.apartment_injective
    change (a'.linear.comp (rootAnnihilator (S := B.S) B.i).mkQ) w =
      (H.apartment.linear.comp (rootAnnihilator (S := B.S) B.i).mkQ) w
    rw [apartment_linear_comp_mkQ f hf e a' he ha',
      apartment_linear_comp_mkQ f hf H.embedding H.apartment H.equivariant H.apartment_compatible]
  have hbij : Function.Bijective A := A.linear_bijective_iff.mp (by rw [hlinear]; exact Function.bijective_id)
  let Φ := AffineEquiv.ofBijective hbij
  have hΦ (w : B.Apartment) : Φ w = h w := rfl
  have hΦlin : Φ.linear = LinearEquiv.refl ℝ (TranslationSpace B.i) := by
    apply LinearEquiv.ext
    intro v
    exact LinearMap.congr_fun hlinear v
  have hΦeq (n : normalizerPoints B.i) (w : B.Apartment) : Φ (n • w) = n • Φ w := by
    apply B.apartment.apartmentMap_injective B.isConnectedReductive B.isMaximalSplitTorus
    apply H.injective
    change H.embedding (B.apartmentMap (Φ (n • w))) =
      H.embedding (B.apartmentMap (n • Φ w))
    rw [hΦ, hh, ← B.normalizer_smul_apartmentMap, he, ← hh w, ← H.equivariant,
      B.normalizer_smul_apartmentMap, hΦ]
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have hpairs : RelativeRoot.HasOppositeFactorPairs B.i :=
    (RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs _
      B.isMaximalSplitTorus.isSplitSubtorus.1).mp
      (rootRankOneFactorization F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus)
  intro w
  have hv := B.apartment.val_eq_of_equivariant_affineEquiv_of_hasOppositeFactorPairs
    B.apartment B.centralizer B.isOmegaCompatible B.isOmegaCompatible B.isConnectedReductive
    B.isMaximalSplitTorus hpairs Φ hΦlin hΦeq w
  have hw : h w = w := KPApartmentData.Apartment.ext (by simpa only [hΦ] using hv)
  simpa only [hw] using hh w

end Langlands.Geometry.Building.UnramifiedBuildingDescent

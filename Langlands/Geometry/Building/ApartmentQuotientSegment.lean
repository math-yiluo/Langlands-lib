import Langlands.Geometry.Building.ApartmentQuotientRootDistance
import Langlands.Geometry.Building.GaloisApartmentQuotientAction
import Langlands.Geometry.Building.IntegerValuationCommonApartmentsProof
import Langlands.Geometry.Building.UnramifiedApartmentModelInput

/-! # Chart-independent segments in the original apartment quotient -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

namespace KPApartmentData

section General

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
  [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : kˣ → ℝ}
  (D : KPApartmentData i ω)

/-- A rational element mapping two apartment points into the apartment also
maps their entire closed segment by affine interpolation of the endpoints. -/
theorem smul_apartmentMap_lineMap_of_two_eq
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (g : rationalPoints G) (a b x y : D.Apartment)
    (ha : g • D.apartmentMap a = D.apartmentMap x)
    (hb : g • D.apartmentMap b = D.apartmentMap y)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    g • D.apartmentMap (AffineMap.lineMap a b t) =
      D.apartmentMap (AffineMap.lineMap x y t) := by
  obtain ⟨n, hna, hnb⟩ :=
    D.exists_normalizer_eq_of_two_apartmentMap_eq hG hi g a b x y ha hb
  have hfa : ((n : rationalPoints G)⁻¹ * g) • D.apartmentMap a = D.apartmentMap a := by
    rw [mul_smul, ha, ← hna, D.apartmentMap_smul, inv_smul_smul]
  have hfb : ((n : rationalPoints G)⁻¹ * g) • D.apartmentMap b = D.apartmentMap b := by
    rw [mul_smul, hb, ← hnb, D.apartmentMap_smul, inv_smul_smul]
  have hfix := D.smul_apartmentMap_lineMap_eq hG hi hfa hfb ht0 ht1
  calc
    g • D.apartmentMap (AffineMap.lineMap a b t) =
        (n : rationalPoints G) •
          (((n : rationalPoints G)⁻¹ * g) •
            D.apartmentMap (AffineMap.lineMap a b t)) := by
      simp only [mul_smul, smul_inv_smul]
    _ = (n : rationalPoints G) • D.apartmentMap (AffineMap.lineMap a b t) := by
      rw [hfix]
    _ = D.apartmentMap (AffineMap.lineMap x y t) := by
      rw [← D.apartmentMap_smul]
      have hn := (D.normalizerAffineEquiv n).apply_lineMap a b t
      simp only [normalizerAffineEquiv_apply] at hn
      rw [hn, hna, hnb]

/-- Interpolate in chosen common-apartment coordinates. The translated chart
formula below proves independence of these choices. -/
def chosenSegmentPoint (hcommon : D.HasCommonApartments)
    (x y : D.ReducedBuilding) (t : Set.Icc (0 : ℝ) 1) : D.ReducedBuilding :=
  let c := D.commonApartmentCoordinates hcommon x y
  c.translate • D.apartmentMap (AffineMap.lineMap c.first c.second (t : ℝ))

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hcommon : D.HasCommonApartments)

include hG hi

/-- Every translated apartment gives the same segment point in the original quotient. -/
theorem chosenSegmentPoint_smul_apartmentMap (g : rationalPoints G)
    (a b : D.Apartment) (t : Set.Icc (0 : ℝ) 1) :
    D.chosenSegmentPoint hcommon (g • D.apartmentMap a) (g • D.apartmentMap b) t =
      g • D.apartmentMap (AffineMap.lineMap a b (t : ℝ)) := by
  let c := D.commonApartmentCoordinates hcommon
    (g • D.apartmentMap a) (g • D.apartmentMap b)
  have ha : (g⁻¹ * c.translate) • D.apartmentMap c.first = D.apartmentMap a := by
    rw [mul_smul, c.first_eq, inv_smul_smul]
  have hb : (g⁻¹ * c.translate) • D.apartmentMap c.second = D.apartmentMap b := by
    rw [mul_smul, c.second_eq, inv_smul_smul]
  have hseg := D.smul_apartmentMap_lineMap_of_two_eq hG hi (g⁻¹ * c.translate)
    c.first c.second a b ha hb t.property.1 t.property.2
  change c.translate • D.apartmentMap (AffineMap.lineMap c.first c.second (t : ℝ)) = _
  calc
    _ = g • ((g⁻¹ * c.translate) •
        D.apartmentMap (AffineMap.lineMap c.first c.second (t : ℝ))) := by
      simp only [mul_smul, smul_inv_smul]
    _ = _ := by rw [hseg]

theorem chosenSegmentPoint_apartmentMap (a b : D.Apartment)
    (t : Set.Icc (0 : ℝ) 1) :
    D.chosenSegmentPoint hcommon (D.apartmentMap a) (D.apartmentMap b) t =
      D.apartmentMap (AffineMap.lineMap a b (t : ℝ)) := by
  simpa only [one_smul] using
    D.chosenSegmentPoint_smul_apartmentMap hG hi hcommon 1 a b t

omit hG hi in
@[simp] theorem chosenSegmentPoint_zero (x y : D.ReducedBuilding) :
    D.chosenSegmentPoint hcommon x y ⟨0, le_rfl, zero_le_one⟩ = x := by
  let c := D.commonApartmentCoordinates hcommon x y
  change c.translate • D.apartmentMap (AffineMap.lineMap c.first c.second 0) = x
  rw [AffineMap.lineMap_apply_zero]
  exact c.first_eq

omit hG hi in
@[simp] theorem chosenSegmentPoint_one (x y : D.ReducedBuilding) :
    D.chosenSegmentPoint hcommon x y ⟨1, zero_le_one, le_rfl⟩ = y := by
  let c := D.commonApartmentCoordinates hcommon x y
  change c.translate • D.apartmentMap (AffineMap.lineMap c.first c.second 1) = y
  rw [AffineMap.lineMap_apply_one]
  exact c.second_eq

/-- The original rational-point action preserves the parameter of interpolation. -/
theorem chosenSegmentPoint_smul (g : rationalPoints G) (x y : D.ReducedBuilding)
    (t : Set.Icc (0 : ℝ) 1) :
    D.chosenSegmentPoint hcommon (g • x) (g • y) t =
      g • D.chosenSegmentPoint hcommon x y t := by
  obtain ⟨h, a, b, rfl, rfl⟩ := hcommon x y
  change D.chosenSegmentPoint hcommon (g • h • D.apartmentMap a)
    (g • h • D.apartmentMap b) t =
      g • D.chosenSegmentPoint hcommon (h • D.apartmentMap a)
        (h • D.apartmentMap b) t
  rw [← mul_smul, ← mul_smul,
    D.chosenSegmentPoint_smul_apartmentMap hG hi hcommon,
    D.chosenSegmentPoint_smul_apartmentMap hG hi hcommon, mul_smul]

theorem smul_chosenSegmentPoint_eq_of_endpoints_fixed
    {g : rationalPoints G} {x y : D.ReducedBuilding}
    (hx : g • x = x) (hy : g • y = y) (t : Set.Icc (0 : ℝ) 1) :
    g • D.chosenSegmentPoint hcommon x y t = D.chosenSegmentPoint hcommon x y t := by
  rw [← D.chosenSegmentPoint_smul hG hi hcommon, hx, hy]

/-- The closed segment as a subset of the existing quotient. -/
def chosenSegment (x y : D.ReducedBuilding) : Set D.ReducedBuilding :=
  Set.range (D.chosenSegmentPoint hcommon x y)

omit hG hi in
theorem left_mem_chosenSegment (x y : D.ReducedBuilding) :
    x ∈ D.chosenSegment hcommon x y :=
  ⟨⟨0, le_rfl, zero_le_one⟩, D.chosenSegmentPoint_zero hcommon x y⟩

omit hG hi in
theorem right_mem_chosenSegment (x y : D.ReducedBuilding) :
    y ∈ D.chosenSegment hcommon x y :=
  ⟨⟨1, zero_le_one, le_rfl⟩, D.chosenSegmentPoint_one hcommon x y⟩

/-- Fixing a segment pointwise is equivalent to fixing its two endpoints. -/
theorem mem_pointwiseFixer_chosenSegment_iff (g : rationalPoints G)
    (x y : D.ReducedBuilding) :
    g ∈ D.pointwiseFixer (D.chosenSegment hcommon x y) ↔ g • x = x ∧ g • y = y := by
  rw [D.mem_pointwiseFixer]
  constructor
  · intro h
    exact ⟨h x (D.left_mem_chosenSegment hcommon x y),
      h y (D.right_mem_chosenSegment hcommon x y)⟩
  · rintro ⟨hx, hy⟩ z ⟨t, rfl⟩
    exact D.smul_chosenSegmentPoint_eq_of_endpoints_fixed hG hi hcommon hx hy t

/-- The translated chart formula determines the segment map uniquely. -/
theorem eq_chosenSegmentPoint_of_smul_apartmentMap
    (s : D.ReducedBuilding → D.ReducedBuilding → Set.Icc (0 : ℝ) 1 → D.ReducedBuilding)
    (hs : ∀ (g : rationalPoints G) (a b : D.Apartment) (t : Set.Icc (0 : ℝ) 1),
      s (g • D.apartmentMap a) (g • D.apartmentMap b) t =
        g • D.apartmentMap (AffineMap.lineMap a b (t : ℝ))) :
    s = D.chosenSegmentPoint hcommon := by
  funext x y t
  obtain ⟨g, a, b, rfl, rfl⟩ := hcommon x y
  exact (hs g a b t).trans (D.chosenSegmentPoint_smul_apartmentMap hG hi hcommon g a b t).symm

end General

section Coefficients

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance segmentExtendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left]
  {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i) ω)
  (hD : GaloisStable k K i D)

/-- Actual coefficient transport preserves affine interpolation in this apartment. -/
theorem galoisAction_lineMap (σ : K ≃ₐ[k] K) (a c : D.Apartment) (t : ℝ) :
    galoisAction k K i D hD σ (AffineMap.lineMap a c t) =
      AffineMap.lineMap (galoisAction k K i D hD σ a)
        (galoisAction k K i D hD σ c) t :=
  (galoisAffineAction k K i D hD σ).apply_lineMap a c t

variable (hG : IsConnectedReductive (baseChanged k K G))
  (hi : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i))
  (hcommon : D.HasCommonApartments)

include hG hi

/-- The actual coefficient action on the original quotient preserves segment parameters. -/
theorem galoisQuotientAction_chosenSegmentPoint (σ : K ≃ₐ[k] K)
    (x y : D.ReducedBuilding) (t : Set.Icc (0 : ℝ) 1) :
    galoisQuotientAction k K i D hD σ (D.chosenSegmentPoint hcommon x y t) =
      D.chosenSegmentPoint hcommon
        (galoisQuotientAction k K i D hD σ x)
        (galoisQuotientAction k K i D hD σ y) t := by
  obtain ⟨g, a, c, rfl, rfl⟩ := hcommon x y
  change galoisQuotientAction k K i D hD σ
      (D.chosenSegmentPoint hcommon (g • D.apartmentMap a) (g • D.apartmentMap c) t) =
    D.chosenSegmentPoint hcommon
      (galoisQuotientAction k K i D hD σ (g • D.apartmentMap a))
      (galoisQuotientAction k K i D hD σ (g • D.apartmentMap c)) t
  have hchart := D.chosenSegmentPoint_smul_apartmentMap hG hi hcommon g a c t
  rw [hchart, galoisQuotientAction_smul, galoisQuotientAction_apartmentMap,
    galoisAction_lineMap]
  simp only [galoisQuotientAction_smul, galoisQuotientAction_apartmentMap]
  exact (D.chosenSegmentPoint_smul_apartmentMap hG hi hcommon
    (rationalConjugate k K G σ g)
    (galoisAction k K i D hD σ a) (galoisAction k K i D hD σ c) t).symm

/-- Coefficient-fixed endpoints give a segment fixed pointwise by every actual
coefficient automorphism, in the same quotient as the endpoints. -/
theorem galoisQuotientAction_chosenSegmentPoint_eq_of_endpoints_fixed
    {x y : D.ReducedBuilding}
    (hx : ∀ σ : K ≃ₐ[k] K, galoisQuotientAction k K i D hD σ x = x)
    (hy : ∀ σ : K ≃ₐ[k] K, galoisQuotientAction k K i D hD σ y = y)
    (t : Set.Icc (0 : ℝ) 1) (σ : K ≃ₐ[k] K) :
    galoisQuotientAction k K i D hD σ (D.chosenSegmentPoint hcommon x y t) =
      D.chosenSegmentPoint hcommon x y t := by
  rw [galoisQuotientAction_chosenSegmentPoint k K i D hD hG hi hcommon, hx σ, hy σ]

end Coefficients

end KPApartmentData

namespace MaximalUnramified

/-- Original upper apartment and full V6 data supply common apartments in the
same quotient, without a separate common-apartment hypothesis. -/
theorem hasCommonApartments_of_apartment
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {iT : T.toGrp ⟶ G}
    (hG : IsConnectedReductive G)
    (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)) :
    letI := mono_of_isMaximalSplitTorus hiT
    ∀ (D : KPApartmentData
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
      (IntegerValuation.order (valuation F)))
      (C : CentralizerDatum
        (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      IntegerValuation.IsOmegaCompatible (valuation F) D C →
        D.HasCommonApartments := by
  have := mono_of_isMaximalSplitTorus hiT
  intro D C h6
  exact commonApartments F (baseChanged F (inertiaFixedField F) G)
    (buildingDataOfApartment hG hiT D C h6)

end MaximalUnramified

/-- The original unramified host inputs give canonical affine segments in the
actual quotient, equivariant for both rational points and coefficients. -/
def UnramifiedFixedSegmentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      letI := mono_of_isMaximalSplitTorus hiT
      ∀ (D : KPApartmentData
        (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
        (IntegerValuation.order (MaximalUnramified.valuation F)))
        (C : CentralizerDatum
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
        IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C →
        ∀ (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D),
          ∃ s : D.ReducedBuilding → D.ReducedBuilding →
              Set.Icc (0 : ℝ) 1 → D.ReducedBuilding,
            (∀ (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
              (a b : D.Apartment) (t : Set.Icc (0 : ℝ) 1),
              s (g • D.apartmentMap a) (g • D.apartmentMap b) t =
                g • D.apartmentMap (AffineMap.lineMap a b (t : ℝ))) ∧
            (∀ x y, s x y ⟨0, le_rfl, zero_le_one⟩ = x ∧
              s x y ⟨1, zero_le_one, le_rfl⟩ = y) ∧
            (∀ (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) x y t,
              s (g • x) (g • y) t = g • s x y t) ∧
            (∀ (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) x y,
              g ∈ D.pointwiseFixer (Set.range (s x y)) ↔ g • x = x ∧ g • y = y) ∧
            (∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) x y t,
              KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ
                  (s x y t) =
                s (KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ x)
                  (KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y) t) ∧
            (∀ x y,
              (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
                KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ x = x) →
              (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
                KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y = y) →
              ∀ t (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F),
                KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ
                  (s x y t) = s x y t)

set_option maxHeartbeats 1600000 in
/-- Construct the segment on the original host quotient from the original data. -/
theorem unramifiedFixedSegment : UnramifiedFixedSegmentStatement.{u} := by
  intro F _ _ _ _ G hG T iT
  have : IsAffineHom G.X.hom := hG.isAffineHom
  intro hiT
  have := mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD
  have hc : D.HasCommonApartments :=
    MaximalUnramified.hasCommonApartments_of_apartment hG hiT D C h6
  have hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G) :=
    hG.baseChange_of_algebraicExtension
  have hcoeff := KPApartmentData.galoisQuotientAction_chosenSegmentPoint
    F (inertiaFixedField F) iT D hD hGK hiT hc
  refine ⟨D.chosenSegmentPoint hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g a b t
    exact D.chosenSegmentPoint_smul_apartmentMap hGK hiT hc g a b t
  · intro x y
    exact ⟨D.chosenSegmentPoint_zero hc x y, D.chosenSegmentPoint_one hc x y⟩
  · intro g x y t
    exact D.chosenSegmentPoint_smul hGK hiT hc g x y t
  · intro g x y
    change g ∈ D.pointwiseFixer (D.chosenSegment hc x y) ↔ g • x = x ∧ g • y = y
    exact D.mem_pointwiseFixer_chosenSegment_iff hGK hiT hc g x y
  · exact hcoeff
  · intro x y hx hy t σ
    exact (hcoeff σ x y t).trans
      (congrArg₂ (fun x y => D.chosenSegmentPoint hc x y t) (hx σ) (hy σ))

end Langlands.Geometry.Building

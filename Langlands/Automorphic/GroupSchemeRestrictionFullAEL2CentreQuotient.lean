import Langlands.Automorphic.GroupSchemeRestrictionFullAEL2FullGroup

/-! # The almost-everywhere cuspidal condition over `A_G \ G(𝔸_F)` -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.QuotientIntegration
open Langlands.Automorphic.GroupSchemeFunctions

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
variable (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
variable (S : CommGroupScheme (Spec (CommRingCat.of ℚ)))
variable (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G)

section Splitting

variable {S j} {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}

/-- If the split-centre image is the positive image of a central torus, it consists of
central points of `G(𝔸_F)`. -/
theorem subgroup_le_center_of_splitting (hc : IsCentral i)
    (h : subgroup F G S j = imageSubgroup F T G i) :
    subgroup F G S j ≤ Subgroup.center (AdelicGroupPoints F G) := by
  rw [h]
  rintro _ ⟨a, ha, rfl⟩
  exact Subgroup.mem_center_iff.mpr fun x =>
    (positivePointMap_commute F G T i hc ⟨a, ha⟩ x).eq.symm

/-- Points of the positive image of `i` lie in the split-centre image. -/
theorem positivePointMap_mem_subgroup (h : subgroup F G S j = imageSubgroup F T G i)
    (a : intrinsicSubgroup F T) : positivePointMap F G T i a ∈ subgroup F G S j := by
  rw [h]
  exact ⟨a.val, a.property, rfl⟩

end Splitting

/-- A central split-centre image commutes with every adelic point. -/
theorem commute_of_le_center (hZ : subgroup F G S j ≤ Subgroup.center (AdelicGroupPoints F G))
    {z : AdelicGroupPoints F G} (hz : z ∈ subgroup F G S j) (x : AdelicGroupPoints F G) :
    Commute z x :=
  (Subgroup.mem_center_iff.mp (hZ hz) x).symm

/-- A central split-centre image is normal. -/
theorem normal_of_le_center
    (hZ : subgroup F G S j ≤ Subgroup.center (AdelicGroupPoints F G)) :
    (subgroup F G S j).Normal :=
  ⟨fun z hz g => by
    rw [← (commute_of_le_center F G S j hZ hz g).eq, mul_inv_cancel_right]
    exact hz⟩

variable [(subgroup F G S j).Normal]

/-- The quotient group `A_G \ G(𝔸_F)` of the adelic points by the split-centre image. -/
def CentreQuotient : Type := AdelicGroupPoints F G ⧸ subgroup F G S j

namespace CentreQuotient

instance instGroup : Group (CentreQuotient F G S j) :=
  inferInstanceAs (Group (AdelicGroupPoints F G ⧸ subgroup F G S j))

instance instTopologicalSpace : TopologicalSpace (CentreQuotient F G S j) :=
  inferInstanceAs (TopologicalSpace (AdelicGroupPoints F G ⧸ subgroup F G S j))

instance instIsTopologicalGroup : IsTopologicalGroup (CentreQuotient F G S j) :=
  inferInstanceAs (IsTopologicalGroup (AdelicGroupPoints F G ⧸ subgroup F G S j))

instance instLocallyCompactSpace : LocallyCompactSpace (CentreQuotient F G S j) :=
  inferInstanceAs (LocallyCompactSpace (AdelicGroupPoints F G ⧸ subgroup F G S j))

/-- The Borel σ-algebra (Mathlib's quotient σ-algebra need not be Borel). -/
instance instMeasurableSpace : MeasurableSpace (CentreQuotient F G S j) := borel _

instance instBorelSpace : BorelSpace (CentreQuotient F G S j) := ⟨rfl⟩

/-- The quotient map `G(𝔸_F) → A_G \ G(𝔸_F)`. -/
def mk : AdelicGroupPoints F G →* CentreQuotient F G S j :=
  QuotientGroup.mk' (subgroup F G S j)

theorem mk_surjective : Function.Surjective (mk F G S j) := QuotientGroup.mk'_surjective _

theorem continuous_mk : Continuous (mk F G S j) := continuous_quotient_mk'

theorem mk_mul_of_mem {z : AdelicGroupPoints F G} (hz : z ∈ subgroup F G S j)
    (g : AdelicGroupPoints F G) : mk F G S j (z * g) = mk F G S j g := by
  have hz' : mk F G S j z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
  rw [map_mul, hz', one_mul]

/-- A function on `G(𝔸_F)` invariant under left translation by `A_G`, as a function on
`A_G \ G(𝔸_F)`. -/
def lift {α : Sort*} (f : AdelicGroupPoints F G → α)
    (hf : ∀ z ∈ subgroup F G S j, ∀ g, f (z * g) = f g) : CentreQuotient F G S j → α :=
  _root_.Quotient.lift (s := QuotientGroup.leftRel (subgroup F G S j)) f fun a b hab => by
    have hab : a⁻¹ * b ∈ subgroup F G S j := QuotientGroup.leftRel_apply.mp hab
    have hconj : a * (a⁻¹ * b) * a⁻¹ ∈ subgroup F G S j :=
      ‹(subgroup F G S j).Normal›.conj_mem _ hab a
    have hb : b = a * (a⁻¹ * b) * a⁻¹ * a := by group
    rw [hb, hf _ hconj]

@[simp] theorem lift_mk {α : Sort*} (f : AdelicGroupPoints F G → α) (hf) (g) :
    lift F G S j f hf (mk F G S j g) = f g := rfl

/-- Every regular Haar measure on `A_G \ G(𝔸_F)` has the null sets of `Measure.haar`. -/
theorem ae_eq_ae_haar (ν : Measure (CentreQuotient F G S j)) [ν.IsHaarMeasure] [ν.Regular] :
    ae ν = ae (Measure.haar : Measure (CentreQuotient F G S j)) := by
  rw [Measure.isMulLeftInvariant_eq_smul_of_regular ν Measure.haar,
    Measure.ae_smul_measure_eq (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne']

end CentreQuotient

section Haar

variable {S j} {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (I : Type) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
variable (hc : IsCentral i) (h : subgroup F G S j = imageSubgroup F T G i)

/-- With the split-centre image equal to the positive image of a central split torus, the
norm-one subgroup `G(𝔸_F)¹` maps isomorphically onto `A_G \ G(𝔸_F)`. -/
def normOneCentreQuotientEquiv :
    AdelicGroupPoints.normOneSubgroup F G ≃ₜ* CentreQuotient F G S j where
  toFun n := CentreQuotient.mk F G S j n
  invFun := CentreQuotient.lift F G S j (normOneProjection F G T i hi I e hc) fun z hz g => by
    rw [h] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    rw [map_mul]
    change normOneProjection F G T i hi I e hc (positivePointMap F G T i ⟨a, ha⟩) * _ = _
    rw [normOneProjection_positivePointMap, one_mul]
  left_inv n := normOneProjection_normOne F G T i hi I e hc n
  right_inv q := by
    obtain ⟨x, rfl⟩ := CentreQuotient.mk_surjective F G S j q
    change CentreQuotient.mk F G S j (normOneFactor F G T i hi I e x : AdelicGroupPoints F G) =
      CentreQuotient.mk F G S j x
    conv_rhs => rw [← positivePointMap_mul_normOneFactor F G T i hi I e x]
    exact (CentreQuotient.mk_mul_of_mem F G S j (positivePointMap_mem_subgroup F G h _) _).symm
  map_mul' m n := map_mul (CentreQuotient.mk F G S j) (m : AdelicGroupPoints F G) n
  continuous_toFun := (CentreQuotient.continuous_mk F G S j).comp continuous_subtype_val
  continuous_invFun := (QuotientGroup.isQuotientMap_mk (subgroup F G S j)).continuous_iff.mpr
    (normOneProjection F G T i hi I e hc).continuous

@[simp] theorem normOneCentreQuotientEquiv_apply (n : AdelicGroupPoints.normOneSubgroup F G) :
    normOneCentreQuotientEquiv F G hi I e hc h n = CentreQuotient.mk F G S j n := rfl

include hi I e hc h in
/-- Almost everywhere for Haar measure on `A_G \ G(𝔸_F)` is almost everywhere for Haar measure
on `G(𝔸_F)¹` along the inclusion. -/
theorem CentreQuotient.ae_haar_iff_ae_normOne (p : CentreQuotient F G S j → Prop) :
    (∀ᵐ x ∂(Measure.haar : Measure (CentreQuotient F G S j)), p x) ↔
      ∀ᵐ (m : AdelicGroupPoints.normOneSubgroup F G) ∂Measure.haar,
        p (CentreQuotient.mk F G S j m) := by
  let φ := normOneCentreQuotientEquiv F G hi I e hc h
  have hreg : (Measure.map φ
      (Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G))).Regular :=
    Measure.Regular.map φ.toHomeomorph
  have hemb : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  rw [Measure.isMulLeftInvariant_eq_smul_of_regular
      (Measure.haar : Measure (CentreQuotient F G S j)) (Measure.map φ Measure.haar),
    Measure.ae_smul_measure_iff (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne',
    hemb.ae_map_iff]
  rfl

include hi I e hc h in
/-- Almost everywhere for Haar measure on `A_G \ G(𝔸_F)` is almost everywhere for Haar measure
on `G(𝔸_F)` along the quotient map. -/
theorem CentreQuotient.ae_haar_iff_ae_haar_mk (p : CentreQuotient F G S j → Prop) :
    (∀ᵐ x ∂(Measure.haar : Measure (CentreQuotient F G S j)), p x) ↔
      ∀ᵐ g ∂(Measure.haar : Measure (AdelicGroupPoints F G)), p (CentreQuotient.mk F G S j g) :=
  (CentreQuotient.ae_haar_iff_ae_normOne F G hi I e hc h p).trans
    (ae_haar_iff_ae_normOne_of_decomposition F G hi I e hc
      (fun g => p (CentreQuotient.mk F G S j g)) (fun m => p (CentreQuotient.mk F G S j m))
      fun a _ => iff_of_eq (congrArg p (CentreQuotient.mk_mul_of_mem F G S j
        (positivePointMap_mem_subgroup F G h a) _))).symm

end Haar

section Cuspidal

variable (hZ : subgroup F G S j ≤ Subgroup.center (AdelicGroupPoints F G))

/-- The constant term along `P`, `g ↦ ∫_{[N_P]} φ(n g) dn`, as a function on
`A_G \ G(𝔸_F)`. -/
def centreQuotientParabolicPeriod (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) : CentreQuotient F G S j → ℂ :=
  CentreQuotient.lift F G S j (quotientFullParabolicPeriod F G hPD hG S j P φ) fun _ hz g =>
    quotientFullParabolicPeriod_mul F G hPD hG S j P φ hz (commute_of_le_center F G S j hZ hz) g

@[simp] theorem centreQuotientParabolicPeriod_mk (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) (g : AdelicGroupPoints F G) :
    centreQuotientParabolicPeriod F G hPD hG S j hZ P φ (CentreQuotient.mk F G S j g) =
      quotientFullParabolicPeriod F G hPD hG S j P φ g := rfl

/-- Absolute convergence of the `[N_P]` integral at a point of `A_G \ G(𝔸_F)`, for the
mass-one quotient measure; it does not depend on the representative. -/
def HasConvergentCentreQuotientParabolicPeriod (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) : CentreQuotient F G S j → Prop :=
  CentreQuotient.lift F G S j (HasConvergentQuotientFullParabolicPeriod F G hPD hG S j P φ)
    fun _ hz g => by
      rw [HasConvergentQuotientFullParabolicPeriod, HasConvergentQuotientFullParabolicPeriod,
        quotientFullParabolicPeriodIntegrand_mul F G hPD hG S j P φ hz
          (commute_of_le_center F G S j hZ hz)]

@[simp] theorem hasConvergentCentreQuotientParabolicPeriod_mk (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) (g : AdelicGroupPoints F G) :
    HasConvergentCentreQuotientParabolicPeriod F G hPD hG S j hZ P φ
        (CentreQuotient.mk F G S j g) ↔
      HasConvergentQuotientFullParabolicPeriod F G hPD hG S j P φ g := Iff.rfl

/-- For every proper rational parabolic, the `[N_P]` integral converges absolutely and vanishes
for almost every point of `A_G \ G(𝔸_F)`, for its Haar measure. -/
def IsCentreQuotientParabolicCuspidal (φ : Quotient F G S j → ℂ) : Prop :=
  ∀ P : ProperRationalParabolic G,
    (∀ᵐ x ∂(Measure.haar : Measure (CentreQuotient F G S j)),
      HasConvergentCentreQuotientParabolicPeriod F G hPD hG S j hZ P φ x) ∧
    centreQuotientParabolicPeriod F G hPD hG S j hZ P φ =ᵐ[
      (Measure.haar : Measure (CentreQuotient F G S j))] 0

/-- The condition may be stated with any regular Haar measure on `A_G \ G(𝔸_F)`. -/
theorem isCentreQuotientParabolicCuspidal_iff_of_regular
    (ν : Measure (CentreQuotient F G S j)) [ν.IsHaarMeasure] [ν.Regular]
    (φ : Quotient F G S j → ℂ) :
    IsCentreQuotientParabolicCuspidal F G hPD hG S j hZ φ ↔
      ∀ P : ProperRationalParabolic G,
        (∀ᵐ x ∂ν, HasConvergentCentreQuotientParabolicPeriod F G hPD hG S j hZ P φ x) ∧
        centreQuotientParabolicPeriod F G hPD hG S j hZ P φ =ᵐ[ν] 0 := by
  rw [IsCentreQuotientParabolicCuspidal, CentreQuotient.ae_eq_ae_haar F G S j ν]

end Cuspidal

section Comparison

variable {S j} (hZ : subgroup F G S j ≤ Subgroup.center (AdelicGroupPoints F G))
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (I : Type) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
variable (hc : IsCentral i)

include hi I e hc in
/-- With splitting coordinates, the condition over `A_G \ G(𝔸_F)` is the published a.e.
condition over the full adelic group. -/
theorem isCentreQuotientParabolicCuspidal_iff_full_of_splitting
    (h : subgroup F G S j = imageSubgroup F T G i) (φ : Quotient F G S j → ℂ) :
    IsCentreQuotientParabolicCuspidal F G hPD hG S j hZ φ ↔
      IsAEQuotientFullParabolicCuspidal F G hPD hG S j φ := by
  refine forall_congr' fun P => and_congr ?_ ?_
  · exact CentreQuotient.ae_haar_iff_ae_haar_mk F G hi I e hc h
      (HasConvergentCentreQuotientParabolicPeriod F G hPD hG S j hZ P φ)
  · exact CentreQuotient.ae_haar_iff_ae_haar_mk F G hi I e hc h
      (fun x => centreQuotientParabolicPeriod F G hPD hG S j hZ P φ x = 0)

include hi I e hc in
/-- With splitting coordinates, the condition over `A_G \ G(𝔸_F)` is the published a.e.
condition over `G(𝔸_F)¹`. -/
theorem isCentreQuotientParabolicCuspidal_iff_of_splitting
    (h : subgroup F G S j = imageSubgroup F T G i) (φ : Quotient F G S j → ℂ) :
    IsCentreQuotientParabolicCuspidal F G hPD hG S j hZ φ ↔
      IsAEQuotientParabolicCuspidal F G hPD hG S j φ :=
  (isCentreQuotientParabolicCuspidal_iff_full_of_splitting F G hPD hG hZ hi I e hc h φ).trans
    (isAEQuotientFullParabolicCuspidal_iff_of_splitting F G hPD hG hi I e hc h φ)

variable (hT : IsSplitTorus T.toGrp)

include hi hc hT in
/-- The comparison with splitting coordinates obtained from `IsSplitTorus`. -/
theorem isCentreQuotientParabolicCuspidal_iff
    (h : subgroup F G S j = imageSubgroup F T G i) (φ : Quotient F G S j → ℂ) :
    IsCentreQuotientParabolicCuspidal F G hPD hG S j hZ φ ↔
      IsAEQuotientParabolicCuspidal F G hPD hG S j φ := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  exact isCentreQuotientParabolicCuspidal_iff_of_splitting F G hPD hG hZ hi I e hc h φ

include hi hc hT in
/-- The published a.e. cuspidal locus of `L²([G])` is described by the condition over
`A_G \ G(𝔸_F)`. -/
theorem mem_quotientFullAEL2CuspidalLocus_iff_centreQuotient
    (h : subgroup F G S j = imageSubgroup F T G i) (measureQ : Measure (Quotient F G S j))
    (φ : Lp ℂ 2 measureQ) :
    φ ∈ quotientFullAEL2CuspidalLocus F G hPD hG S j measureQ ↔
      IsCentreQuotientParabolicCuspidal F G hPD hG S j hZ φ :=
  (isCentreQuotientParabolicCuspidal_iff F G hPD hG hZ hi hc hT h φ).symm

end Comparison

end Langlands.Global.RestrictionSplitCentre

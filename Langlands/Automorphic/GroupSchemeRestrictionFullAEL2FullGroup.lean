import Langlands.Automorphic.GroupSchemeRestrictionFullAEL2
import Langlands.Global.AdelicSplitCenterHaar

/-! # The almost-everywhere cuspidal condition over the full adelic group -/

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

section FullGroup

/-- The inclusion of the adelic points of the unipotent radical of `P` into `G(𝔸_F)`. -/
def properParabolicAmbientInclusion (P : ProperRationalParabolic G) :
    AdelicSubgroupPoints.adelicPoints F G (properRationalParabolicRadicals hPD hG P) →*
      AdelicGroupPoints F G :=
  (AdelicGroupPoints.normOneSubgroup F G).subtype.comp
    (properParabolicNormOneInclusion F G hPD hG P).toMonoidHom

/-- Rational points of the unipotent radical lie in `A_G G(F)`. -/
theorem properParabolicAmbientInclusion_rational_mem (P : ProperRationalParabolic G)
    (n : AdelicSubgroupPoints.rationalSubgroup F G (properRationalParabolicRadicals hPD hG P)) :
    properParabolicAmbientInclusion F G hPD hG P n.val ∈ rationalSubgroup F G S j :=
  principal_le_rationalSubgroup F G S j
    (AdelicGroupPoints.rationalNormOneSubgroupInclusion F G
      ⟨_, properParabolicNormOneInclusion_rational_mem F G hPD hG P n⟩).property

/-- The constant-term integrand over `[N_P]` at an arbitrary adelic point: `n ↦ φ(n g)`. -/
def quotientFullParabolicPeriodIntegrand (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) (g : AdelicGroupPoints F G) :
    AdelicSubgroupPoints.RationalQuotient F G (properRationalParabolicRadicals hPD hG P) → ℂ :=
  periodIntegrand (rationalSubgroup F G S j)
    (AdelicSubgroupPoints.rationalSubgroup F G (properRationalParabolicRadicals hPD hG P))
    (properParabolicAmbientInclusion F G hPD hG P)
    (properParabolicAmbientInclusion_rational_mem F G hPD hG S j P)
    1 (fun _ => rfl) φ g

@[simp]
theorem quotientFullParabolicPeriodIntegrand_mk (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) (g : AdelicGroupPoints F G)
    (n : AdelicSubgroupPoints.adelicPoints F G (properRationalParabolicRadicals hPD hG P)) :
    quotientFullParabolicPeriodIntegrand F G hPD hG S j P φ g
      (LeftCosetSpace.mk (AdelicSubgroupPoints.rationalSubgroup F G
        (properRationalParabolicRadicals hPD hG P)) n) =
      φ (LeftCosetSpace.mk (rationalSubgroup F G S j) ((n : AdelicGroupPoints F G) * g)) := by
  change (1 : ℂ)⁻¹ * _ = _
  rw [inv_one, one_mul]
  rfl

/-- At a norm-one point the full integrand is the published norm-one integrand. -/
theorem quotientFullParabolicPeriodIntegrand_normOne (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) (m : AdelicGroupPoints.normOneSubgroup F G) :
    quotientFullParabolicPeriodIntegrand F G hPD hG S j P φ m =
      quotientParabolicPeriodIntegrand F G hPD hG S j P φ m := by
  funext q
  obtain ⟨n, rfl⟩ := LeftCosetSpace.mk_surjective _ q
  rw [quotientFullParabolicPeriodIntegrand_mk, quotientParabolicPeriodIntegrand_mk]

/-- Left translation by a central point of the split-centre image does not change the
integrand. -/
theorem quotientFullParabolicPeriodIntegrand_mul (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) {z : AdelicGroupPoints F G} (hz : z ∈ subgroup F G S j)
    (hcomm : ∀ x : AdelicGroupPoints F G, Commute z x) (g : AdelicGroupPoints F G) :
    quotientFullParabolicPeriodIntegrand F G hPD hG S j P φ (z * g) =
      quotientFullParabolicPeriodIntegrand F G hPD hG S j P φ g := by
  funext q
  obtain ⟨n, rfl⟩ := LeftCosetSpace.mk_surjective _ q
  rw [quotientFullParabolicPeriodIntegrand_mk, quotientFullParabolicPeriodIntegrand_mk,
    ← mul_assoc, ← (hcomm (n : AdelicGroupPoints F G)).eq, mul_assoc]
  exact congrArg φ (LeftCosetSpace.mk_subgroup_mul (rationalSubgroup F G S j)
    ⟨z, subgroup_le_rationalSubgroup F G S j hz⟩ _)

/-- Absolute convergence of the `[N_P]` integral at an arbitrary adelic point, for the
mass-one quotient measure. -/
def HasConvergentQuotientFullParabolicPeriod (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) (g : AdelicGroupPoints F G) : Prop :=
  Integrable (quotientFullParabolicPeriodIntegrand F G hPD hG S j P φ g)
    (properParabolicQuotientMeasure F G hPD hG P)

/-- The constant term `g ↦ ∫_{[N_P]} φ(n g) dn` on all of `G(𝔸_F)`. -/
def quotientFullParabolicPeriod (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) (g : AdelicGroupPoints F G) : ℂ :=
  ∫ q, quotientFullParabolicPeriodIntegrand F G hPD hG S j P φ g q
    ∂properParabolicQuotientMeasure F G hPD hG P

theorem hasConvergentQuotientFullParabolicPeriod_normOne (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) (m : AdelicGroupPoints.normOneSubgroup F G) :
    HasConvergentQuotientFullParabolicPeriod F G hPD hG S j P φ m ↔
      HasConvergentQuotientParabolicPeriod F G hPD hG S j P φ m := by
  rw [HasConvergentQuotientFullParabolicPeriod, HasConvergentQuotientParabolicPeriod,
    quotientFullParabolicPeriodIntegrand_normOne]

theorem quotientFullParabolicPeriod_normOne (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) (m : AdelicGroupPoints.normOneSubgroup F G) :
    quotientFullParabolicPeriod F G hPD hG S j P φ m =
      quotientParabolicPeriod F G hPD hG S j P φ m := by
  rw [quotientFullParabolicPeriod, quotientParabolicPeriod,
    quotientFullParabolicPeriodIntegrand_normOne]

/-- The period is invariant under left translation by central points of the split-centre
image, so it is a function on `A_G \ G(𝔸_F)`. -/
theorem quotientFullParabolicPeriod_mul (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) {z : AdelicGroupPoints F G} (hz : z ∈ subgroup F G S j)
    (hcomm : ∀ x : AdelicGroupPoints F G, Commute z x) (g : AdelicGroupPoints F G) :
    quotientFullParabolicPeriod F G hPD hG S j P φ (z * g) =
      quotientFullParabolicPeriod F G hPD hG S j P φ g := by
  rw [quotientFullParabolicPeriod, quotientFullParabolicPeriod,
    quotientFullParabolicPeriodIntegrand_mul F G hPD hG S j P φ hz hcomm]

/-- For every proper rational parabolic, the `[N_P]` integral converges absolutely and vanishes
for almost every point of `G(𝔸_F)`, for its Haar measure. -/
def IsAEQuotientFullParabolicCuspidal (φ : Quotient F G S j → ℂ) : Prop :=
  ∀ P : ProperRationalParabolic G,
    (∀ᵐ g ∂(Measure.haar : Measure (AdelicGroupPoints F G)),
      HasConvergentQuotientFullParabolicPeriod F G hPD hG S j P φ g) ∧
    quotientFullParabolicPeriod F G hPD hG S j P φ =ᵐ[
      (Measure.haar : Measure (AdelicGroupPoints F G))] 0

end FullGroup

section Comparison

variable {S j} {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (I : Type) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
variable (hc : IsCentral i)

include hi I e hc in
/-- A property of adelic points that depends only on the norm-one factor holds almost
everywhere for Haar measure on `G(𝔸_F)` exactly when its norm-one form holds almost
everywhere for Haar measure on `G(𝔸_F)¹`. -/
theorem ae_haar_iff_ae_normOne_of_decomposition (p : AdelicGroupPoints F G → Prop)
    (q : AdelicGroupPoints.normOneSubgroup F G → Prop)
    (hp : ∀ (a : intrinsicSubgroup F T) (m : AdelicGroupPoints.normOneSubgroup F G),
      p (positivePointMap F G T i a * m) ↔ q m) :
    (∀ᵐ x ∂(Measure.haar : Measure (AdelicGroupPoints F G)), p x) ↔
      ∀ᵐ m ∂(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)), q m := by
  let := positiveIsTopologicalGroup F T I e
  let := normalizedPositiveHaarMeasure_isHaarMeasure F G T i hi I e hc
  let := normalizedPositiveHaarMeasure_sigmaFinite F G T i hi I e hc
  have hpres : MeasurePreserving (normOneDecomposition F G T i hi I e).toMeasurableEquiv.symm
      (Measure.haar : Measure (AdelicGroupPoints F G))
      ((normalizedPositiveHaarMeasure F G T i hi I e hc).prod
        (Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G))) :=
    measurePreserving_normOneDecomposition_symm F G T i hi I e hc
  have hset : {x | ¬ p x} = (normOneDecomposition F G T i hi I e).toMeasurableEquiv.symm ⁻¹'
      (Set.univ ×ˢ {m | ¬ q m}) := by
    ext x
    have hx := (normOneDecomposition F G T i hi I e).apply_symm_apply x
    rw [normOneDecomposition_symm_apply, normOneDecomposition_apply] at hx
    change ¬ p x ↔ True ∧ ¬ q (normOneFactor F G T i hi I e x)
    rw [true_and, ← hp (positiveFactor F G T i hi I e x), hx]
  have hpos : normalizedPositiveHaarMeasure F G T i hi I e hc Set.univ ≠ 0 :=
    isOpen_univ.measure_ne_zero _ Set.univ_nonempty
  rw [ae_iff, ae_iff, hset, hpres.measure_preimage_equiv, Measure.prod_prod, mul_eq_zero,
    or_iff_right hpos]

include hi I e hc in
/-- With the split-centre image equal to the positive image of `i`, the a.e. cuspidal
condition over `G(𝔸_F)` agrees with the published condition over `G(𝔸_F)¹`. -/
theorem isAEQuotientFullParabolicCuspidal_iff_of_splitting
    (h : subgroup F G S j = imageSubgroup F T G i) (φ : Quotient F G S j → ℂ) :
    IsAEQuotientFullParabolicCuspidal F G hPD hG S j φ ↔
      IsAEQuotientParabolicCuspidal F G hPD hG S j φ := by
  have hmem : ∀ a : intrinsicSubgroup F T, positivePointMap F G T i a ∈ subgroup F G S j := by
    intro a
    rw [h]
    exact ⟨a.val, a.property, rfl⟩
  have hint : ∀ (P : ProperRationalParabolic G) (a : intrinsicSubgroup F T)
      (m : AdelicGroupPoints.normOneSubgroup F G),
      quotientFullParabolicPeriodIntegrand F G hPD hG S j P φ
          (positivePointMap F G T i a * m) =
        quotientParabolicPeriodIntegrand F G hPD hG S j P φ m := by
    intro P a m
    rw [quotientFullParabolicPeriodIntegrand_mul F G hPD hG S j P φ (hmem a)
      (positivePointMap_commute F G T i hc a), quotientFullParabolicPeriodIntegrand_normOne]
  refine forall_congr' fun P => and_congr ?_ ?_
  · exact ae_haar_iff_ae_normOne_of_decomposition F G hi I e hc _ _ fun a m => by
      rw [HasConvergentQuotientFullParabolicPeriod, HasConvergentQuotientParabolicPeriod,
        hint P a m]
  · exact ae_haar_iff_ae_normOne_of_decomposition F G hi I e hc _ _ fun a m => by
      change quotientFullParabolicPeriod F G hPD hG S j P φ _ = 0 ↔
        quotientParabolicPeriod F G hPD hG S j P φ m = 0
      rw [quotientFullParabolicPeriod, quotientParabolicPeriod, hint P a m]

variable (hT : IsSplitTorus T.toGrp)

include hi hc hT in
/-- The comparison with splitting coordinates obtained from `IsSplitTorus`. -/
theorem isAEQuotientFullParabolicCuspidal_iff
    (h : subgroup F G S j = imageSubgroup F T G i) (φ : Quotient F G S j → ℂ) :
    IsAEQuotientFullParabolicCuspidal F G hPD hG S j φ ↔
      IsAEQuotientParabolicCuspidal F G hPD hG S j φ := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  exact isAEQuotientFullParabolicCuspidal_iff_of_splitting F G hPD hG hi I e hc h φ

include hi hc hT in
/-- The published a.e. cuspidal locus of `L²([G])` is described by the condition over the full
adelic group. -/
theorem mem_quotientFullAEL2CuspidalLocus_iff_full
    (h : subgroup F G S j = imageSubgroup F T G i) (measureQ : Measure (Quotient F G S j))
    (φ : Lp ℂ 2 measureQ) :
    φ ∈ quotientFullAEL2CuspidalLocus F G hPD hG S j measureQ ↔
      IsAEQuotientFullParabolicCuspidal F G hPD hG S j φ :=
  (isAEQuotientFullParabolicCuspidal_iff F G hPD hG hi hc hT h φ).symm

end Comparison

end Langlands.Global.RestrictionSplitCentre

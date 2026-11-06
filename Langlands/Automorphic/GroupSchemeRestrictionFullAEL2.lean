import Langlands.Automorphic.GroupSchemeFullAEL2
import Langlands.Automorphic.GroupSchemeParabolicL2ClosednessProof
import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2

/-! # The almost-everywhere cuspidal `L²` subspace of the restriction split-centre quotient -/

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

section Intrinsic

/-- The constant-term integrand over `[N_P]` of a function on the restriction quotient, at a
norm-one adelic point: `n ↦ φ(n g)`. -/
def quotientParabolicPeriodIntegrand (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) (g : AdelicGroupPoints.normOneSubgroup F G) :
    AdelicSubgroupPoints.RationalQuotient F G (properRationalParabolicRadicals hPD hG P) → ℂ :=
  periodIntegrand (AdelicGroupPoints.rationalNormOneSubgroup F G)
    (AdelicSubgroupPoints.rationalSubgroup F G (properRationalParabolicRadicals hPD hG P))
    (properParabolicNormOneInclusion F G hPD hG P).toMonoidHom
    (properParabolicNormOneInclusion_rational_mem F G hPD hG P)
    1 (fun _ => rfl) (fun q => φ (normOneToQuotient F G S j q)) g

@[simp]
theorem quotientParabolicPeriodIntegrand_mk (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) (g : AdelicGroupPoints.normOneSubgroup F G)
    (n : AdelicSubgroupPoints.adelicPoints F G (properRationalParabolicRadicals hPD hG P)) :
    quotientParabolicPeriodIntegrand F G hPD hG S j P φ g
      (LeftCosetSpace.mk (AdelicSubgroupPoints.rationalSubgroup F G
        (properRationalParabolicRadicals hPD hG P)) n) =
      φ (LeftCosetSpace.mk (rationalSubgroup F G S j)
        ((n : AdelicGroupPoints F G) * (g : AdelicGroupPoints F G))) := by
  change (1 : ℂ)⁻¹ * _ = _
  rw [inv_one, one_mul]
  rfl

/-- Absolute convergence of the `[N_P]` integral for the mass-one quotient measure. -/
def HasConvergentQuotientParabolicPeriod (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) (g : AdelicGroupPoints.normOneSubgroup F G) : Prop :=
  Integrable (quotientParabolicPeriodIntegrand F G hPD hG S j P φ g)
    (properParabolicQuotientMeasure F G hPD hG P)

/-- The constant term `g ↦ ∫_{[N_P]} φ(n g) dn` with the mass-one quotient measure. -/
def quotientParabolicPeriod (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) (g : AdelicGroupPoints.normOneSubgroup F G) : ℂ :=
  ∫ q, quotientParabolicPeriodIntegrand F G hPD hG S j P φ g q
    ∂properParabolicQuotientMeasure F G hPD hG P

/-- For every proper rational parabolic, the `[N_P]` integral converges absolutely and vanishes
for almost every norm-one adelic point. -/
def IsAEQuotientParabolicCuspidal (φ : Quotient F G S j → ℂ) : Prop :=
  ∀ P : ProperRationalParabolic G,
    (∀ᵐ g ∂(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)),
      HasConvergentQuotientParabolicPeriod F G hPD hG S j P φ g) ∧
    quotientParabolicPeriod F G hPD hG S j P φ =ᵐ[
      (Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G))] 0

/-- The `L²` classes, for a measure on the restriction quotient, whose representative satisfies
`IsAEQuotientParabolicCuspidal`. -/
def quotientFullAEL2CuspidalLocus (measureQ : Measure (Quotient F G S j)) :
    Set (Lp ℂ 2 measureQ) :=
  {φ | IsAEQuotientParabolicCuspidal F G hPD hG S j φ}

end Intrinsic

section Transport

variable {S j} {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (h : subgroup F G S j = imageSubgroup F T G i)

/-- The integrand is the positive-torus integrand of the transported function. -/
theorem quotientParabolicPeriodIntegrand_eq (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) (g : AdelicGroupPoints.normOneSubgroup F G) :
    quotientParabolicPeriodIntegrand F G hPD hG S j P φ g =
      properParabolicPositivePeriodIntegrand F G hPD hG T i P
        (φ ∘ quotientMeasurableEquiv F G h) g := by
  simp only [quotientParabolicPeriodIntegrand, properParabolicPositivePeriodIntegrand,
    Function.comp_apply, quotientMeasurableEquiv_normOneToPositiveQuotient]

theorem hasConvergentQuotientParabolicPeriod_iff (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) (g : AdelicGroupPoints.normOneSubgroup F G) :
    HasConvergentQuotientParabolicPeriod F G hPD hG S j P φ g ↔
      HasConvergentProperParabolicPositivePeriod F G hPD hG T i P
        (φ ∘ quotientMeasurableEquiv F G h) g := by
  unfold HasConvergentQuotientParabolicPeriod HasConvergentProperParabolicPositivePeriod
  rw [quotientParabolicPeriodIntegrand_eq F G hPD hG h]

theorem quotientParabolicPeriod_eq (P : ProperRationalParabolic G)
    (φ : Quotient F G S j → ℂ) :
    quotientParabolicPeriod F G hPD hG S j P φ =
      properParabolicPositivePeriod F G hPD hG T i P (φ ∘ quotientMeasurableEquiv F G h) := by
  funext g
  unfold quotientParabolicPeriod properParabolicPositivePeriod
  rw [quotientParabolicPeriodIntegrand_eq F G hPD hG h]

/-- The cuspidality condition is the positive-torus condition for the transported function. -/
theorem isAEQuotientParabolicCuspidal_iff (φ : Quotient F G S j → ℂ) :
    IsAEQuotientParabolicCuspidal F G hPD hG S j φ ↔
      φ ∘ quotientMeasurableEquiv F G h ∈ aeParabolicCuspidalFunctionSubmodule F G hPD hG T i := by
  change (∀ P, _ ∧ _) ↔ (∀ P, _ ∧ _)
  simp only [hasConvergentQuotientParabolicPeriod_iff F G hPD hG h,
    quotientParabolicPeriod_eq F G hPD hG h]

variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]

section Data

variable (I : Type) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)

include hi I e hc in
/-- With the canonical quotient measure, an `L²` class lies in the locus exactly when its
image under `quotientL2Equiv` lies in the published positive-torus locus. -/
theorem mem_quotientFullAEL2CuspidalLocus_iff (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    φ ∈ quotientFullAEL2CuspidalLocus F G hPD hG S j (quotientHaarMeasure F G S j) ↔
      (quotientL2Equiv F G h).symm φ ∈ fullAEL2CuspidalLocus F G hPD hG T i := by
  change IsAEQuotientParabolicCuspidal F G hPD hG S j φ ↔
    ((quotientL2Equiv F G h).symm φ : PositiveRationalQuotient F G T i → ℂ) ∈
      aeParabolicCuspidalFunctionSubmodule F G hPD hG T i
  rw [isAEQuotientParabolicCuspidal_iff F G hPD hG h]
  exact mem_aeParabolicCuspidalFunctionSubmodule_congr F G hPD hG T i hi I e hc _ _
    ((Lp.stronglyMeasurable φ).comp_measurable (quotientMeasurableEquiv F G h).measurable)
    (Lp.stronglyMeasurable _) (coeFn_quotientL2Equiv_symm F G h φ).symm

include hi I e hc in
/-- The locus is the preimage of the published positive-torus locus. -/
theorem quotientFullAEL2CuspidalLocus_eq_preimage :
    quotientFullAEL2CuspidalLocus F G hPD hG S j (quotientHaarMeasure F G S j) =
      (quotientL2Equiv F G h).symm ⁻¹' fullAEL2CuspidalLocus F G hPD hG T i := by
  ext φ
  exact mem_quotientFullAEL2CuspidalLocus_iff F G hPD hG h hi I e hc φ

end Data

variable (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)

include hi hc hT in
theorem mem_quotientFullAEL2CuspidalLocus_iff_of_splitTorus
    (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    φ ∈ quotientFullAEL2CuspidalLocus F G hPD hG S j (quotientHaarMeasure F G S j) ↔
      (quotientL2Equiv F G h).symm φ ∈ fullAEL2CuspidalLocus F G hPD hG T i := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  exact mem_quotientFullAEL2CuspidalLocus_iff F G hPD hG h hi I e hc φ

/-- The locus as a complex subspace of `L²` for the canonical quotient measure. -/
def quotientFullAEL2CuspidalSubmodule :
    Submodule ℂ (Lp ℂ 2 (quotientHaarMeasure F G S j)) where
  carrier := quotientFullAEL2CuspidalLocus F G hPD hG S j (quotientHaarMeasure F G S j)
  zero_mem' := by
    obtain ⟨I, hI, ⟨e⟩⟩ := hT
    let := Fintype.ofFinite I
    apply (mem_quotientFullAEL2CuspidalLocus_iff F G hPD hG h hi I e hc _).mpr
    rw [map_zero]
    exact (fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc).zero_mem
  add_mem' := by
    intro φ ψ hφ hψ
    obtain ⟨I, hI, ⟨e⟩⟩ := hT
    let := Fintype.ofFinite I
    have hφ' := (mem_quotientFullAEL2CuspidalLocus_iff F G hPD hG h hi I e hc φ).mp hφ
    have hψ' := (mem_quotientFullAEL2CuspidalLocus_iff F G hPD hG h hi I e hc ψ).mp hψ
    apply (mem_quotientFullAEL2CuspidalLocus_iff F G hPD hG h hi I e hc _).mpr
    rw [map_add]
    exact (fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc).add_mem hφ' hψ'
  smul_mem' := by
    intro z φ hφ
    obtain ⟨I, hI, ⟨e⟩⟩ := hT
    let := Fintype.ofFinite I
    have hφ' := (mem_quotientFullAEL2CuspidalLocus_iff F G hPD hG h hi I e hc φ).mp hφ
    apply (mem_quotientFullAEL2CuspidalLocus_iff F G hPD hG h hi I e hc _).mpr
    rw [map_smul]
    exact (fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc).smul_mem z hφ'

@[simp]
theorem mem_quotientFullAEL2CuspidalSubmodule (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    φ ∈ quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT ↔
      φ ∈ quotientFullAEL2CuspidalLocus F G hPD hG S j (quotientHaarMeasure F G S j) :=
  Iff.rfl

variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]

include h hi hc hT in
/-- The locus is closed, by the published closedness of the positive-torus locus. -/
theorem isClosed_quotientFullAEL2CuspidalLocus :
    IsClosed (quotientFullAEL2CuspidalLocus F G hPD hG S j (quotientHaarMeasure F G S j)) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  rw [quotientFullAEL2CuspidalLocus_eq_preimage F G hPD hG h hi I e hc]
  exact (groupSchemeParabolicL2Closedness F G hPD hG T i hi I e hc).2.2.preimage
    (quotientL2Equiv F G h).symm.continuous

theorem isClosed_quotientFullAEL2CuspidalSubmodule :
    IsClosed (quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT :
      Set (Lp ℂ 2 (quotientHaarMeasure F G S j))) :=
  isClosed_quotientFullAEL2CuspidalLocus F G hPD hG h hi hc hT

/-- The subspace is a Hilbert space. -/
theorem completeSpace_quotientFullAEL2CuspidalSubmodule :
    CompleteSpace (quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT) :=
  (isClosed_quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT).completeSpace_coe

variable (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j))

/-- The subspace is stable under the right regular representation of `G(𝔸_F)`. -/
def quotientFullAEL2CuspidalSubrepresentation :
    Subrepresentation (rationalQuotientL2RightAction F G (quotientHaarMeasure F G S j) hInv') where
  toSubmodule := quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT
  apply_mem_toSubmodule g φ hφ := by
    obtain ⟨I, hI, ⟨e⟩⟩ := hT
    let := Fintype.ofFinite I
    have hφ' := (mem_quotientFullAEL2CuspidalLocus_iff F G hPD hG h hi I e hc φ).mp hφ
    apply (mem_quotientFullAEL2CuspidalLocus_iff F G hPD hG h hi I e hc _).mpr
    have hR := quotientL2Equiv_rightAction F G h
      (haarQuotientMeasureRightInvariant F G T i hi I e hc) hInv' g ((quotientL2Equiv F G h).symm φ)
    rw [LinearIsometryEquiv.apply_symm_apply] at hR
    rw [← hR, LinearIsometryEquiv.symm_apply_apply]
    exact (fullAEL2CuspidalSubrepresentation F G hPD hG T i hi I e hc).apply_mem_toSubmodule g hφ'

/-- Right translation restricted to the subspace. -/
def quotientFullAEL2CuspidalRightAction :
    Representation ℂ (AdelicGroupPoints F G)
      (quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT) :=
  (quotientFullAEL2CuspidalSubrepresentation F G hPD hG h hi hc hT hInv').toRepresentation

theorem norm_quotientFullAEL2CuspidalRightAction (g : AdelicGroupPoints F G)
    (φ : quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT) :
    ‖quotientFullAEL2CuspidalRightAction F G hPD hG h hi hc hT hInv' g φ‖ = ‖φ‖ :=
  (rationalQuotientL2RightTranslate F G _ hInv' g).norm_map φ.val

/-- The inclusion into `L²` intertwines the right actions. -/
def quotientFullAEL2CuspidalToLp :
    (quotientFullAEL2CuspidalRightAction F G hPD hG h hi hc hT hInv').IntertwiningMap
      (rationalQuotientL2RightAction F G (quotientHaarMeasure F G S j) hInv') where
  toLinearMap := (quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT).subtype
  isIntertwining' _ := rfl

end Transport

section Independence

variable {S j}

/-- The subspace does not depend on the auxiliary positive-torus data used to prove closure. -/
theorem quotientFullAEL2CuspidalSubmodule_eq
    {T T' : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G}
    (h : subgroup F G S j = imageSubgroup F T G i)
    (h' : subgroup F G S j = imageSubgroup F T' G i')
    (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (hi' : Function.Injective (characterRestrict i')) [(characterRestrict i').range.FiniteIndex]
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)
    (hc' : IsCentral i') (hT' : IsSplitTorus T'.toGrp) :
    quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT =
      quotientFullAEL2CuspidalSubmodule F G hPD hG h' hi' hc' hT' :=
  Submodule.ext fun _ => Iff.rfl

end Independence

section Comparison

variable {S j} {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (h : subgroup F G S j = imageSubgroup F T G i)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (I : Type) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)

/-- `quotientL2Equiv` restricts to an isometric isomorphism between the published
positive-torus subspace and the restriction-quotient subspace. -/
def fullAEL2CuspidalEquiv :
    fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc ≃ₗᵢ[ℂ]
      quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc ⟨I, inferInstance, ⟨e⟩⟩ where
  toFun φ := ⟨quotientL2Equiv F G h φ.val,
    (mem_quotientFullAEL2CuspidalLocus_iff F G hPD hG h hi I e hc _).mpr
      (by rw [LinearIsometryEquiv.symm_apply_apply]; exact φ.property)⟩
  invFun φ := ⟨(quotientL2Equiv F G h).symm φ.val,
    (mem_quotientFullAEL2CuspidalLocus_iff F G hPD hG h hi I e hc _).mp φ.property⟩
  left_inv φ := Subtype.ext ((quotientL2Equiv F G h).symm_apply_apply φ.val)
  right_inv φ := Subtype.ext ((quotientL2Equiv F G h).apply_symm_apply φ.val)
  map_add' _ _ := Subtype.ext (map_add (quotientL2Equiv F G h) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (quotientL2Equiv F G h) _ _)
  norm_map' φ := (quotientL2Equiv F G h).norm_map φ.val

@[simp]
theorem coe_fullAEL2CuspidalEquiv (φ : fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc) :
    (fullAEL2CuspidalEquiv F G hPD hG h hi I e hc φ :
      Lp ℂ 2 (quotientHaarMeasure F G S j)) = quotientL2Equiv F G h φ.val :=
  rfl

variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]
variable (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j))

/-- The isomorphism intertwines the published positive-torus action with the
restriction-quotient action. -/
theorem fullAEL2CuspidalEquiv_rightAction (g : AdelicGroupPoints F G)
    (φ : fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc) :
    fullAEL2CuspidalEquiv F G hPD hG h hi I e hc
        (fullAEL2CuspidalRightAction F G hPD hG T i hi I e hc g φ) =
      quotientFullAEL2CuspidalRightAction F G hPD hG h hi hc ⟨I, inferInstance, ⟨e⟩⟩ hInv' g
        (fullAEL2CuspidalEquiv F G hPD hG h hi I e hc φ) :=
  Subtype.ext (quotientL2Equiv_rightAction F G h
    (haarQuotientMeasureRightInvariant F G T i hi I e hc) hInv' g φ.val)

end Comparison

section SplitComponents

variable {S j} {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (hj : IsSplitComponent j) (hs : IsSplitComponent i)

/-- For split components, the cuspidal subspace of `L²` of the restriction quotient with its
canonical measure. -/
def splitComponentFullAEL2CuspidalSubmodule :
    Submodule ℂ (Lp ℂ 2 (quotientHaarMeasure F G S j)) :=
  quotientFullAEL2CuspidalSubmodule F G hPD hG (subgroup_eq_of_splitComponents F G hj hs) hi
    hs.1.2 hs.1.1.1

@[simp]
theorem mem_splitComponentFullAEL2CuspidalSubmodule
    (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    φ ∈ splitComponentFullAEL2CuspidalSubmodule F G hPD hG hi hj hs ↔
      φ ∈ quotientFullAEL2CuspidalLocus F G hPD hG S j (quotientHaarMeasure F G S j) :=
  Iff.rfl

/-- For split components, `splitComponentL2Equiv` carries the published positive-torus locus
onto the restriction-quotient locus. -/
theorem mem_splitComponentFullAEL2CuspidalSubmodule_iff
    (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    φ ∈ splitComponentFullAEL2CuspidalSubmodule F G hPD hG hi hj hs ↔
      (splitComponentL2Equiv F G hj hs).symm φ ∈ fullAEL2CuspidalLocus F G hPD hG T i :=
  mem_quotientFullAEL2CuspidalLocus_iff_of_splitTorus F G hPD hG
    (subgroup_eq_of_splitComponents F G hj hs) hi hs.1.2 hs.1.1.1 φ

variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]

theorem isClosed_splitComponentFullAEL2CuspidalSubmodule :
    IsClosed (splitComponentFullAEL2CuspidalSubmodule F G hPD hG hi hj hs :
      Set (Lp ℂ 2 (quotientHaarMeasure F G S j))) :=
  isClosed_quotientFullAEL2CuspidalSubmodule F G hPD hG (subgroup_eq_of_splitComponents F G hj hs) hi
    hs.1.2 hs.1.1.1

/-- For split components, the cuspidal subrepresentation of `splitComponentL2RightAction`. -/
def splitComponentFullAEL2CuspidalSubrepresentation :
    Subrepresentation (splitComponentL2RightAction F G hi hj hs) :=
  quotientFullAEL2CuspidalSubrepresentation F G hPD hG (subgroup_eq_of_splitComponents F G hj hs) hi
    hs.1.2 hs.1.1.1
    (quotientHaarMeasure_rightInvariant_of_splitComponents F G hi hj hs)

end SplitComponents

end Langlands.Global.RestrictionSplitCentre

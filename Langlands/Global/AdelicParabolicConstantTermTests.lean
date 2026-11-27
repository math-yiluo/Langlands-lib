import Langlands.Global.AdelicLeviPairingAutomorphicTests
import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.Global.AdelicConstantTermAutomorphyProof

/-! # Constant terms and Levi tests of moderate-growth functions on parabolic quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (Q J : StandardIndex F G fam.i fam.ν)

local notation "Y" => (AdelicGroupPoints F G → ℂ)
local notation "UJ" => SubgroupFunctor.range (fam.iU J ≫ fam.p J)
local notation "ΔJ" => AdelicSubgroupPoints.rationalSubgroup F G UJ
local notation "μU" => AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G UJ
local notation "ΓQ" => parabolicQuotientSubgroup F (fam.p Q) (fam.iU Q) (fam.l Q)
local notation "ι" => AdelicGroupPoints.map F (fam.M J) G (fam.l J ≫ fam.p J)

/-- For `J ≤ Q`, the rational points of the Levi `M_J` lie in `U_Q(𝔸) M_Q(F)`. -/
theorem rationalLeviImage_le_of_le (hJQ : J ≤ Q) :
    rationalImage F (fam.l J ≫ fam.p J) ≤ ΓQ := by
  have hle : SubgroupFunctor.range (fam.l J ≫ fam.p J) ≤ SubgroupFunctor.range (fam.p Q) :=
    (SubgroupFunctor.range_comp_le _ _).trans ((fam.le_iff_range_le J Q).mp hJQ)
  let : IsClosedImmersion (fam.p Q).hom.hom.left := (fam.isCompatible Q).parabolic.isClosedSubgroup
  have hcomp := SubgroupFunctor.rangeFactor_comp (fam.l J ≫ fam.p J) (fam.p Q) hle
  rw [← hcomp]
  exact (rationalImage_comp_le _ _).trans (rationalImage_le_parabolicQuotientSubgroup _ _ _
    (fam.isCompatible Q).levi (fam.isUnipotentRadical Q))

section Integrand

variable {Q J}

local instance parabolicTestsClosedRadical :
    IsClosed (AdelicSubgroupPoints.adelicPoints F G UJ : Set (AdelicGroupPoints F G)) :=
  AdelicSubgroupPoints.isClosed_adelicPoints_range F G (fam.iU J ≫ fam.p J)

local instance parabolicTestsRadicalBorel : BorelSpace (AdelicSubgroupPoints.RationalQuotient F G UJ) :=
  AdelicSubgroupPoints.rationalQuotientBorelSpace F G UJ

private theorem radical_lift_invariant (hJQ : J ≤ Q) {f : Y}
    (hinv : ∀ x ∈ ΓQ, ∀ g, f (x * g) = f g) (g : AdelicGroupPoints F G) (x : ΔJ)
    (y : AdelicSubgroupPoints.adelicPoints F G UJ) :
    f (((x.val * y : AdelicSubgroupPoints.adelicPoints F G UJ) : AdelicGroupPoints F G) * g) =
      f ((y : AdelicGroupPoints F G) * g) := by
  change f (((x.val : AdelicGroupPoints F G) * y.val) * g) = f (y.val * g)
  rw [mul_assoc]
  exact hinv _ (fam.rationalRadicalImage_le_of_le hJQ
    ((mem_rationalSubgroup_range_iff _ x.val).mp x.2)) _

/-- The constant-term integrand of a `U_J(F)`-invariant function, on the compact quotient. -/
def radicalIntegrand (hJQ : J ≤ Q) {f : Y} (hinv : ∀ x ∈ ΓQ, ∀ g, f (x * g) = f g)
    (g : AdelicGroupPoints F G) :
    AdelicSubgroupPoints.RationalQuotient F G UJ → ℂ :=
  LeftCosetSpace.lift ΔJ (fun y => f ((y : AdelicGroupPoints F G) * g))
    (fam.radical_lift_invariant hJQ hinv g)

theorem radicalIntegrand_mk (hJQ : J ≤ Q) {f : Y} (hinv : ∀ x ∈ ΓQ, ∀ g, f (x * g) = f g)
    (g : AdelicGroupPoints F G)
    (y : AdelicSubgroupPoints.adelicPoints F G UJ) :
    fam.radicalIntegrand hJQ hinv g (LeftCosetSpace.mk ΔJ y) = f ((y : AdelicGroupPoints F G) * g) :=
  rfl

theorem constantTerm_eq_integral_radicalIntegrand (hJQ : J ≤ Q) {f : Y}
    (hinv : ∀ x ∈ ΓQ, ∀ g, f (x * g) = f g) (g : AdelicGroupPoints F G) :
    fam.constantTerm J f g = ∫ q, fam.radicalIntegrand hJQ hinv g q ∂μU := by
  unfold constantTerm subgroupConstantTerm
  congr 1
  funext q
  exact congrArg (fam.radicalIntegrand hJQ hinv g) (Quotient.out_eq q)

/-- The constant term along `U_J` of a continuous function on `U_Q(𝔸) M_Q(F) \ G(𝔸)`,
`J ≤ Q`, is continuous. -/
theorem continuous_constantTerm_of_le (hJQ : J ≤ Q) {f : Y}
    (hinv : ∀ x ∈ ΓQ, ∀ g, f (x * g) = f g) (hcont : Continuous f) : Continuous (fam.constantTerm J f) := by
  let := fam.compactSpace_radicalRationalQuotient J
  let : IsProbabilityMeasure μU :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G UJ
  rw [show fam.constantTerm J f = fun g => ∫ q, fam.radicalIntegrand hJQ hinv g q ∂μU from
    funext (fam.constantTerm_eq_integral_radicalIntegrand hJQ hinv)]
  have hc : Continuous (Function.uncurry (fam.radicalIntegrand hJQ hinv)) := by
    rw [← (IsOpenQuotientMap.id.prodMap
      (LeftCosetSpace.isOpenQuotientMap_mk ΔJ)).continuous_comp_iff]
    change Continuous (fun x : AdelicGroupPoints F G × AdelicSubgroupPoints.adelicPoints F G UJ =>
      f ((x.2 : AdelicGroupPoints F G) * x.1))
    exact hcont.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
  rw [← continuousOn_univ]
  exact continuousOn_integral_of_compact_support («μ» := μU) isCompact_univ hc.continuousOn
    (by simp)

/-- The constant term along `U_J` of a function on `U_Q(𝔸) M_Q(F) \ G(𝔸)`, `J ≤ Q`, is left
invariant under the rational points of the Levi `M_J`. -/
theorem constantTerm_leviRational_mul_of_le (hJQ : J ≤ Q) {f : Y}
    (hinv : ∀ x ∈ ΓQ, ∀ g, f (x * g) = f g) (q : RationalGroupPoints F (fam.M J))
    (g : AdelicGroupPoints F G) :
    fam.constantTerm J f (ι (rational F (fam.M J) q) * g) = fam.constantTerm J f g := by
  let U := UJ
  let P := SubgroupFunctor.range (fam.p J)
  have hUP : U.IsNormalizedBy P := by
    intro X y x hy hx
    change y ∈ (SubgroupFunctor.range (fam.p J)).carrier X at hy
    change x ∈ (SubgroupFunctor.range (fam.iU J ≫ fam.p J)).carrier X at hx
    change y * x * y⁻¹ ∈ (SubgroupFunctor.range (fam.iU J ≫ fam.p J)).carrier X
    rw [(fam.isCompatible J).parabolic_eq] at hy
    rw [fam.range_radical_eq_standardUnipotent J] at hx ⊢
    exact StandardLeviIntersection.conj_mem_standardUnipotent fam.i fam.ν hy hx
  let q' : AdelicSubgroupPoints.rationalPoints F G P :=
    ⟨(fam.M J).affinePointsTarget (fam.l J ≫ fam.p J) (CommAlgCat.of F F) q,
      SubgroupFunctor.mem_range.mpr ⟨q ≫ (fam.l J).hom.hom, by
        simp only [GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc]⟩⟩
  have hq : rational F G q'.val = ι (rational F (fam.M J) q) :=
    DFunLike.congr_fun (AdelicGroupPoints.rational_naturality F (fam.M J) (fam.l J ≫ fam.p J)) q
  have hqΓ : rational F G q'.val ∈ ΓQ := by
    rw [hq]
    exact fam.rationalLeviImage_le_of_le Q J hJQ ⟨q, rfl⟩
  let := fam.compactSpace_radicalRationalQuotient J
  let a := AdelicSubgroupPoints.adelicNormalizerConj F G hUP
    (AdelicSubgroupPoints.rational F G P q'⁻¹)
  have ha := AdelicSubgroupPoints.adelicNormalizerConj_mem_rationalSubgroup_iff F G hUP q'⁻¹
  let e := QuotientIntegration.quotientAutomorphism ΔJ a ha
  have he := AdelicSubgroupPoints.measurePreserving_rationalQuotientAutomorphism F G U a ha
  have hfun : fam.radicalIntegrand hJQ hinv (rational F G q'.val * g) =
      fam.radicalIntegrand hJQ hinv g ∘ e := by
    funext x
    obtain ⟨n, rfl⟩ := LeftCosetSpace.mk_surjective ΔJ x
    change f ((n : AdelicGroupPoints F G) * (rational F G q'.val * g)) =
      f ((a n : AdelicGroupPoints F G) * g)
    have hmul : (n : AdelicGroupPoints F G) * (rational F G q'.val * g) =
        rational F G q'.val * ((a n : AdelicGroupPoints F G) * g) := by
      simp [a, mul_assoc]
    rw [hmul]
    exact hinv _ hqΓ _
  rw [← hq, fam.constantTerm_eq_integral_radicalIntegrand hJQ hinv,
    fam.constantTerm_eq_integral_radicalIntegrand hJQ hinv, hfun]
  exact he.integral_comp e.measurableEmbedding _

private theorem compact_radical_representatives :
    ∃ Kc : Set (AdelicSubgroupPoints.adelicPoints F G UJ), IsCompact Kc ∧
      ∀ q : AdelicSubgroupPoints.RationalQuotient F G UJ, ∃ y ∈ Kc, LeftCosetSpace.mk ΔJ y = q := by
  classical
  let := fam.compactSpace_radicalRationalQuotient J
  let : LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G UJ) :=
    (parabolicTestsClosedRadical fam (J := J)).locallyCompactSpace
  choose K hKc hKn using fun b : AdelicSubgroupPoints.adelicPoints F G UJ => exists_compact_mem_nhds b
  let V (b : AdelicSubgroupPoints.adelicPoints F G UJ) :
      Set (AdelicSubgroupPoints.RationalQuotient F G UJ) := LeftCosetSpace.mk ΔJ '' interior (K b)
  have ho : ∀ b, IsOpen (V b) := fun b =>
    (LeftCosetSpace.isOpenQuotientMap_mk ΔJ).isOpenMap _ isOpen_interior
  have hcover : (Set.univ : Set (AdelicSubgroupPoints.RationalQuotient F G UJ)) ⊆ ⋃ b, V b := by
    intro q _
    obtain ⟨b, rfl⟩ := LeftCosetSpace.mk_surjective ΔJ q
    exact Set.mem_iUnion.mpr ⟨b, b, mem_interior_iff_mem_nhds.mpr (hKn b), rfl⟩
  obtain ⟨fin, hfin⟩ := isCompact_univ.elim_finite_subcover V ho hcover
  refine ⟨⋃ b ∈ fin, K b, fin.finite_toSet.isCompact_biUnion (fun b _ => hKc b), fun q => ?_⟩
  obtain ⟨b, hb, y, hy, rfl⟩ := Set.mem_iUnion₂.mp (hfin (Set.mem_univ q))
  exact ⟨y, Set.mem_iUnion₂.mpr ⟨b, hb, interior_subset hy⟩, rfl⟩

variable {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)

local notation "Hgt" => RepresentationGrowth.adelicHeight F G rho
local notation "Nrm" => RepresentationGrowth.adelicSourceNorm F G rho

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
include hN in
private theorem sourceNorm_mul_le' (x g : AdelicGroupPoints F G) :
    Nrm (x * g) ≤ Hgt x * Nrm g := by
  let C : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
  have hC : 0 < C := pow_pos (by exact_mod_cast hN) _
  apply le_of_mul_le_mul_left _ hC
  calc
    C * Nrm (x * g) = Hgt (x * g) :=
      (RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho _).symm
    _ ≤ Hgt x * Hgt g := RepresentationGrowth.adelicHeight_mul_le F G rho hN x g
    _ = C * (Hgt x * Nrm g) := by
      rw [RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho g]
      change Hgt x * (C * Nrm g) = _
      ring

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
include hN in
private theorem sourceNorm_rpow_mul_le' (R : ℝ) (x g : AdelicGroupPoints F G) :
    Nrm (x * g) ^ R ≤ Hgt x ^ |R| * Nrm g ^ R := by
  have hp (y) : 0 < Nrm y := RepresentationGrowth.adelicSourceNorm_pos F G rho hN y
  have hx : 0 < Hgt x := zero_lt_one.trans_le (RepresentationGrowth.one_le_adelicHeight F G rho hN x)
  by_cases hR : 0 ≤ R
  · rw [abs_of_nonneg hR, ← Real.mul_rpow hx.le (hp g).le]
    exact Real.rpow_le_rpow (hp _).le (sourceNorm_mul_le' rho hN x g) hR
  · have hinv : Nrm g ≤ Hgt x * Nrm (x * g) := by
      simpa only [inv_mul_cancel_left, RepresentationGrowth.adelicHeight_inv] using
        sourceNorm_mul_le' rho hN x⁻¹ (x * g)
    have hb := Real.rpow_le_rpow_of_nonpos (hp g) hinv (le_of_not_ge hR)
    rw [Real.mul_rpow hx.le (hp _).le] at hb
    rw [abs_of_nonpos (le_of_not_ge hR), Real.rpow_neg hx.le, ← div_eq_inv_mul]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hx R)).2 (by rwa [mul_comm])

include hN in
/-- The constant term along `U_J` of a function of moderate growth on
`U_Q(𝔸) M_Q(F) \ G(𝔸)`, `J ≤ Q`, has moderate growth with the same exponent. -/
theorem hasModerateGrowth_constantTerm_of_le (hJQ : J ≤ Q) {f : Y}
    (hinv : ∀ x ∈ ΓQ, ∀ g, f (x * g) = f g) (hgrowth : HasModerateGrowthFunction F G rho f) :
    HasModerateGrowthFunction F G rho (fam.constantTerm J f) := by
  obtain ⟨C, hC, r, hf⟩ := hgrowth
  obtain ⟨Kc, hKc, hsurj⟩ := fam.compact_radical_representatives (J := J)
  let b (y : AdelicSubgroupPoints.adelicPoints F G UJ) : ℝ := Hgt y.val ^ |r|
  have hb : Continuous b :=
    ((RepresentationGrowth.continuous_adelicHeight F G rho hN).comp continuous_subtype_val).rpow_const
      (fun _ => Or.inr (abs_nonneg r))
  obtain ⟨B, hB⟩ := hKc.bddAbove_image hb.continuousOn
  let := fam.compactSpace_radicalRationalQuotient J
  let : IsProbabilityMeasure μU :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G UJ
  refine ⟨C * max B 1, mul_pos hC (lt_of_lt_of_le zero_lt_one (le_max_right _ _)), r, fun g => ?_⟩
  rw [fam.constantTerm_eq_integral_radicalIntegrand hJQ hinv]
  refine (norm_integral_le_of_norm_le_const (C := C * max B 1 * Nrm g ^ r)
    (Filter.Eventually.of_forall fun q => ?_)).trans_eq (by simp)
  obtain ⟨y, hy, rfl⟩ := hsurj q
  rw [fam.radicalIntegrand_mk hJQ hinv]
  have hNg : 0 ≤ Nrm g ^ r :=
    Real.rpow_nonneg (RepresentationGrowth.adelicSourceNorm_pos F G rho hN g).le _
  calc
    ‖f ((y : AdelicGroupPoints F G) * g)‖ ≤ C * Nrm ((y : AdelicGroupPoints F G) * g) ^ r := hf _
    _ ≤ C * (b y * Nrm g ^ r) :=
      mul_le_mul_of_nonneg_left (sourceNorm_rpow_mul_le' rho hN r y.val g) hC.le
    _ ≤ C * (max B 1 * Nrm g ^ r) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        ((hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)) hNg) hC.le
    _ = C * max B 1 * Nrm g ^ r := by ring

include hN in
/-- The constant term along `U_J` of a continuous function of moderate growth on
`U_Q(𝔸) M_Q(F) \ G(𝔸)`, `J ≤ Q`, has absolutely convergent norm-one Levi pairings against
every continuous rationally invariant test with integrable weighted majorants. -/
theorem constantTerm_mem_leviPairingDomain_of_le (hJQ : J ≤ Q) {f : Y}
    (hinv : ∀ x ∈ ΓQ, ∀ g, f (x * g) = f g) (hcont : Continuous f)
    (hgrowth : HasModerateGrowthFunction F G rho f) {test : AdelicGroupPoints F (fam.M J) → ℂ}
    (htc : Continuous test)
    (hti : IsLeftInvariantUnder F (fam.M J) (rationalSubgroup F (fam.M J)) test)
    (hmaj : ∀ g (R : ℝ), fam.HasLeviPairingMajorant J test g rho R) :
    fam.constantTerm J f ∈ fam.leviPairingDomain J test :=
  fam.mem_leviPairingDomain_of_moderateGrowth J rho
    (fun x hx g => by
      obtain ⟨q, rfl⟩ := hx
      exact fam.constantTerm_leviRational_mul_of_le hJQ hinv q g)
    (fam.continuous_constantTerm_of_le hJQ hinv hcont)
    (fam.hasModerateGrowth_constantTerm_of_le rho hN hJQ hinv hgrowth) htc hti hmaj

/-- The constant term along `U_J` is linear on finite combinations of continuous functions on
`U_Q(𝔸) M_Q(F) \ G(𝔸)`, `J ≤ Q`. -/
theorem constantTerm_finset_sum_of_le (hJQ : J ≤ Q) {κ : Type*} (t : Finset κ) (c : κ → ℂ)
    (f : κ → Y) (hcont : ∀ i ∈ t, Continuous (f i))
    (hinv : ∀ i ∈ t, ∀ x ∈ ΓQ, ∀ g, f i (x * g) = f i g) :
    fam.constantTerm J (∑ i ∈ t, c i • f i) = ∑ i ∈ t, c i • fam.constantTerm J (f i) := by
  funext g
  have hint (i : κ) (hi : i ∈ t) := fam.integrable_constantTermIntegrand_of_le Q J hJQ
    (hcont i hi) (hinv i hi) g
  unfold constantTerm subgroupConstantTerm
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_finsetSum t fun i hi => (hint i hi).const_mul (c i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul (c i) _

end Integrand

end Langlands.Global.StandardParabolicFamily

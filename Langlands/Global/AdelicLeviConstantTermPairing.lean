import Langlands.Global.AdelicConstantTermEvaluation
import Langlands.Global.AdelicConstantTermTransitivity

/-! # Continuous Levi pairings of unipotent constant terms -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Filter
open scoped CategoryTheory.MonObj Topology

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G) (J : StandardIndex F G 𝓕.i 𝓕.ν)

local notation "M" => 𝓕.M J
local notation "j" => 𝓕.iU J ≫ 𝓕.p J
local notation "ι" => AdelicGroupPoints.map F M G (𝓕.l J ≫ 𝓕.p J)
local notation "Γ" => rationalNormOneSubgroup F M
local notation "μ" => normOneRationalQuotientHaarMeasure F M

/-- The constant term of a continuous rational-invariant input is continuous in its
ambient adelic argument. -/
theorem continuous_constantTerm (f : ContinuousRationalFunctions F G) :
    Continuous (𝓕.constantTerm J (evaluate F G f)) := by
  let := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let := 𝓕.compactSpace_radicalRationalQuotient J
  have heq : 𝓕.constantTerm J (evaluate F G f) =
      AdelicSubgroupPoints.normalizedConstantTerm F G (SubgroupFunctor.range j) f :=
    funext fun g =>
      (AdelicSubgroupPoints.normalizedConstantTerm_range_eq_subgroupConstantTerm F G j f g).symm
  rw [heq]
  exact AdelicSubgroupPoints.continuous_normalizedConstantTerm F G (SubgroupFunctor.range j) f

/-- The constant term of a rational-invariant input is left invariant under the image
of the principal points of its standard Levi. -/
theorem constantTerm_leviRational_mul (f : ContinuousRationalFunctions F G)
    (q : RationalGroupPoints F M) (g : AdelicGroupPoints F G) :
    𝓕.constantTerm J (evaluate F G f) (ι (rational F M q) * g) =
      𝓕.constantTerm J (evaluate F G f) g := by
  let U := SubgroupFunctor.range j
  let P := SubgroupFunctor.range (𝓕.p J)
  have hUP : U.IsNormalizedBy P := by
    intro X y x hy hx
    change y ∈ (SubgroupFunctor.range (𝓕.p J)).carrier X at hy
    change x ∈ (SubgroupFunctor.range j).carrier X at hx
    change y * x * y⁻¹ ∈ (SubgroupFunctor.range j).carrier X
    rw [(𝓕.isCompatible J).parabolic_eq] at hy
    rw [𝓕.range_radical_eq_standardUnipotent J] at hx ⊢
    exact StandardLeviIntersection.conj_mem_standardUnipotent 𝓕.i 𝓕.ν hy hx
  let q' : AdelicSubgroupPoints.rationalPoints F G P :=
    ⟨(𝓕.M J).affinePointsTarget (𝓕.l J ≫ 𝓕.p J) (CommAlgCat.of F F) q,
      SubgroupFunctor.mem_range.mpr ⟨q ≫ (𝓕.l J).hom.hom, by
        simp only [GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc]⟩⟩
  have hq : rational F G q'.val = ι (rational F M q) :=
    DFunLike.congr_fun (AdelicGroupPoints.rational_naturality F M (𝓕.l J ≫ 𝓕.p J)) q
  let := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let := 𝓕.compactSpace_radicalRationalQuotient J
  change AdelicGroupPoints.subgroupConstantTerm F j (evaluate F G f) _ =
    AdelicGroupPoints.subgroupConstantTerm F j (evaluate F G f) g
  rw [← AdelicSubgroupPoints.normalizedConstantTerm_range_eq_subgroupConstantTerm F G j f,
    ← AdelicSubgroupPoints.normalizedConstantTerm_range_eq_subgroupConstantTerm F G j f, ← hq]
  exact AdelicSubgroupPoints.normalizedConstantTerm_rationalNormalizer_mul F G U hUP q' f g

variable (ψ : AdelicGroupPoints F (𝓕.M J) → ℂ)
  (hψ : IsLeftInvariantUnder F (𝓕.M J) (rationalSubgroup F (𝓕.M J)) ψ)
  (g : AdelicGroupPoints F G)

include hψ in
/-- The integrand of the Levi pairing with a constant term can be evaluated on any
representative of a norm-one Levi class. -/
theorem leviPairingIntegrand_constantTerm_eq (f : ContinuousRationalFunctions F G)
    {q : NormOneRationalQuotient F M} {x : normOneSubgroup F M}
    (hx : LeftCosetSpace.mk Γ x = q) :
    𝓕.leviPairingIntegrand J (𝓕.constantTerm J (evaluate F G f)) g ψ q =
      𝓕.constantTerm J (evaluate F G f) (ι x.val * g) * starRingEnd ℂ (ψ x.val) := by
  let b (y : normOneSubgroup F M) :=
    𝓕.constantTerm J (evaluate F G f) (ι y.val * g) * starRingEnd ℂ (ψ y.val)
  have hb (a : Γ) (y : normOneSubgroup F M) : b (a.val * y) = b y := by
    obtain ⟨r, hr⟩ := a.property
    have hr' : rational F M r = a.val.val := congrArg Subtype.val hr
    change 𝓕.constantTerm J (evaluate F G f) (ι (a.val.val * y.val) * g) *
      starRingEnd ℂ (ψ (a.val.val * y.val)) = _
    rw [map_mul, mul_assoc, ← hr', 𝓕.constantTerm_leviRational_mul J,
      hψ (rational F M r) ⟨r, rfl⟩ y.val]
  let B := LeftCosetSpace.lift Γ b hb
  change b (Quotient.out q) = b x
  calc
    b (Quotient.out q) = B q := congrArg B (Quotient.out_eq q)
    _ = b x := congrArg B hx.symm

include hψ in
/-- For a continuous principal-invariant test, pairing with a constant term gives
an integrand continuous on the actual norm-one quotient. -/
theorem continuous_leviPairingIntegrand_constantTerm
    (hψc : Continuous ψ) (f : ContinuousRationalFunctions F G) :
    Continuous (𝓕.leviPairingIntegrand J (𝓕.constantTerm J (evaluate F G f)) g ψ) := by
  rw [LeftCosetSpace.continuous_iff Γ]
  have heq : 𝓕.leviPairingIntegrand J (𝓕.constantTerm J (evaluate F G f)) g ψ ∘
      LeftCosetSpace.mk Γ = fun x : normOneSubgroup F M =>
        𝓕.constantTerm J (evaluate F G f) (ι x.val * g) * starRingEnd ℂ (ψ x.val) :=
    funext fun _ => 𝓕.leviPairingIntegrand_constantTerm_eq J ψ hψ g f rfl
  rw [heq]
  exact ((𝓕.continuous_constantTerm J f).comp
    (((ι).continuous.comp continuous_subtype_val).mul_const g)).mul
    (hψc.comp continuous_subtype_val).star

variable {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
  (hrho : IsClosedSubgroup rho) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth) (R : ℝ)
  (L : Subgroup (FiniteAdelicGroupPoints F G))

local notation "𝔉" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "value" => UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L
local notation "D₁" => weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L 1
local notation "S" => RepresentationGrowth.adelicSourceNorm F G rho

/-- The test times the ambient growth weight has an integrable majorant. The
weight can be checked at a convenient representative of each norm-one class. -/
def HasLeviPairingMajorant : Prop :=
  ∃ b : NormOneRationalQuotient F M → ℝ, Integrable b μ ∧
    ∀ᵐ q ∂μ, ∃ x : normOneSubgroup F M, LeftCosetSpace.mk Γ x = q ∧
      S (ι x.val * g) ^ R * ‖ψ x.val‖ ≤ b q

variable (hψc : Continuous ψ) (hbound : 𝓕.HasLeviPairingMajorant J ψ g rho R)

include hψ hψc hbound in
/-- The paired integrands are integrable, and one constant bounds all pairings on
the growth stage by the order-zero weighted derivative seminorm. -/
theorem exists_leviPairing_constantTerm_bound :
    ∃ C : ℝ, ∀ v : 𝔉,
      Integrable (𝓕.leviPairingIntegrand J (𝓕.constantTerm J (value v)) g ψ) μ ∧
      ‖𝓕.leviPairing J (𝓕.constantTerm J (value v)) g ψ‖ ≤ C * ‖D₁ v‖ := by
  let := 𝓕.compactSpace_radicalRationalQuotient J
  obtain ⟨C, hC⟩ := exists_norm_subgroupConstantTerm_le F G rho hN hrho hsmooth hcalc R L j
  obtain ⟨b, hb, hdom⟩ := hbound
  refine ⟨max C 0 * (∫ q, b q ∂μ), fun v => ?_⟩
  let f := uniformGrowthToContinuousRational F G rho hN hrho hsmooth hcalc R L v
  let A := max C 0 * ‖D₁ v‖
  have hA : 0 ≤ A := mul_nonneg (le_max_right _ _) (norm_nonneg _)
  have hI : Integrable (fun q => A * b q) μ := hb.const_mul A
  have hle : ∀ᵐ q ∂μ, ‖𝓕.leviPairingIntegrand J (𝓕.constantTerm J (value v)) g ψ q‖ ≤
      A * b q := by
    filter_upwards [hdom] with q hq
    obtain ⟨x, hx, hxb⟩ := hq
    change ‖𝓕.leviPairingIntegrand J (𝓕.constantTerm J (evaluate F G f)) g ψ q‖ ≤ _
    rw [𝓕.leviPairingIntegrand_constantTerm_eq J ψ hψ g f hx, norm_mul]
    simp only [Complex.norm_conj]
    let y := ι x.val * g
    have hweight : 0 ≤ S y ^ R :=
      Real.rpow_nonneg (RepresentationGrowth.adelicSourceNorm_pos F G rho hN y).le _
    have hCy : ‖𝓕.constantTerm J (value v) y‖ ≤ A * S y ^ R :=
      (hC v y).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _)) hweight)
    change ‖𝓕.constantTerm J (value v) y‖ * ‖ψ x.val‖ ≤ _
    calc
      _ ≤ (A * S y ^ R) * ‖ψ x.val‖ := mul_le_mul_of_nonneg_right hCy (norm_nonneg _)
      _ = A * (S y ^ R * ‖ψ x.val‖) := mul_assoc _ _ _
      _ ≤ A * b q := mul_le_mul_of_nonneg_left hxb hA
  have hc := 𝓕.continuous_leviPairingIntegrand_constantTerm J ψ hψ g hψc f
  refine ⟨hI.mono' hc.aestronglyMeasurable hle, ?_⟩
  refine (norm_integral_le_of_norm_le hI hle).trans_eq ?_
  rw [integral_const_mul]
  simp only [A, mul_right_comm]

/-- Pair the standard unipotent constant term with a fixed continuous rational-invariant
Levi test admitting an integrable weighted majorant. The result is a continuous linear
form on the ambient uniform-growth space. -/
def constantTermLeviPairingCLM : 𝔉 →L[ℂ] ℂ := by
  let bound := 𝓕.exists_leviPairing_constantTerm_bound J ψ hψ g rho hN hrho hsmooth hcalc
    R L hψc hbound
  let C := Classical.choose bound
  have hC := Classical.choose_spec bound
  let t (q : NormOneRationalQuotient F M) : 𝔉 →L[ℂ] ℂ :=
    letI := 𝓕.compactSpace_radicalRationalQuotient J
    (starRingEnd ℂ (ψ ((Quotient.out q : normOneSubgroup F M) : AdelicGroupPoints F M))) •
      subgroupConstantTermEvalCLM F G rho hN hrho hsmooth hcalc R L j
        (ι ((Quotient.out q : normOneSubgroup F M) : AdelicGroupPoints F M) * g)
  have ht (v : 𝔉) : (fun q => t q v) =
      𝓕.leviPairingIntegrand J (𝓕.constantTerm J (value v)) g ψ := by
    funext q
    simp only [t, leviPairingIntegrand, constantTerm, smul_apply,
      subgroupConstantTermEvalCLM_apply, smul_eq_mul, mul_comm]
  have hi (v : 𝔉) : Integrable (fun q => t q v) μ := by
    rw [ht]
    exact (hC v).1
  let T : 𝔉 →ₗ[ℂ] ℂ :=
    { toFun := fun v => 𝓕.leviPairing J (𝓕.constantTerm J (value v)) g ψ
      map_add' := fun v w => by
        unfold leviPairing
        rw [← ht (v + w), ← ht v, ← ht w]
        simp only [map_add]
        exact integral_add (hi v) (hi w)
      map_smul' := fun c v => by
        unfold leviPairing
        rw [← ht (c • v), ← ht v]
        simp only [map_smul, RingHom.id_apply, integral_smul] }
  refine ⟨T, ?_⟩
  apply continuous_of_tendsto_nhds_zero T
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (fun v => (hC v).2) ?_
  have hc : Continuous (fun v : 𝔉 => C * ‖D₁ v‖) := continuous_const.mul (D₁).continuous.norm
  simpa only [map_zero, norm_zero, mul_zero] using (hc.continuousAt (x := (0 : 𝔉))).tendsto

@[simp]
theorem constantTermLeviPairingCLM_apply (v : 𝔉) :
    𝓕.constantTermLeviPairingCLM J ψ hψ g rho hN hrho hsmooth hcalc R L hψc hbound v =
      𝓕.leviPairing J (𝓕.constantTerm J (value v)) g ψ := rfl

end Langlands.Global.StandardParabolicFamily

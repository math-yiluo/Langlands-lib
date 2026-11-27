import Langlands.Global.AdelicLeadingCuspidalInjectivityReduction
import Langlands.Global.AdelicCuspidalProjectionExistenceReductionStatement
import Langlands.Global.AdelicStandardConstantTerm
import Langlands.Global.AdelicModerateCuspidalSmoothing
import Langlands.Global.AdelicRightConvolutionEnveloping
import Langlands.Global.AdelicFiniteVolumeProof
import Langlands.Global.AdelicLocalFinitenessSolutionAutomorphy
import Langlands.Global.AdelicRepresentationHeightPropernessProof
import Langlands.Automorphic.JointAdmissibilityCenter

/-! # Automorphic cuspidal projections from continuous ones -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open AdelicSubgroupPoints

section Period

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine U.X.left]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]

local notation "A" => AdelicGroupPoints F G
local notation "dg" => (Measure.haar : Measure (AdelicGroupPoints F G))
local notation "V" => SubgroupFunctor.range j
local notation "Uₐ" => adelicPoints F G V
local notation "Γ" => AdelicSubgroupPoints.rationalSubgroup F G V
local notation "Qt" => AdelicSubgroupPoints.RationalQuotient F G V
local notation "du" => normalizedRationalQuotientHaarMeasure F G V

/-- A continuous compact right convolution commutes with a compact radical average on a
continuous function invariant under the rational points of the radical. -/
theorem subgroupConstantTerm_rightConvolution_apply_of_rationalImage [CompactSpace Qt]
    {h f : A → ℂ} (hh : Continuous h) (hSupp : HasCompactSupport h) (hf : Continuous f)
    (hInv : ∀ x ∈ rationalImage F j, ∀ g : A, f (x * g) = f g) (g : A) :
    subgroupConstantTerm F j (rightConvolution F G h f) g =
      rightConvolution F G h (subgroupConstantTerm F j f) g := by
  let : IsClosed (Uₐ : Set A) := isClosed_adelicPoints_range F G j
  let : BorelSpace Qt := AdelicSubgroupPoints.rationalQuotientBorelSpace F G V
  let : IsProbabilityMeasure du := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  let fU (a : A) : Qt → ℂ := LeftCosetSpace.lift Γ (fun u : Uₐ => f (u.val * (g * a))) (fun r u => by
    change f ((r.val.val * u.val) * (g * a)) = f (u.val * (g * a))
    rw [mul_assoc]
    exact hInv _ ((mem_rationalSubgroup_range_iff j r.val).mp r.2) _)
  let φ (q : Qt) (a : A) : ℂ := h a * fU a q
  have hcont : Continuous (Function.uncurry φ) := by
    rw [← ((LeftCosetSpace.isOpenQuotientMap_mk Γ).prodMap IsOpenQuotientMap.id).continuous_comp_iff]
    change Continuous (fun p : Uₐ × A => h p.2 * f (p.1.val * (g * p.2)))
    exact (hh.comp continuous_snd).mul
      (hf.comp ((continuous_subtype_val.comp continuous_fst).mul (continuous_const.mul continuous_snd)))
  have hcs : HasCompactSupport (Function.uncurry φ) := by
    apply (isCompact_univ.prod hSupp).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_univ.prod (isClosed_tsupport h))
    rintro ⟨q, a⟩ ha
    refine ⟨Set.mem_univ _, ?_⟩
    by_contra han
    exact ha (by change h a * fU a q = 0; rw [image_eq_zero_of_notMem_tsupport han, zero_mul])
  have hφ (q : Qt) (a : A) : φ q a = h a * f ((Quotient.out q : Uₐ).val * (g * a)) :=
    (congrArg (fun x => h a * fU a x) (Quotient.out_eq q)).symm
  calc
    subgroupConstantTerm F j (rightConvolution F G h f) g = ∫ q : Qt, (∫ a, φ q a ∂dg) ∂du := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun q => ?_
      change (∫ a, h a * f (((Quotient.out q : Uₐ).val * g) * a) ∂dg) = _
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun a => by simp only [hφ, mul_assoc]
    _ = ∫ a, (∫ q : Qt, φ q a ∂du) ∂dg := integral_integral_swap_of_hasCompactSupport hcont hcs
    _ = rightConvolution F G h (subgroupConstantTerm F j f) g := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun a => ?_
      change (∫ q : Qt, φ q a ∂du) = h a * (∫ q : Qt, f ((Quotient.out q : Uₐ).val * (g * a)) ∂du)
      simp_rw [hφ, integral_const_mul]

end Period

section Regularity

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G

omit [LocallyOfFiniteType G.X.hom] in
/-- Finiteness of the span of the left `K_∞`-translates of a kernel is right `K_∞`-finiteness of
the kernel composed with inversion. -/
theorem isInfiniteSubgroupFiniteFunction_inv_of_leftFinite
    (K : Subgroup (InfiniteAdelicGroupPoints F G)) {α : A → ℂ}
    (hα : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K =>
      fun h : A => α (ofInfinite F G k * h)))) :
    IsInfiniteSubgroupFiniteFunction F G K (fun g => α g⁻¹) := by
  let inv : (A → ℂ) →ₗ[ℂ] (A → ℂ) := LinearMap.funLeft ℂ ℂ (fun g : A => g⁻¹)
  change FiniteDimensional ℂ (Submodule.span ℂ _)
  have hle : Submodule.span ℂ (Set.range fun k : K =>
      fun g : A => (fun g => α g⁻¹) (g * ofInfinite F G k)) ≤
      (Submodule.span ℂ (Set.range fun k : K => fun h : A => α (ofInfinite F G k * h))).map inv := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    refine ⟨fun h => α (ofInfinite F G (k⁻¹ : K) * h), ⟨k⁻¹, rfl⟩, ?_⟩
    funext g
    simp [inv, LinearMap.funLeft_apply, mul_inv_rev, map_inv]
  exact Submodule.finiteDimensional_of_le hle

variable {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

/-- Centre finiteness of a right convolution `ψ₀ * α` whose kernel reproduces a centre-finite
function `φ`, when every kernel that annihilates `φ` by right convolution annihilates `ψ₀`. -/
theorem isCenterFiniteFunction_rightConvolution_of_reproducing
    {φ ψ₀ α : A → ℂ} (hα : IsAdelicTestFunction F G α)
    (hφc : Continuous φ) (hψc : Continuous ψ₀) (hrep : rightConvolution F G α φ = φ)
    (hcen : IsCenterFiniteFunction F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth) φ)
    (huniq : ∀ k : A → ℂ, IsAdelicTestFunction F G k →
      rightConvolution F G k φ = 0 → rightConvolution F G k ψ₀ = 0) :
    IsCenterFiniteFunction F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
      (rightConvolution F G α ψ₀) := by
  obtain ⟨J, hJfin, hJ⟩ := hcen
  refine ⟨J, hJfin, fun z hz b hslice => ?_⟩
  obtain ⟨k, hk, -, hkspec⟩ := adelicRightConvolutionEnveloping hsmooth
    (adelicDifferentialCommutator_of_smooth F G hsmooth) (z : AdelicEnvelopingAlgebra F G hsmooth) α hα
  have hφk : rightConvolution F G k φ = 0 := by
    funext x
    rw [← pair_projections F G x]
    have hspec := hkspec φ hφc.measurable hφc.locallyIntegrable (finite F G x)
    have hfun : (fun a => rightConvolution F G α φ (pair F G a (finite F G x))) =
        functionInfiniteSlice F G φ (finite F G x) :=
      funext fun a => congrFun hrep _
    have hmem : functionInfiniteSlice F G φ (finite F G x) ∈ InfinitePlotSmoothFunctions F G := by
      rw [← hfun]
      exact (rightConvolutionSmoothSlice hsmooth α φ hα hφc.measurable hφc.locallyIntegrable
        (finite F G x)).property
    have hsl : rightConvolutionSmoothSlice hsmooth α φ hα hφc.measurable hφc.locallyIntegrable
        (finite F G x) = ⟨functionInfiniteSlice F G φ (finite F G x), hmem⟩ := Subtype.ext hfun
    rw [hsl] at hspec
    have h0 := hJ z hz (finite F G x) hmem
    change InfiniteAdelicGroupPoints.plotSmoothEnvelopingAction F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
      (z : AdelicEnvelopingAlgebra F G hsmooth) _ = 0 at h0
    rw [h0] at hspec
    have := congrArg (fun v : InfinitePlotSmoothFunctions F G =>
      (v : InfiniteAdelicGroupPoints F G → ℂ) (infinite F G x)) hspec
    exact this.symm
  have hψk := huniq k hk hφk
  have hspec := hkspec ψ₀ hψc.measurable hψc.locallyIntegrable b
  have hsl : rightConvolutionSmoothSlice hsmooth α ψ₀ hα hψc.measurable hψc.locallyIntegrable b =
      ⟨functionInfiniteSlice F G (rightConvolution F G α ψ₀) b, hslice⟩ := Subtype.ext rfl
  rw [hsl] at hspec
  change InfiniteAdelicGroupPoints.plotSmoothEnvelopingAction F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
    (z : AdelicEnvelopingAlgebra F G hsmooth) _ = 0
  rw [hspec]
  apply Subtype.ext
  funext a
  change rightConvolution F G k ψ₀ (pair F G a b) = 0
  rw [hψk]
  rfl

end Regularity

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Index" => StandardIndex F G fam.i fam.ν
local notation "A" => AdelicGroupPoints F G
local notation "dg" => (Measure.haar : Measure (AdelicGroupPoints F G))

/-- The scalar relating the adelic height of a matrix embedding of size `N` to its source norm. -/
def heightScale (F : Type u) [Field F] [NumberField F] (N : ℕ) : ℝ :=
  (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)

section Pairing

variable (Q : StandardIndex F G fam.i fam.ν)

local notation "M" => fam.M Q
local notation "ι" => AdelicGroupPoints.map F (fam.M Q) G (fam.l Q ≫ fam.p Q)
local notation "Γ" => rationalNormOneSubgroup F (fam.M Q)
local notation "μ" => normOneRationalQuotientHaarMeasure F (fam.M Q)

/-- Left invariance under `U_Q(𝔸) M_Q(F)` gives left invariance under the rational Levi. -/
theorem leviRational_mul_of_parabolicInvariant {f : A → ℂ}
    (hf : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p Q) (fam.iU Q) (fam.l Q)) f)
    (r : RationalGroupPoints F M) (x : A) :
    f (ι (rational F M r) * x) = f x :=
  hf _ (Subgroup.mem_sup_right ⟨r, rfl⟩) x

/-- The Levi pairing integrand of a rational-Levi-invariant function can be evaluated at any
representative. -/
theorem leviPairingIntegrand_mk {f : A → ℂ}
    (hf : ∀ (r : RationalGroupPoints F M) (x : A), f (ι (rational F M r) * x) = f x)
    {t : AdelicGroupPoints F M → ℂ}
    (ht : IsLeftInvariantUnder F M (rationalSubgroup F M) t)
    (g : A) (m : normOneSubgroup F M) :
    fam.leviPairingIntegrand Q f g t (LeftCosetSpace.mk Γ m) =
      f (ι m.val * g) * starRingEnd ℂ (t m.val) := by
  let b (y : normOneSubgroup F M) := f (ι y.val * g) * starRingEnd ℂ (t y.val)
  have hb (a : Γ) (y : normOneSubgroup F M) : b (a.val * y) = b y := by
    obtain ⟨r, hr⟩ := a.property
    have hr' : rational F M r = a.val.val := congrArg Subtype.val hr
    change f (ι (a.val.val * y.val) * g) * starRingEnd ℂ (t (a.val.val * y.val)) = _
    rw [map_mul, mul_assoc, ← hr', hf, ht (rational F M r) ⟨r, rfl⟩ y.val]
  let B := LeftCosetSpace.lift Γ b hb
  change b (Quotient.out (LeftCosetSpace.mk Γ m)) = b m
  calc
    b (Quotient.out (LeftCosetSpace.mk Γ m)) = B (LeftCosetSpace.mk Γ m) :=
      congrArg B (Quotient.out_eq (LeftCosetSpace.mk Γ m))
    _ = b m := rfl

/-- The Levi pairing integrand, as a function of the class and of a right translation
parameter, is continuous. -/
theorem continuous_leviPairingIntegrand_uncurry {f : A → ℂ} (hfc : Continuous f)
    (hf : ∀ (r : RationalGroupPoints F M) (x : A), f (ι (rational F M r) * x) = f x)
    {t : AdelicGroupPoints F M → ℂ} (htc : Continuous t)
    (ht : IsLeftInvariantUnder F M (rationalSubgroup F M) t) (g : A) :
    Continuous (fun p : NormOneRationalQuotient F M × A =>
      fam.leviPairingIntegrand Q f (g * p.2) t p.1) := by
  rw [← ((LeftCosetSpace.isOpenQuotientMap_mk Γ).prodMap IsOpenQuotientMap.id).continuous_comp_iff]
  have heq : ((fun p : NormOneRationalQuotient F M × A =>
      fam.leviPairingIntegrand Q f (g * p.2) t p.1) ∘
        Prod.map (LeftCosetSpace.mk Γ) id) =
      fun p : normOneSubgroup F M × A =>
        f (ι p.1.val * (g * p.2)) * starRingEnd ℂ (t p.1.val) := by
    funext p
    exact fam.leviPairingIntegrand_mk Q hf ht (g * p.2) p.1
  rw [heq]
  exact (hfc.comp (((ι).continuous.comp (continuous_subtype_val.comp continuous_fst)).mul
    (continuous_const.mul continuous_snd))).mul
    (Complex.continuous_conj.comp (htc.comp (continuous_subtype_val.comp continuous_fst)))

/-- The Levi pairing integrand of a continuous rational-Levi-invariant function is continuous. -/
theorem continuous_leviPairingIntegrand {f : A → ℂ} (hfc : Continuous f)
    (hf : ∀ (r : RationalGroupPoints F M) (x : A), f (ι (rational F M r) * x) = f x)
    {t : AdelicGroupPoints F M → ℂ} (htc : Continuous t)
    (ht : IsLeftInvariantUnder F M (rationalSubgroup F M) t) (g : A) :
    Continuous (fam.leviPairingIntegrand Q f g t) := by
  have h := (fam.continuous_leviPairingIntegrand_uncurry Q hfc hf htc ht g).comp
    (continuous_id.prodMk (continuous_const : Continuous fun _ : NormOneRationalQuotient F M =>
      (1 : A)))
  simpa only [Function.comp_def, mul_one, id_eq] using h

variable {N : ℕ} (rho : MatrixRepresentation G (Fin N))

theorem heightScale_nonneg : 0 ≤ heightScale F N := by
  unfold heightScale; positivity

local notation "H" => RepresentationGrowth.adelicHeight F G rho
local notation "S" => RepresentationGrowth.adelicSourceNorm F G rho
local notation "sc" => heightScale F N

/-- The integrand of a right translate is bounded by a power of the height of the translation
times the weighted test of `HasLeviPairingMajorant`. -/
theorem norm_leviPairingIntegrand_mk_le (hN : 0 < N) {f : A → ℂ}
    (hf : ∀ (r : RationalGroupPoints F M) (x : A), f (ι (rational F M r) * x) = f x)
    {t : AdelicGroupPoints F M → ℂ}
    (ht : IsLeftInvariantUnder F M (rationalSubgroup F M) t)
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (hgrowth : ∀ x, ‖f x‖ ≤ C * H x ^ r)
    (g y : A) (x : normOneSubgroup F M) :
    ‖fam.leviPairingIntegrand Q f (g * y) t (LeftCosetSpace.mk Γ x)‖ ≤
      C * sc ^ r * (H y ^ r * (S (ι x.val * g) ^ r * ‖t x.val‖)) := by
  have hs : (0 : ℝ) ≤ sc := heightScale_nonneg
  have hH (z : A) : 0 ≤ H z := zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN z)
  have hS (z : A) : 0 ≤ S z := (RepresentationGrowth.adelicSourceNorm_pos F G rho hN z).le
  rw [fam.leviPairingIntegrand_mk Q hf ht, norm_mul, Complex.norm_conj]
  have h1 : H (ι x.val * (g * y)) ^ r ≤ H (ι x.val * g) ^ r * H y ^ r := by
    rw [← mul_assoc, ← Real.mul_rpow (hH _) (hH _)]
    exact Real.rpow_le_rpow (hH _) (RepresentationGrowth.adelicHeight_mul_le F G rho hN _ _) hr
  have h2 : H (ι x.val * g) ^ r = sc ^ r * S (ι x.val * g) ^ r := by
    rw [RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm]
    exact Real.mul_rpow hs (hS _)
  calc
    ‖f (ι x.val * (g * y))‖ * ‖t x.val‖ ≤ (C * H (ι x.val * (g * y)) ^ r) * ‖t x.val‖ :=
      mul_le_mul_of_nonneg_right (hgrowth _) (norm_nonneg _)
    _ ≤ (C * (H (ι x.val * g) ^ r * H y ^ r)) * ‖t x.val‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC) (norm_nonneg _)
    _ = C * sc ^ r * (H y ^ r * (S (ι x.val * g) ^ r * ‖t x.val‖)) := by
      rw [h2]; ring

/-- Integrability of the Levi pairing integrand from a weighted majorant of the test. -/
theorem integrable_leviPairingIntegrand_of_majorant (hN : 0 < N) {f : A → ℂ} (hfc : Continuous f)
    (hf : ∀ (r : RationalGroupPoints F M) (x : A), f (ι (rational F M r) * x) = f x)
    {t : AdelicGroupPoints F M → ℂ} (htc : Continuous t)
    (ht : IsLeftInvariantUnder F M (rationalSubgroup F M) t)
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (hgrowth : ∀ x, ‖f x‖ ≤ C * H x ^ r)
    (g : A) (hmaj : fam.HasLeviPairingMajorant Q t g rho r) :
    Integrable (fam.leviPairingIntegrand Q f g t) μ := by
  obtain ⟨b, hb, hbound⟩ := hmaj
  refine (hb.const_mul (C * sc ^ r * H 1 ^ r)).mono'
    (fam.continuous_leviPairingIntegrand Q hfc hf htc ht g).aestronglyMeasurable ?_
  filter_upwards [hbound] with q hq
  obtain ⟨x, hx, hxb⟩ := hq
  have hH1 : 0 ≤ H 1 ^ r := Real.rpow_nonneg
    (zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN 1)) _
  have hCs : 0 ≤ C * sc ^ r := mul_nonneg hC (Real.rpow_nonneg heightScale_nonneg _)
  have := fam.norm_leviPairingIntegrand_mk_le Q rho hN hf ht hC hr hgrowth g 1 x
  rw [mul_one, hx] at this
  calc
    ‖fam.leviPairingIntegrand Q f g t q‖ ≤
        C * sc ^ r * (H 1 ^ r * (S (ι x.val * g) ^ r * ‖t x.val‖)) := this
    _ ≤ C * sc ^ r * (H 1 ^ r * b q) := by gcongr
    _ = C * sc ^ r * H 1 ^ r * b q := by ring

/-- Fubini's theorem for the Levi pairing of a compactly supported right convolution. -/
theorem leviPairing_rightConvolution (hN : 0 < N) {f : A → ℂ} (hfc : Continuous f)
    (hf : ∀ (r : RationalGroupPoints F M) (x : A), f (ι (rational F M r) * x) = f x)
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (hgrowth : ∀ x, ‖f x‖ ≤ C * H x ^ r)
    {h : A → ℂ} (hhc : Continuous h) (hhs : HasCompactSupport h)
    {t : AdelicGroupPoints F M → ℂ} (htc : Continuous t)
    (ht : IsLeftInvariantUnder F M (rationalSubgroup F M) t)
    (g : A) (hmaj : fam.HasLeviPairingMajorant Q t g rho r) :
    Integrable (fam.leviPairingIntegrand Q (rightConvolution F G h f) g t) μ ∧
      fam.leviPairing Q (rightConvolution F G h f) g t =
        ∫ y, h y * fam.leviPairing Q f (g * y) t ∂dg := by
  have : IsFiniteMeasure μ :=
    connectedReductiveFiniteVolume F M (fam.isCompatible Q).levi.isConnectedReductive
  let Φ : NormOneRationalQuotient F M × A → ℂ := fun p =>
    h p.2 * fam.leviPairingIntegrand Q f (g * p.2) t p.1
  have hΦc : Continuous Φ :=
    (hhc.comp continuous_snd).mul (fam.continuous_leviPairingIntegrand_uncurry Q hfc hf htc ht g)
  obtain ⟨b, hb, hbound⟩ := hmaj
  let w : A → ℝ := fun y => ‖h y‖ * H y ^ r
  have hw : Integrable w dg :=
    (hhc.norm.mul ((RepresentationGrowth.continuous_adelicHeight F G rho hN).rpow_const
      (fun _ => Or.inr hr))).integrable_of_hasCompactSupport hhs.norm.mul_right
  have hΦi : Integrable Φ ((μ).prod dg) := by
    refine ((hb.mul_prod hw).const_mul (C * sc ^ r)).mono' hΦc.aestronglyMeasurable ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hbound] with p hp
    obtain ⟨x, hx, hxb⟩ := hp
    have hCs : 0 ≤ C * sc ^ r := mul_nonneg hC (Real.rpow_nonneg heightScale_nonneg _)
    have hnorm := fam.norm_leviPairingIntegrand_mk_le Q rho hN hf ht hC hr hgrowth g p.2 x
    rw [hx] at hnorm
    have hHy : 0 ≤ H p.2 ^ r := Real.rpow_nonneg
      (zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN _)) _
    calc
      ‖Φ p‖ = ‖h p.2‖ * ‖fam.leviPairingIntegrand Q f (g * p.2) t p.1‖ := norm_mul _ _
      _ ≤ ‖h p.2‖ * (C * sc ^ r * (H p.2 ^ r * (S (ι x.val * g) ^ r * ‖t x.val‖))) :=
        mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ ≤ ‖h p.2‖ * (C * sc ^ r * (H p.2 ^ r * b p.1)) := by gcongr
      _ = C * sc ^ r * (b p.1 * w p.2) := by simp only [w]; ring
  have hint : fam.leviPairingIntegrand Q (rightConvolution F G h f) g t =
      fun q => ∫ y, Φ (q, y) ∂dg := by
    funext q
    change (∫ y, h y * f (ι ((Quotient.out q : normOneSubgroup F M) : AdelicGroupPoints F M) *
        g * y) ∂dg) * starRingEnd ℂ (t ((Quotient.out q : normOneSubgroup F M) :
          AdelicGroupPoints F M)) = _
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Φ, leviPairingIntegrand, mul_assoc]
  refine ⟨hint ▸ hΦi.integral_prod_left, ?_⟩
  unfold leviPairing
  rw [hint]
  rw [integral_integral_swap (f := fun q y => Φ (q, y)) hΦi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Φ]
  rw [integral_const_mul]

end Pairing

section Cuspidality

/-- The rational points of a smaller standard radical lie in `U_P(𝔸) M_P(F)`. -/
theorem rationalRadicalImage_le_parabolicQuotient {P R : Index} (hRP : R ≤ P) :
    rationalImage F (fam.iU R ≫ fam.p R) ≤
      parabolicQuotientSubgroup F (fam.p P) (fam.iU P) (fam.l P) := by
  have hle : SubgroupFunctor.range (fam.iU R ≫ fam.p R) ≤ SubgroupFunctor.range (fam.p P) :=
    (SubgroupFunctor.range_comp_le _ _).trans ((fam.le_iff_range_le R P).mp hRP)
  let : IsClosedImmersion (fam.p P).hom.hom.left := (fam.isCompatible P).parabolic.isClosedSubgroup
  have hcomp := SubgroupFunctor.rangeFactor_comp (fam.iU R ≫ fam.p R) (fam.p P) hle
  rw [← hcomp]
  exact (rationalImage_comp_le _ _).trans (rationalImage_le_parabolicQuotientSubgroup _ _ _
    (fam.isCompatible P).levi (fam.isUnipotentRadical P))

/-- Compact right convolution preserves cuspidality along a standard parabolic. -/
theorem isCuspidalAlong_rightConvolution (P : Index) {h f : A → ℂ} (hh : Continuous h)
    (hSupp : HasCompactSupport h) (hf : Continuous f)
    (hinv : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p P) (fam.iU P) (fam.l P)) f)
    (hcusp : fam.IsCuspidalAlong P f) :
    fam.IsCuspidalAlong P (rightConvolution F G h f) := by
  intro R hRP
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G
      (SubgroupFunctor.range (fam.iU R ≫ fam.p R))) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (fam.iU R ≫ fam.p R)
      (fam.isUnipotentRadical R).1.smooth (fam.isUnipotentRadical R).1.connectedSpace
        (fam.isUnipotentRadical R).1.isUnipotent
  funext g
  change subgroupConstantTerm F (fam.iU R ≫ fam.p R) (rightConvolution F G h f) g = 0
  rw [subgroupConstantTerm_rightConvolution_apply_of_rationalImage (fam.iU R ≫ fam.p R) hh hSupp hf
    (fun x hx g => hinv x (fam.rationalRadicalImage_le_parabolicQuotient hRP.le hx) g)]
  change rightConvolution F G h (fam.constantTerm R f) g = 0
  rw [hcusp R hRP]
  simp [rightConvolution]

end Cuspidality

section Uniqueness

/-- For a positive-size embedding, the vanishing criterion shows that a continuous cuspidal
function of moderate growth in the fibrewise cuspidal annihilator is zero. -/
theorem eq_zero_of_inCuspidalAnnihilator (hvan : ParabolicCuspidalVanishingStatement.{u})
    {K : Subgroup A} (hK : IsMaximalCompactSubgroup F G K)
    (hKmin : IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K)
    {N : ℕ} {rho : MatrixRepresentation G (Fin N)} (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    {Q : Index} {χ : A → ℂ} (hχ : fam.IsModerateContinuousOnParabolic rho Q χ)
    (hcusp : fam.IsCuspidalAlong Q χ)
    (hann : fam.InCuspidalAnnihilator (K.comap (ofInfinite F G).toMonoidHom) rho Q χ) :
    χ = 0 :=
  hvan F G fam K hK (fam.isIwasawaCompact_of_minimal hKmin) rho hN hrho Q χ hχ (by
    intro R hRQ
    rcases eq_or_lt_of_le hRQ with rfl | hlt
    · rw [fam.constantTerm_eq_self_of_unipotent_invariant R
        (fun x hx => hχ.1 x (Subgroup.mem_sup_left hx))]
      exact hann
    · rw [hcusp R hlt]
      exact (fam.cuspidalAnnihilator _ rho R).zero_mem)

end Uniqueness

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

section RankZero

variable {F : Type u} [Field F] [NumberField F]

/-- On a group with a single adelic point, every left invariant function of moderate growth is
automorphic. -/
theorem isAutomorphicFunctionOn_of_subsingleton
    {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left]
    [Subsingleton (AdelicGroupPoints F H)] {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d H.X.hom) (hcalc : AdelicDifferentialCommutator F H hsmooth)
    (Γ : Subgroup (AdelicGroupPoints F H)) (Kinf : Subgroup (InfiniteAdelicGroupPoints F H))
    {N : ℕ} (rho : MatrixRepresentation H (Fin N)) {φ : AdelicGroupPoints F H → ℂ}
    (hinv : IsLeftInvariantUnder F H Γ φ) (hmod : HasModerateGrowthFunction F H rho φ) :
    IsAutomorphicFunctionOn F H hsmooth hcalc Γ Kinf rho φ := by
  have hinf : Subsingleton (InfiniteAdelicGroupPoints F H) :=
    ⟨fun a b => by
      have := Subsingleton.elim (ofInfinite F H a) (ofInfinite F H b)
      simpa using congrArg (infinite F H) this⟩
  set c : ℂ := φ 1
  have hφ : φ = fun _ => c := funext fun g => by rw [Subsingleton.elim g 1]
  have hslice (b : FiniteAdelicGroupPoints F H) : functionInfiniteSlice F H φ b = fun _ => c := by
    funext a
    exact congrFun hφ _
  refine ⟨hinv, ⟨?_, fun b => ?_, ⟨⊤, isOpen_univ, fun l _ g => by rw [hφ]⟩⟩, ?_, ?_, hmod⟩
  · rw [hφ]; exact continuous_const
  · rw [hslice]; exact fun E _ _ M _ _ p hp => contMDiff_const
  · apply FiniteDimensional.span_of_finite
    exact (Set.finite_singleton (fun _ : AdelicGroupPoints F H => c)).subset
      (by rintro _ ⟨k, rfl⟩; funext g; exact congrFun hφ _)
  · have : Finite (InfiniteAdelicGroupPoints F H) := Finite.of_subsingleton
    have hW : FiniteDimensional ℂ (InfinitePlotSmoothFunctions F H) :=
      FiniteDimensional.finiteDimensional_submodule (InfinitePlotSmoothFunctions F H)
    let v : InfinitePlotSmoothFunctions F H := ⟨fun _ => c, fun E _ _ M _ _ p hp => contMDiff_const⟩
    obtain ⟨I, hI, hann⟩ := exists_cofiniteIdeal_annihilates_of_finite_centralOrbit
      (InfiniteAdelicGroupPoints.plotSmoothCenterAction F H hsmooth hcalc) v
      (FiniteDimensional.finiteDimensional_submodule _)
    refine ⟨I, hI, fun z hz b h => ?_⟩
    have hv : (⟨functionInfiniteSlice F H φ b, h⟩ : InfinitePlotSmoothFunctions F H) = v :=
      Subtype.ext (hslice b)
    rw [hv]
    exact hann z hz

end RankZero

/-- Weighted majorants of Levi cusp forms, the parabolic cuspidal vanishing criterion,
Harish-Chandra's reproducing kernel and continuous cuspidal projections give automorphic
cuspidal projections. -/
theorem cuspidalProjectionExistenceReduction :
    CuspidalProjectionExistenceReductionStatement.{u} := by
  intro hmaj hvan hrep hcont F _ _ G _ _ _ fam K hK hKmin hKlevi N d rho hsmooth hrho Kinf Q φ hφ
  obtain ⟨ψ₀, hψ₀, hψ₀cusp, hψ₀pair⟩ :=
    hcont F G fam K hK hKmin hKlevi rho hsmooth hrho Q φ hφ
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : Subsingleton (AdelicGroupPoints F G) :=
      ⟨fun _ _ => (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective
        (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩
    exact ⟨ψ₀, isAutomorphicFunctionOn_of_subsingleton _ _ _ _ rho hψ₀.1 hψ₀.2.2, hψ₀cusp,
      hψ₀pair⟩
  obtain ⟨α, hα, hαfin, hαrep⟩ := hrep F G fam K hK hKmin hKlevi rho hsmooth hrho Q φ hφ
  have hφc : Continuous φ := hφ.2.1.1
  have hψ₀c : Continuous ψ₀ := hψ₀.2.1
  have hφL := fam.leviRational_mul_of_parabolicInvariant Q hφ.1
  have hψ₀L := fam.leviRational_mul_of_parabolicInvariant Q hψ₀.1
  obtain ⟨C, r, hC, hr, hg⟩ := (hasModerateGrowthFunction_iff_hasHeightGrowth hN ψ₀).mp hψ₀.2.2
  obtain ⟨Cφ, rφ, hCφ, hrφ, hgφ⟩ :=
    (hasModerateGrowthFunction_iff_hasHeightGrowth hN φ).mp hφ.2.2.2.2
  -- Fubini compares the pairings of the two convolutions with one kernel.
  have hpair : ∀ k : AdelicGroupPoints F G → ℂ, Continuous k → HasCompactSupport k →
      ∀ t : AdelicGroupPoints F (fam.M Q) → ℂ, fam.IsLeviCuspForm Kinf rho Q t →
      ∀ g : AdelicGroupPoints F G,
        Integrable (fam.leviPairingIntegrand Q (rightConvolution F G k ψ₀) g t)
            (normOneRationalQuotientHaarMeasure F (fam.M Q)) ∧
          fam.leviPairing Q (rightConvolution F G k ψ₀) g t =
            fam.leviPairing Q (rightConvolution F G k φ) g t := by
    intro k hkc hks t ht g
    have htc : Continuous t := ht.1.2.1.1
    have htL := ht.1.1
    obtain ⟨hI, hEq⟩ := fam.leviPairing_rightConvolution Q rho hN hψ₀c hψ₀L hC hr hg hkc hks htc
      htL g (hmaj F G fam K hK hKmin hKlevi rho hrho Q t ht g r)
    obtain ⟨-, hEqφ⟩ := fam.leviPairing_rightConvolution Q rho hN hφc hφL hCφ hrφ hgφ hkc hks htc
      htL g (hmaj F G fam K hK hKmin hKlevi rho hrho Q t ht g rφ)
    refine ⟨hI, ?_⟩
    rw [hEq, hEqφ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change k y * fam.leviPairing Q ψ₀ (g * y) t = k y * fam.leviPairing Q φ (g * y) t
    rw [(hψ₀pair t ht (g * y)).2.2]
  -- Properties of convolutions of the continuous projection.
  have hconv : ∀ k : AdelicGroupPoints F G → ℂ, IsAdelicTestFunction F G k →
      fam.IsModerateContinuousOnParabolic rho Q (rightConvolution F G k ψ₀) ∧
        fam.IsCuspidalAlong Q (rightConvolution F G k ψ₀) := by
    intro k hk
    obtain ⟨C', hC', hb⟩ := norm_rightConvolution_le_of_height_bound rho hN hk.1.1 hk.2.1 hC hr hg
    refine ⟨⟨isLeftInvariantUnder_rightConvolution hψ₀.1,
      (adelicRightConvolutionDifferentiation F G d hsmooth k ψ₀ hk hψ₀c.measurable
        hψ₀c.locallyIntegrable).2.1.1,
      (hasModerateGrowthFunction_iff_hasHeightGrowth hN _).mpr ⟨C', r, hC', hr, hb⟩⟩,
      fam.isCuspidalAlong_rightConvolution Q hk.1.1 hk.2.1 hψ₀c hψ₀.1 hψ₀cusp⟩
  -- Uniqueness: a kernel annihilating `φ` annihilates `ψ₀`.
  have huniq : ∀ k : AdelicGroupPoints F G → ℂ, IsAdelicTestFunction F G k →
      rightConvolution F G k φ = 0 → rightConvolution F G k ψ₀ = 0 := by
    intro k hk hk0
    obtain ⟨hmc, hcu⟩ := hconv k hk
    refine fam.eq_zero_of_inCuspidalAnnihilator hvan hK hKmin hN hrho hmc hcu ?_
    intro t ht g
    obtain ⟨hI, hEq⟩ := hpair k hk.1.1 hk.2.1 t ht g
    refine ⟨hI, ?_⟩
    rw [hEq, hk0]
    simp [StandardParabolicFamily.leviPairing, StandardParabolicFamily.leviPairingIntegrand]
  obtain ⟨hmcα, hcuα⟩ := hconv α hα
  refine ⟨rightConvolution F G α ψ₀, ⟨hmcα.1,
    (adelicRightConvolutionDifferentiation F G d hsmooth α ψ₀ hα hψ₀c.measurable
      hψ₀c.locallyIntegrable).2.1,
    isInfiniteSubgroupFiniteFunction_rightConvolution Kinf hα.1.1 hα.2.1 hψ₀c
      (isInfiniteSubgroupFiniteFunction_inv_of_leftFinite Kinf hαfin),
    isCenterFiniteFunction_rightConvolution_of_reproducing hsmooth hα hφc hψ₀c hαrep hφ.2.2.2.1
      huniq,
    hmcα.2.2⟩, hcuα, fun t ht g => ?_⟩
  obtain ⟨hI, hEq⟩ := hpair α hα.1.1 hα.2.1 t ht g
  refine ⟨(hψ₀pair t ht g).1, hI, ?_⟩
  rw [hEq, hαrep]

end Langlands.Global

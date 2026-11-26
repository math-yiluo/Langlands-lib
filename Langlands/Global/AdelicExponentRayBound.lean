import Langlands.Global.AdelicLeadingExponentDirectness
import Langlands.Global.AdelicTemperedVanishingReduction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Exponent bounds from growth along a positive split-component ray -/

noncomputable section

open CategoryTheory AlgebraicGeometry Filter
open scoped CategoryTheory.MonObj Topology

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions
  Langlands.HarishChandraSchwartz

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "A" => AdelicGroupPoints F G
local notation "P" => fam.P J
local notation "B" => fam.positiveSplitComponent J
local notation "Parameter" => ComplexCharacterParameter F P

local instance : CommGroup B where
  toGroup := inferInstance
  mul_comm a b := Subtype.ext (fam.positiveSplitComponent_mul_comm J a.property b.property)

/-- Functions whose growth on the powers of `a` is less than every positive exponential
of rate greater than `r`, at each starting point. -/
private def rayGrowth (a : B) (r : ℝ) : Submodule ℂ (A → ℂ) where
  carrier := {f | ∀ g (b : ℝ), 0 < b → r < b →
    Tendsto (fun n : ℕ => (b : ℂ)⁻¹ ^ n * f ((map F P G (fam.p J) a.val) ^ n * g)) atTop (𝓝 0)}
  zero_mem' := by
    intro g b _ _
    simpa only [Pi.zero_apply, mul_zero] using tendsto_const_nhds
  add_mem' := by
    intro f h hf hh g b hb hr
    simpa only [Pi.add_apply, mul_add, add_zero] using (hf g b hb hr).add (hh g b hb hr)
  smul_mem' := by
    intro c f hf g b hb hr
    have heq (n : ℕ) :
        (b : ℂ)⁻¹ ^ n * (c • f) ((map F P G (fam.p J) a.val) ^ n * g) =
          c * ((b : ℂ)⁻¹ ^ n * f ((map F P G (fam.p J) a.val) ^ n * g)) := by
      rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    simp only [heq]
    simpa only [mul_zero] using tendsto_const_nhds.mul (hf g b hb hr)

private theorem rayGrowth_invariant (a : B) (r : ℝ) (b : B) :
    fam.rayGrowth J a r ≤ (fam.rayGrowth J a r).comap (fam.splitComponentRepresentation J b) := by
  intro f hf g t ht hrt
  let x := map F P G (fam.p J) a.val
  let y := map F P G (fam.p J) b.val
  have hxy : Commute x y := by
    show x * y = y * x
    rw [← map_mul, ← map_mul, fam.positiveSplitComponent_mul_comm J a.property b.property]
  have heq (n : ℕ) : y * (x ^ n * g) = x ^ n * (y * g) := by
    rw [← mul_assoc, (hxy.pow_left n).eq.symm, mul_assoc]
  change Tendsto (fun n : ℕ => (t : ℂ)⁻¹ ^ n * f (y * (x ^ n * g))) atTop (𝓝 0)
  simpa only [heq] using hf (y * g) t ht hrt

private theorem rayGrowth_of_polynomial_bound (a : B) {r : ℝ} (hr : 0 < r)
    {f : A → ℂ} (hf : ∀ g, ∃ (C : ℝ) (d : ℕ), ∀ n : ℕ,
      ‖f ((map F P G (fam.p J) a.val) ^ n * g)‖ ≤ C * r ^ n * (1 + (n : ℝ)) ^ d) :
    f ∈ fam.rayGrowth J a r := by
  intro g b hb hbr
  obtain ⟨C, d, hC⟩ := hf g
  let k := Real.log (b / r)
  have hk : 0 < k := Real.log_pos (by rwa [lt_div_iff₀ hr, one_mul])
  have hExp : Real.exp k = b / r := Real.exp_log (div_pos hb hr)
  have hExpPow (n : ℕ) : Real.exp (k * (n : ℝ)) = (b / r) ^ n := by
    rw [mul_comm, Real.exp_nat_mul, hExp]
  have hsmall := (isLittleO_pow_exp_pos_mul_atTop d hk).tendsto_div_nhds_zero
  have hsmallNat : Tendsto (fun n : ℕ => (n : ℝ) ^ d / Real.exp (k * (n : ℝ))) atTop (𝓝 0) :=
    hsmall.comp tendsto_natCast_atTop_atTop
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (g := fun n : ℕ => C * (2 : ℝ) ^ d * ((n : ℝ) ^ d / Real.exp (k * (n : ℝ))))
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hb.le]
    have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hscale : (1 + (n : ℝ)) ^ d ≤ (2 * (n : ℝ)) ^ d :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hC0 : 0 ≤ C := by
      simpa only [pow_zero, Nat.cast_zero, add_zero, one_pow, mul_one] using
        (norm_nonneg _).trans (hC 0)
    calc
      _ ≤ b⁻¹ ^ n * (C * r ^ n * (1 + (n : ℝ)) ^ d) :=
        mul_le_mul_of_nonneg_left (hC n) (by positivity)
      _ ≤ b⁻¹ ^ n * (C * r ^ n * (2 * (n : ℝ)) ^ d) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hscale (by positivity)) (by positivity)
      _ = C * 2 ^ d * ((n : ℝ) ^ d / Real.exp (k * (n : ℝ))) := by
        rw [hExpPow, mul_pow, div_pow, inv_pow]
        field_simp
  · simpa only [mul_zero] using
      (tendsto_const_nhds (x := C * (2 : ℝ) ^ d)).mul hsmallNat

private theorem norm_eigenvalue_le_of_rayGrowth (a : B) (r : ℝ)
    {f : A → ℂ} (hf : f ∈ fam.rayGrowth J a r) (hf0 : f ≠ 0)
    {z : ℂ} (hz : z ≠ 0) (heigen : fam.splitComponentRepresentation J a f = z • f) :
    ‖z‖ ≤ r := by
  by_contra h
  have hrz : r < ‖z‖ := lt_of_not_ge h
  obtain ⟨g, hg⟩ : ∃ g : A, f g ≠ 0 := Function.ne_iff.mp hf0
  let x := map F P G (fam.p J) a.val
  have hval (y : A) : f (x * y) = z * f y := congrFun heigen y
  have hpow (n : ℕ) : f (x ^ n * g) = z ^ n * f g := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_assoc, hval, ih, pow_succ', mul_assoc]
  have hnorm (n : ℕ) : ‖(‖z‖ : ℂ)⁻¹ ^ n * f (x ^ n * g)‖ = ‖f g‖ := by
    rw [hpow, ← mul_assoc, ← mul_pow, norm_mul, norm_pow, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz),
      one_pow, one_mul]
  have ht := (hf g ‖z‖ (norm_pos_iff.mpr hz) hrz).norm
  change Tendsto (fun n : ℕ => ‖(‖z‖ : ℂ)⁻¹ ^ n * f (x ^ n * g)‖) atTop (𝓝 ‖(0 : ℂ)‖) at ht
  simp only [hnorm, norm_zero] at ht
  exact hg (norm_eq_zero.mp (tendsto_nhds_unique ht tendsto_const_nhds).symm)

/-- Every nonzero component of an exponent decomposition inherits the normalized
modulus bound along any positive split-component ray on which the sum, divided by
the half-modulus, has polynomial growth from every starting point. -/
theorem norm_parameterPower_le_one_of_ray_bound
    {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))
    {ψ : A → ℂ} {s : Finset Parameter} {c : Parameter → A → ℂ}
    (hψ : fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho J ψ s c)
    (a : B) (hGrow : ∀ g, ∃ (C : ℝ) (degree : ℕ), ∀ n : ℕ,
      ‖ψ ((map F P G (fam.p J) a.val) ^ n * g)‖ ≤
        C * ‖fam.halfModulus J a.val‖ ^ n * (1 + (n : ℝ)) ^ degree)
    (lam : Parameter) (hlam : lam ∈ s) (hc : c lam ≠ 0) :
    ‖parameterPower F P lam a.val‖ ≤ 1 := by
  let r := ‖fam.halfModulus J a.val‖
  let bound := fam.rayGrowth J a r
  have hr : 0 < r := by
    dsimp [r, halfModulus, parameterPower]
    exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
  let T := fam.splitComponentRepresentation J
  let R : B →* Module.End ℂ ((A → ℂ) ⧸ bound) :=
    { toFun := fun b => bound.mapQ bound (T b) (fam.rayGrowth_invariant J a r b)
      map_one' := by
        apply LinearMap.ext
        intro q
        obtain ⟨f, rfl⟩ := bound.mkQ_surjective q
        change bound.mkQ (T 1 f) = bound.mkQ f
        rw [map_one, Module.End.one_apply]
      map_mul' := fun b b' => by
        apply LinearMap.ext
        intro q
        obtain ⟨f, rfl⟩ := bound.mkQ_surjective q
        change bound.mkQ (T (b * b') f) = bound.mkQ (T b (T b' f))
        rw [map_mul, Module.End.mul_apply] }
  let χ (p : Parameter) (b : B) :=
    parameterPower F P (p + halfModulusParameter F P) b.val
  have hg (p : Parameter) (hp : p ∈ s) :
      c p ∈ jointGenEigenspace T (χ p) :=
    fam.mem_jointGenEigenspace_of_hasUnnormalizedExponent J
      ((fam.hasExponent_iff J p (c p)).mp (hψ.exponent p hp))
  have hQ (p : Parameter) (hp : p ∈ s) :
      bound.mkQ (c p) ∈ jointGenEigenspace R (χ p) := by
    apply mem_jointGenEigenspace.mpr
    intro b
    obtain ⟨k, hk⟩ := (mem_jointGenEigenspace.mp (hg p hp)) b
    have hpow (n : ℕ) (f : A → ℂ) :
        ((R b - χ p b • 1) ^ n) (bound.mkQ f) = bound.mkQ (((T b - χ p b • 1) ^ n) f) := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
        rfl
    exact ⟨k, by rw [hpow, hk, map_zero]⟩
  have hχ : Function.Injective χ := by
    have hinj := (eisensteinPositiveParameters F G P (fam.M J) (fam.A J) (fam.p J) (fam.l J)
      (fam.a J) ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩).2
    intro p p' hh
    exact add_right_cancel (hinj hh)
  have hbψ : ψ ∈ bound := fam.rayGrowth_of_polynomial_bound J a hr hGrow
  have hsum : ∑ p ∈ s, bound.mkQ (c p) = 0 := by
    rw [← map_sum, ← hψ.sum_eq]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hbψ
  have hp : c lam ∈ bound := (Submodule.Quotient.mk_eq_zero _).mp
    ((iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
      ((iSupIndep_jointGenEigenspace R).comp hχ) s _ hQ hsum lam hlam)
  obtain ⟨k, hk⟩ := (mem_jointGenEigenspace.mp (hg lam hlam)) a
  obtain ⟨m, hm0, hm⟩ := exists_pow_apply_eigen (T a) (χ lam a) hc hk
  have hmBound (n : ℕ) : ((T a - χ lam a • 1) ^ n) (c lam) ∈ bound := by
    induction n with
    | zero => simpa using hp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact bound.sub_mem (fam.rayGrowth_invariant J a r a ih) (bound.smul_mem _ ih)
  have hχne : χ lam a ≠ 0 := Complex.exp_ne_zero _
  have hle := fam.norm_eigenvalue_le_of_rayGrowth J a r (hmBound m) hm0 hχne hm
  change ‖parameterPower F P (lam + halfModulusParameter F P) a.val‖ ≤ r at hle
  rw [parameterPower_add, norm_mul] at hle
  exact le_of_mul_le_mul_right (show ‖parameterPower F P lam a.val‖ * r ≤ 1 * r by
    simpa only [r, halfModulus, one_mul] using hle) hr

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints

/-- The necessity step of Delorme, Proposition 3.6, on a supplied ray. A bound by the half
modulus times a polynomial in the ray parameter forces nonpositive real part for every
nonzero normalized exponent on that ray. -/
def AdelicNormalizedExponentRayBoundStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
    {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))
    (ψ : AdelicGroupPoints F G → ℂ) (s : Finset (ComplexCharacterParameter F (fam.P J)))
    (c : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ),
    fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho J ψ s c →
    ∀ a : fam.positiveSplitComponent J,
      (∀ g, ∃ (C : ℝ) (degree : ℕ), ∀ n : ℕ,
        ‖ψ ((map F (fam.P J) G (fam.p J) a.val) ^ n * g)‖ ≤
          C * ‖fam.halfModulus J a.val‖ ^ n * (1 + (n : ℝ)) ^ degree) →
      ∀ lam ∈ s, c lam ≠ 0 →
        realParameterPairing F (fam.P J) (parameterRealPart F (fam.P J) lam)
          (characterLog F (fam.P J) a.val) ≤ 0

theorem adelicNormalizedExponentRayBound : AdelicNormalizedExponentRayBoundStatement := by
  intro F _ _ G _ _ _ fam J d N hsmooth Kinf rho ψ s c hψ a hGrow lam hlam hc
  have h := fam.norm_parameterPower_le_one_of_ray_bound J hsmooth Kinf rho hψ a hGrow lam hlam hc
  rwa [parameterPower, Complex.norm_exp, complexParameterPairing_re, ← Real.exp_zero, Real.exp_le_exp] at h

end Langlands.Global

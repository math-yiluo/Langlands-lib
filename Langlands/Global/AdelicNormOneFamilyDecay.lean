import Langlands.Global.AdelicUnipotentFamilyOscillation
import Langlands.Global.AdelicUnipotentDecayModulo
import Langlands.Automorphic.GroupSchemeNormOneConjugatePaths

/-! # Iterated decay for families on norm-one points

A family `g o` of functions on `G(𝔸)`, indexed by an arbitrary measure space, is given together
with derivatives `g' o l` along the coordinate directions of an embedded atlas of `G(F∞)¹`, in
the integrated form `IsNormOnePathDerivative`. If the constant term along a unipotent subgroup `U`
vanishes and a coordinate chart `Ψ` contracts the archimedean `U`-translates modulo a left
invariance subgroup, then the integral over the family at a norm-one point gains one contraction
factor over the integrals of the derivatives at nearby points. Iteration gains arbitrary powers. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open AlgebraicGeometry CategoryTheory Filter MeasureTheory NumberField Set Topology Metric
open scoped Classical CategoryTheory.MonObj ENNReal Manifold ContDiff Pointwise

namespace Langlands.Global

open AdelicGroupPoints InfiniteAdelicGroupPoints Langlands.GroupScheme Langlands.Analysis
  Langlands.Automorphic.GroupSchemeFunctions Langlands.Geometry.Manifold

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {d e : ℕ} {hG : SmoothOfRelativeDimension d G.X.hom}

local notation "A" => AdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "G∞¹" => infiniteNormOneSubgroup F G
local notation "IE" => 𝓘(ℝ, Fin e → ℝ)
local notation "IG" => 𝓘(ℝ, smoothModel F d)

/-- **Derivatives along norm-one right orbits, integrated form.** For every norm-one point `y` and
every smooth path `c` of `G(F∞)¹` (for the atlas `At`) with translated velocity `V`,
`g (y c(1)) - g (y c(0)) = ∫₀¹ ∑_l V(t)_l g' l (y c(t)) dt`. -/
def IsNormOnePathDerivative (At : NormOneLieAtlas F G hG e) (g : A → ℂ) (g' : Fin e → A → ℂ) :
    Prop :=
  letI := At.chartedSpace
  letI := At.lieGroup
  ∀ y ∈ normOneSubgroup F G, ∀ (c : ℝ → G∞¹) (V : ℝ → Fin e → ℝ),
    ContMDiff 𝓘(ℝ, ℝ) IE ∞ c → (∀ t, leftPathVelocity c t = V t) → Continuous V →
      g (y * ofInfinite F G (c 1)) - g (y * ofInfinite F G (c 0)) =
        ∫ t in (0 : ℝ)..1, ∑ l : Fin e, (V t l : ℂ) * g' l (y * ofInfinite F G (c t))

omit [LocallyOfFiniteType G.X.hom] in
/-- **Linear combinations.** The integrated derivative identity is preserved by finite linear
combinations, when the derivatives are continuous. -/
theorem isNormOnePathDerivative_sum (At : NormOneLieAtlas F G hG e) {Idx : Type*} (s : Finset Idx)
    (c : Idx → ℂ) (f : Idx → A → ℂ) (f' : Idx → Fin e → A → ℂ)
    (hf' : ∀ k ∈ s, ∀ l, Continuous (f' k l))
    (hder : ∀ k ∈ s, IsNormOnePathDerivative At (f k) (f' k)) :
    IsNormOnePathDerivative At (fun x => ∑ k ∈ s, c k * f k x)
      (fun l x => ∑ k ∈ s, c k * f' k l x) := by
  let := At.chartedSpace
  let := At.lieGroup
  intro y hy cp V hc hV hVc
  have hcc : Continuous cp := hc.continuous
  have hpath : Continuous fun t : ℝ => y * ofInfinite F G (cp t) :=
    continuous_const.mul ((ofInfinite F G).continuous.comp (continuous_subtype_val.comp hcc))
  have hint (k : Idx) (hk : k ∈ s) : IntervalIntegrable
      (fun t => ∑ l : Fin e, (V t l : ℂ) * f' k l (y * ofInfinite F G (cp t))) MeasureTheory.volume 0 1 :=
    (continuous_finsetSum _ fun l _ =>
      (Complex.continuous_ofReal.comp ((continuous_apply l).comp hVc)).mul
        ((hf' k hk l).comp hpath)).intervalIntegrable 0 1
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  rw [Finset.sum_congr rfl fun k hk => by rw [hder k hk y hy cp V hc hV hVc]]
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum fun k hk => (hint k hk).const_mul _]
  congr 1
  funext t
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

omit [LocallyOfFiniteType G.X.hom] in
/-- A right translate by an archimedean conjugate is a left archimedean factor before `k`. -/
theorem mul_ofInfinite_conj (k : A) (h : G∞) :
    k * ofInfinite F G ((infinite F G k)⁻¹ * h * infinite F G k) = ofInfinite F G h * k := by
  obtain ⟨ki, kf, rfl⟩ : ∃ ki kf, k = pair F G ki kf := ⟨_, _, (pair_projections F G k).symm⟩
  simp only [infinite_pair, ofInfinite_eq_pair, pair_mul]
  congr 1 <;> group

section Step

variable {U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine U.X.left]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left] (At : NormOneLieAtlas F G hG e)
  {X : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "m" => map F U G j

set_option maxHeartbeats 1000000 in
/-- **One step of family decay.** Under contraction modulo `L₀` by a chart `Ψ` with values in
`G(F∞)¹`, for families whose constant term along `U` vanishes, the integral over the family at a
norm-one point `p a(t) k` is at most `C ε(t)` times the supremum over nearby points `p a(t) k'`
(with the same finite component) and directions `l` of the integrals of the derivatives. -/
theorem normOneFamilyContractionStep [FiniteDimensional ℝ E]
    (Ω : Set A) (a : X → A) (L₀ : Subgroup A) (Ψ : E → G∞) (ε : X → ℝ)
    (hUs : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (Bε : ℝ) (hBε : 0 ≤ Bε) (hεB : ∀ t, ε t ≤ Bε)
    (hconj : HasUnipotentContractionModulo (F := F) (X := X) (E := E) j Ω a L₀ Ψ ε)
    (hΨ₀ : Ψ 0 = 1) (hΨ₁ : ∀ v, Ψ v ∈ G∞¹)
    (Yf : Set Gf) (hY : IsCompact Yf) (L : Subgroup Gf) (hL : IsOpen (L : Set Gf))
    (K : Set A) (hK : IsCompact K) (hK₁ : K ⊆ normOneSubgroup F G) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    ContMDiff 𝓘(ℝ, E) IG ∞ Ψ →
    ∃ K' : Set A, IsCompact K' ∧ K ⊆ K' ∧ K' ⊆ normOneSubgroup F G ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ Ω, ∀ t : X, p * a t ∈ normOneSubgroup F G → ∀ k ∈ K,
      finite F G (p * a t * k) ∈ Yf →
      ∀ {Ω' : Type w} [MeasurableSpace Ω'] (mΩ : Measure Ω') (g : Ω' → A → ℂ)
        (g' : Ω' → Fin e → A → ℂ),
      (∀ o, Continuous (g o)) → Measurable (fun q : Ω' × A => g q.1 q.2) →
      (∀ o l, Continuous (g' o l)) → (∀ l, Measurable (fun q : Ω' × A => g' q.1 l q.2)) →
      (∀ o (q : RationalGroupPoints F U) x, g o (m (rational F U q) * x) = g o x) →
      (∀ o, ∀ l ∈ L, ∀ x, g o (x * ofFinite F G l) = g o x) →
      (∀ o, ∀ l ∈ L₀, ∀ x, g o (l * x) = g o x) →
      (∀ o, subgroupConstantTerm F j (g o) = 0) →
      (∀ o, IsNormOnePathDerivative At (g o) (g' o)) →
      ∫⁻ o, ‖g o (p * a t * k)‖ₑ ∂mΩ ≤
        ENNReal.ofReal (C * ε t) * ⨆ (k' ∈ K') (_ : finite F G k' = finite F G k) (l : Fin e),
          ∫⁻ o, ‖g' o l (p * a t * k')‖ₑ ∂mΩ := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := At.chartedSpace
  let := At.lieGroup
  intro hΨ
  obtain ⟨D, hD, hosc⟩ := adelicUnipotentFamilyOscillation.{u, w} j hconn hu Yf hY L hL
  obtain ⟨C₀, hC₀, hCconj⟩ := hconj D hD
  let B := C₀ * Bε
  have hB : 0 ≤ B := mul_nonneg hC₀ hBε
  let S := closedBall (0 : E) B
  let Kinf := infinite F G '' K
  have hKinf : IsCompact Kinf := hK.image (infinite F G).continuous
  obtain ⟨C₁, hC₁, hvel⟩ := exists_norm_conjugateDifferential_le At Ψ hΨ₁ Kinf hKinf B hΨ
  let K' := ((ofInfinite F G) ∘ Ψ '' S) * K
  have hΨc : Continuous Ψ := hΨ.continuous
  have hK' : IsCompact K' :=
    ((isCompact_closedBall (0 : E) B).image ((ofInfinite F G).continuous.comp hΨc)).mul hK
  have hKK' : K ⊆ K' := by
    intro k hk
    refine Set.mem_mul.mpr ⟨_, ⟨0, mem_closedBall_self hB, rfl⟩, k, hk, ?_⟩
    simp only [Function.comp_apply, hΨ₀, map_one, one_mul]
  have hK'₁ : K' ⊆ normOneSubgroup F G := by
    rintro _ ⟨_, ⟨v, -, rfl⟩, k, hk, rfl⟩
    exact (normOneSubgroup F G).mul_mem (hΨ₁ v) (hK₁ hk)
  refine ⟨K', hK', hKK', hK'₁, (e : ℝ) * C₁ * C₀, by positivity, ?_⟩
  intro p hp t hpt k hk hfin Ω' _ mΩ g g' hg hgm hg' hg'm hgR hgL hgL₀ hCT hder
  let x := p * a t * k
  have hx₁ : x ∈ normOneSubgroup F G := (normOneSubgroup F G).mul_mem hpt (hK₁ hk)
  let M := ⨆ (k' ∈ K') (_ : finite F G k' = finite F G k) (l : Fin e),
    ∫⁻ o, ‖g' o l (p * a t * k')‖ₑ ∂mΩ
  -- the bound for one archimedean unipotent translate
  have hone (u : InfiniteAdelicGroupPoints F U) (hu : u ∈ D) :
      ∫⁻ o, ‖g o x - g o (m (ofInfinite F U u) * x)‖ₑ ∂mΩ ≤
        ENNReal.ofReal ((e : ℝ) * C₁ * C₀ * ε t) * M := by
    obtain ⟨v, hv, l₀, hl₀, hpu⟩ := hCconj p hp t u hu
    let kinf := infinite F G k
    let c := conjugatePath Ψ hΨ₁ kinf v
    let V : ℝ → Fin e → ℝ := fun s => conjugateDifferential At Ψ hΨ₁ (kinf, s • v) v
    have hc₀ : x * ofInfinite F G (c 0) = x := by
      simp only [c, conjugatePath_zero, OneMemClass.coe_one, map_one, mul_one]
    have hc_pt (s : ℝ) : x * ofInfinite F G (c s) = p * a t * (ofInfinite F G (Ψ (s • v)) * k) := by
      change p * a t * k * ofInfinite F G (c s : G∞) = _
      rw [conjugatePath_val Ψ hΨ₁ hΨ₀, mul_assoc, mul_ofInfinite_conj]
    have hc₁ (o : Ω') : g o (m (ofInfinite F U u) * x) = g o (x * ofInfinite F G (c 1)) := by
      have h1 : m (ofInfinite F U u) * x = l₀ * (p * a t * (ofInfinite F G (Ψ v) * k)) := by
        calc m (ofInfinite F U u) * x = m (ofInfinite F U u) * (p * a t) * k := by
              simp only [x, mul_assoc]
          _ = l₀ * (p * a t * ofInfinite F G (Ψ v)) * k := by rw [hpu]
          _ = l₀ * (p * a t * (ofInfinite F G (Ψ v) * k)) := by simp only [mul_assoc]
      rw [h1, hgL₀ o l₀ hl₀, hc_pt 1, one_smul]
    have hcc : Continuous c := (contMDiff_conjugatePath At Ψ hΨ₁ kinf v hΨ).continuous
    have hpath : Continuous fun s : ℝ => x * ofInfinite F G (c s) :=
      continuous_const.mul ((ofInfinite F G).continuous.comp (continuous_subtype_val.comp hcc))
    have hVc : Continuous V :=
      ((continuous_conjugateDifferential At Ψ hΨ₁ hΨ).comp
        (continuous_const.prodMk (continuous_id.smul continuous_const))).clm_apply continuous_const
    have hint (o : Ω') : g o (x * ofInfinite F G (c 1)) - g o (x * ofInfinite F G (c 0)) =
        ∫ s in (0 : ℝ)..1, ∑ l : Fin e, (V s l : ℂ) * g' o l (x * ofInfinite F G (c s)) :=
      hder o x hx₁ c V (contMDiff_conjugatePath At Ψ hΨ₁ kinf v hΨ)
        (fun s => leftPathVelocity_conjugatePath At Ψ hΨ₁ kinf v s hΨ) hVc
    have hcont (o : Ω') : Continuous fun s : ℝ =>
        ∑ l : Fin e, (V s l : ℂ) * g' o l (x * ofInfinite F G (c s)) :=
      continuous_finsetSum _ fun l _ =>
        (Complex.continuous_ofReal.comp ((continuous_apply l).comp hVc)).mul
          ((hg' o l).comp hpath)
    have hmeas : Measurable (Function.uncurry fun (o : Ω') (s : ℝ) =>
        ∑ l : Fin e, (V s l : ℂ) * g' o l (x * ofInfinite F G (c s))) := by
      refine Finset.measurable_sum _ fun l _ => ?_
      exact ((Complex.continuous_ofReal.comp ((continuous_apply l).comp hVc)).measurable.comp
        measurable_snd).mul ((hg'm l).comp (measurable_fst.prodMk (hpath.measurable.comp measurable_snd)))
    have hftc := lintegral_enorm_sub_le_iSup_of_integral mΩ
      (f := fun o s => g o (x * ofInfinite F G (c s))) hint hcont hmeas
    have hvB : v ∈ closedBall (0 : E) B := by
      rw [mem_closedBall, dist_zero_right]
      exact hv.trans (mul_le_mul_of_nonneg_left (hεB t) hC₀)
    have hterm (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        ∫⁻ o, ‖∑ l : Fin e, (V s l : ℂ) * g' o l (x * ofInfinite F G (c s))‖ₑ ∂mΩ ≤
          ENNReal.ofReal ((e : ℝ) * C₁ * C₀ * ε t) * M := by
      have hVl (l : Fin e) : ‖((V s l : ℝ) : ℂ)‖ₑ ≤ ENNReal.ofReal (C₁ * (C₀ * ε t)) := by
        rw [← ofReal_norm, Complex.norm_real]
        apply ENNReal.ofReal_le_ofReal
        calc ‖V s l‖ ≤ ‖V s‖ := norm_le_pi_norm (V s) l
          _ ≤ C₁ * ‖v‖ := hvel kinf ⟨k, hk, rfl⟩ v hvB s hs
          _ ≤ C₁ * (C₀ * ε t) := mul_le_mul_of_nonneg_left hv hC₁
      have hsv : s • v ∈ S := by
        rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hs.1]
        rw [mem_closedBall, dist_zero_right] at hvB
        exact (mul_le_of_le_one_left (norm_nonneg v) hs.2).trans hvB
      have hk' : ofInfinite F G (Ψ (s • v)) * k ∈ K' :=
        Set.mem_mul.mpr ⟨_, ⟨s • v, hsv, rfl⟩, k, hk, rfl⟩
      have hk'f : finite F G (ofInfinite F G (Ψ (s • v)) * k) = finite F G k := by
        rw [map_mul, finite_ofInfinite, one_mul]
      have hgM (l : Fin e) :
          ∫⁻ o, ‖g' o l (x * ofInfinite F G (c s))‖ₑ ∂mΩ ≤ M := by
        rw [hc_pt s]
        exact le_iSup₂_of_le (f := fun k' (_ : k' ∈ K') =>
          ⨆ (_ : finite F G k' = finite F G k) (l : Fin e), ∫⁻ o, ‖g' o l (p * a t * k')‖ₑ ∂mΩ)
          _ hk' (le_iSup_of_le hk'f (le_iSup_of_le l le_rfl))
      calc ∫⁻ o, ‖∑ l : Fin e, (V s l : ℂ) * g' o l (x * ofInfinite F G (c s))‖ₑ ∂mΩ
          ≤ ∫⁻ o, ∑ l : Fin e, ‖((V s l : ℝ) : ℂ)‖ₑ * ‖g' o l (x * ofInfinite F G (c s))‖ₑ ∂mΩ := by
            refine lintegral_mono fun o => (enorm_sum_le _ _).trans ?_
            exact Finset.sum_le_sum fun l _ => (enorm_mul _ _).le
        _ = ∑ l : Fin e, ‖((V s l : ℝ) : ℂ)‖ₑ * ∫⁻ o, ‖g' o l (x * ofInfinite F G (c s))‖ₑ ∂mΩ := by
            rw [lintegral_finsetSum]
            · exact Finset.sum_congr rfl fun l _ => lintegral_const_mul _
                ((hg'm l).comp (measurable_id.prodMk measurable_const)).enorm
            · intro l _
              exact ((hg'm l).comp (measurable_id.prodMk measurable_const)).enorm.const_mul _
        _ ≤ ∑ _l : Fin e, ENNReal.ofReal (C₁ * (C₀ * ε t)) * M :=
            Finset.sum_le_sum fun l _ => mul_le_mul' (hVl l) (hgM l)
        _ = ENNReal.ofReal ((e : ℝ) * C₁ * C₀ * ε t) * M := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
            congr 1
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg e)]
            congr 1
            ring
    calc ∫⁻ o, ‖g o x - g o (m (ofInfinite F U u) * x)‖ₑ ∂mΩ
        = ∫⁻ o, ‖g o (x * ofInfinite F G (c 1)) - g o (x * ofInfinite F G (c 0))‖ₑ ∂mΩ := by
          refine lintegral_congr fun o => ?_
          rw [hc₁ o, hc₀, enorm_sub_rev]
      _ ≤ ⨆ s ∈ Icc (0 : ℝ) 1, ∫⁻ o,
            ‖∑ l : Fin e, (V s l : ℂ) * g' o l (x * ofInfinite F G (c s))‖ₑ ∂mΩ := hftc
      _ ≤ ENNReal.ofReal ((e : ℝ) * C₁ * C₀ * ε t) * M := iSup₂_le hterm
  have hzero (o : Ω') : subgroupConstantTerm F j (g o) x = 0 := by rw [hCT o]; rfl
  calc ∫⁻ o, ‖g o (p * a t * k)‖ₑ ∂mΩ
      = ∫⁻ o, ‖g o x - subgroupConstantTerm F j (g o) x‖ₑ ∂mΩ := by
        refine lintegral_congr fun o => ?_
        rw [hzero o, sub_zero]
    _ ≤ ⨆ u ∈ D, ∫⁻ o, ‖g o x - g o (m (ofInfinite F U u) * x)‖ₑ ∂mΩ :=
        hosc mΩ g hg hgm hgR hgL x hfin
    _ ≤ ENNReal.ofReal ((e : ℝ) * C₁ * C₀ * ε t) * M := iSup₂_le hone

set_option maxHeartbeats 1000000 in
/-- **Iterated family decay.** With the hypotheses of `normOneFamilyContractionStep` for a whole
system of iterated derivatives `g o w` indexed by words `w` (where `g o (l :: w)` is the derivative
of `g o w` along `l`), the integral over the family of `g o []` at `p a(t) k` is at most
`C ε(t)^n` times the supremum over nearby points and words of length `n` of the integrals of the
derivatives. -/
theorem normOneFamilyDecayModulo [FiniteDimensional ℝ E]
    (Ω : Set A) (a : X → A) (L₀ : Subgroup A) (Ψ : E → G∞) (ε : X → ℝ)
    (hUs : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (Bε : ℝ) (hBε : 0 ≤ Bε) (hεB : ∀ t, ε t ≤ Bε) (hε : ∀ t, 0 ≤ ε t)
    (hconj : HasUnipotentContractionModulo (F := F) (X := X) (E := E) j Ω a L₀ Ψ ε)
    (hΨ₀ : Ψ 0 = 1) (hΨ₁ : ∀ v, Ψ v ∈ G∞¹)
    (Yf : Set Gf) (hY : IsCompact Yf) (L : Subgroup Gf) (hL : IsOpen (L : Set Gf)) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    ContMDiff 𝓘(ℝ, E) IG ∞ Ψ →
    ∀ (n : ℕ) (K : Set A), IsCompact K → K ⊆ normOneSubgroup F G →
    ∃ K' : Set A, IsCompact K' ∧ K ⊆ K' ∧ K' ⊆ normOneSubgroup F G ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ Ω, ∀ t : X, p * a t ∈ normOneSubgroup F G → ∀ k ∈ K,
      finite F G (p * a t * k) ∈ Yf →
      ∀ {Ω' : Type w} [MeasurableSpace Ω'] (mΩ : Measure Ω') (g : Ω' → List (Fin e) → A → ℂ),
      (∀ o w, Continuous (g o w)) → (∀ w, Measurable (fun q : Ω' × A => g q.1 w q.2)) →
      (∀ o w (q : RationalGroupPoints F U) x, g o w (m (rational F U q) * x) = g o w x) →
      (∀ o w, ∀ l ∈ L, ∀ x, g o w (x * ofFinite F G l) = g o w x) →
      (∀ o w, ∀ l ∈ L₀, ∀ x, g o w (l * x) = g o w x) →
      (∀ o w, w.length < n → subgroupConstantTerm F j (g o w) = 0) →
      (∀ o w, w.length < n → IsNormOnePathDerivative At (g o w) (fun l => g o (l :: w))) →
      ∫⁻ o, ‖g o [] (p * a t * k)‖ₑ ∂mΩ ≤
        ENNReal.ofReal (C * ε t ^ n) * ⨆ (k' ∈ K') (_ : finite F G k' = finite F G k)
          (w : List (Fin e)) (_ : w.length = n), ∫⁻ o, ‖g o w (p * a t * k')‖ₑ ∂mΩ := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  intro hΨ n
  induction n with
  | zero =>
    intro K hK hK₁
    refine ⟨K, hK, subset_rfl, hK₁, 1, zero_le_one, ?_⟩
    intro p _ t _ k hk _ Ω' _ mΩ g _ _ _ _ _ _ _
    simp only [pow_zero, mul_one, ENNReal.ofReal_one, one_mul]
    exact le_iSup₂_of_le (f := fun k' (_ : k' ∈ K) => ⨆ (_ : finite F G k' = finite F G k)
      (w : List (Fin e)) (_ : w.length = 0), ∫⁻ o, ‖g o w (p * a t * k')‖ₑ ∂mΩ) k hk
      (le_iSup_of_le rfl (le_iSup_of_le [] (le_iSup_of_le rfl le_rfl)))
  | succ n ih =>
    intro K hK hK₁
    obtain ⟨K₁, hK₁c, hKK₁, hK₁₁, C₁, hC₁, hone⟩ := normOneFamilyContractionStep.{u, w} j At Ω a L₀ Ψ ε
      hUs hconn hu Bε hBε hεB hconj hΨ₀ hΨ₁ Yf hY L hL K hK hK₁ hΨ
    obtain ⟨K', hK'c, hK₁K', hK'₁, C₂, hC₂, hiter⟩ := ih K₁ hK₁c hK₁₁
    refine ⟨K', hK'c, hKK₁.trans hK₁K', hK'₁, C₁ * C₂, mul_nonneg hC₁ hC₂, ?_⟩
    intro p hp t hpt k hk hfin Ω' _ mΩ g hg hgm hgR hgL hgL₀ hCT hder
    let M' := ⨆ (k' ∈ K') (_ : finite F G k' = finite F G k) (w : List (Fin e))
      (_ : w.length = n + 1), ∫⁻ o, ‖g o w (p * a t * k')‖ₑ ∂mΩ
    have h1 := hone p hp t hpt k hk hfin mΩ (fun o => g o []) (fun o l => g o [l])
      (fun o => hg o []) (hgm []) (fun o l => hg o [l]) (fun l => hgm [l])
      (fun o => hgR o []) (fun o => hgL o []) (fun o => hgL₀ o [])
      (fun o => hCT o [] (Nat.succ_pos n)) (fun o => hder o [] (Nat.succ_pos n))
    have h2 : (⨆ (k' ∈ K₁) (_ : finite F G k' = finite F G k) (l : Fin e),
        ∫⁻ o, ‖g o [l] (p * a t * k')‖ₑ ∂mΩ) ≤ ENNReal.ofReal (C₂ * ε t ^ n) * M' := by
      refine iSup₂_le fun k' hk' => iSup_le fun hk'f => iSup_le fun l => ?_
      have hfin' : finite F G (p * a t * k') ∈ Yf := by rwa [map_mul, hk'f, ← map_mul]
      have h := hiter p hp t hpt k' hk' hfin' mΩ (fun o w => g o (w ++ [l]))
        (fun o w => hg o _) (fun w => hgm _) (fun o w => hgR o _) (fun o w => hgL o _)
        (fun o w => hgL₀ o _)
        (fun o w hw => hCT o _ (by simp only [List.length_append, List.length_singleton]; omega))
        (fun o w hw => by
          have := hder o (w ++ [l]) (by simp only [List.length_append, List.length_singleton]; omega)
          simpa only [List.cons_append] using this)
      refine h.trans (mul_le_mul' le_rfl ?_)
      refine iSup₂_le fun k'' hk'' => iSup_le fun hk''f => iSup_le fun w => iSup_le fun hw => ?_
      exact le_iSup₂_of_le (f := fun k'' (_ : k'' ∈ K') => ⨆ (_ : finite F G k'' = finite F G k)
        (w : List (Fin e)) (_ : w.length = n + 1), ∫⁻ o, ‖g o w (p * a t * k'')‖ₑ ∂mΩ) k'' hk''
        (le_iSup_of_le (hk''f.trans hk'f) (le_iSup_of_le (w ++ [l])
          (le_iSup_of_le (by simp only [List.length_append, List.length_singleton, hw]) le_rfl)))
    calc ∫⁻ o, ‖g o [] (p * a t * k)‖ₑ ∂mΩ
        ≤ ENNReal.ofReal (C₁ * ε t) * ⨆ (k' ∈ K₁) (_ : finite F G k' = finite F G k)
            (l : Fin e), ∫⁻ o, ‖g o [l] (p * a t * k')‖ₑ ∂mΩ := h1
      _ ≤ ENNReal.ofReal (C₁ * ε t) * (ENNReal.ofReal (C₂ * ε t ^ n) * M') := mul_le_mul' le_rfl h2
      _ = ENNReal.ofReal (C₁ * C₂ * ε t ^ (n + 1)) * M' := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hC₁ (hε t))]
        congr 2
        ring

end Step

end Langlands.Global

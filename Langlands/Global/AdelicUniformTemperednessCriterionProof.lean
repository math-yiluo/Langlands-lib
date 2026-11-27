import Langlands.Global.AdelicUniformTemperednessGrowth
import Langlands.Global.AdelicUniformTemperednessCriterionStatement
import Langlands.Global.AdelicLocalFinitenessProductBridge
import Langlands.Global.AdelicStandardParabolicFamilyConstruction
import Langlands.GroupScheme.Rational.CentralRootRestriction

/-! # Proof of the uniform temperedness criterion on Siegel sets

The criterion `UniformTemperednessCriterionStatement` (Mœglin–Waldspurger 1995, Lemma I.4.1;
Delorme 2023, Proposition 3.6), proved from `HalfModulusRootProductStatement`, which compares
the half-modulus character of a standard parabolic on its split component with the product of
the positive roots. The exponent is `k = 2m`. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry NumberField Set
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints InfiniteAdelicGroupPoints PositiveRealTorus RepresentationGrowth
  AdelicSiegelFactors

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {𝓕 : StandardParabolicFamily F G}

local notation "A" => AdelicGroupPoints F G
local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "Δ" => simpleRelativeRoots 𝓕.i 𝓕.ν

/-- **Siegel torus points as positive torus points.** For a split component `Z₀ → T` of `G`
and `T₀ → T`, every product `z · a(b)` of `z ∈ A_G` and a positive point `b` of `T₀` is the
image of a positive point `u` of `T` on which every relative root takes the value it takes
at `b`. -/
theorem exists_torusPoint_eq_mul {T₀ Z₀ : CommGroupScheme (Spec (CommRingCat.of F))}
    (j : T₀ ⟶ 𝓕.T) (zc : Z₀ ⟶ 𝓕.T) (hzc : IsSplitComponent (CommGroupScheme.groupHom zc ≫ 𝓕.i))
    {z : A} (hz : z ∈ RestrictionSplitCentre.canonicalSubgroup F G)
    (b : intrinsicSubgroup F T₀) :
    ∃ u ∈ intrinsicSubgroup F 𝓕.T,
      torusPoint (𝓕 := 𝓕) u = z * positiveMap F G 𝓕.T 𝓕.i T₀ j b ∧
      ∀ β ∈ relativeRoots 𝓕.i, normCharacter F 𝓕.T β u = normCharacter F T₀ (j ≫ β) b := by
  rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup hzc] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  let c := map F Z₀.toGrp 𝓕.T.toGrp (CommGroupScheme.groupHom zc) z'
  let c' := map F T₀.toGrp 𝓕.T.toGrp (CommGroupScheme.groupHom j) b.val
  have hc : c ∈ intrinsicSubgroup F 𝓕.T := map_intrinsicSubgroup_le F Z₀ 𝓕.T zc ⟨z', hz', rfl⟩
  have hc' : c' ∈ intrinsicSubgroup F 𝓕.T :=
    map_intrinsicSubgroup_le F T₀ 𝓕.T j ⟨b.val, b.prop, rfl⟩
  refine ⟨c * c', mul_mem hc hc', ?_, fun β hβ => ?_⟩
  · show map F 𝓕.T.toGrp G 𝓕.i (c * c') = _
    rw [map_mul]
    congr 1
  · have h0 : zc ≫ β = 0 :=
      root_restrict_eq_zero_of_isCentral 𝓕.i zc hzc.1.1.1 hzc.1.2 hβ
    have hc1 : normCharacter F 𝓕.T β c = 1 := by
      have := normCharacter_pullback F Z₀ 𝓕.T zc β z'
      rw [h0] at this
      change normCharacter F 𝓕.T β
        (pointMap F Z₀.toGrp 𝓕.T.toGrp (Adeles F) (CommGroupScheme.groupHom zc) z') = 1
      rw [← this, normCharacter_apply, Lie.characterValue_zero, map_one]
    rw [map_mul, hc1, one_mul, normCharacter_pullback]
    rfl

/-- **The bound on Siegel sets for one standard parabolic family.** Assume the half-modulus
statement. Let `rho` be a closed matrix embedding of size `N > 0`, and let `f` have uniform
moderate growth at an open level, with constant terms along every standard index satisfying
subunitary shift equations of order `m`. Let `Z₀ → T` be a split component of `G` and
`j : T₀ → T`. Then for every threshold `t` and compact `Ω` there is `B` with
`‖f x (z a(b) ϖ)‖ ≤ B δ(b)^{1/2} σ(z a(b) ϖ)^{2m}` for `x ∈ S`, `z ∈ A_G`, `b` in the weak
chamber of threshold `t` and `ϖ ∈ Ω`. -/
theorem siegel_bound_of_family (hHM : HalfModulusRootProductStatement.{0}) [Fintype Δ]
    (Fr : TorusFrame 𝓕) {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hG : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hG)
    (hN : 0 < N) (hrho : IsClosedSubgroup rho) {Ix : Type}
    (f : Ix → FinitePlotSmoothRationalFunctions F G) (S : Set Ix)
    (L : Subgroup (FiniteAdelicGroupPoints F G)) (R : ℝ) (m : ℕ)
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G)))
    (hgrowth : IsUniformGrowthFamily rho hG hcalc L R f S)
    (hexp : ∀ J : Idx, ∀ x ∈ S,
      𝓕.HasSubunitaryShiftEquations J m (𝓕.constantTerm J (evaluate F G (f x).val)))
    {T₀ Z₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ 𝓕.T) (zc : Z₀ ⟶ 𝓕.T)
    (hzc : IsSplitComponent (CommGroupScheme.groupHom zc ≫ 𝓕.i))
    (t : ℝ≥0ˣ) (Ω : Set A) (hΩ : IsCompact Ω) :
    ∃ B : ℝ, ∀ x ∈ S, ∀ z ∈ RestrictionSplitCentre.canonicalSubgroup F G,
      ∀ b ∈ weakSimpleRootChamber F T₀ 𝓕.T j G 𝓕.i 𝓕.ν t, ∀ ϖ ∈ Ω,
        ‖evaluate F G (f x).val (z * positiveMap F G 𝓕.T 𝓕.i T₀ j b * ϖ)‖ ≤
          B * Real.sqrt (siegelModulus F G 𝓕.T 𝓕.i 𝓕.ν T₀ j b) *
            adelicLogHeight F G rho (z * positiveMap F G 𝓕.T 𝓕.i T₀ j b * ϖ) ^ (2 * m) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  obtain ⟨hgr, hdgr⟩ := family_growth_bounds rho hG hcalc Fr hN f S L R hL hgrowth
  have hsm : letI := smoothChartedSpace F G hG
      ∀ x ∈ S, ∀ c : FiniteAdelicGroupPoints F G, ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞
        (fun y : InfiniteAdelicGroupPoints F G => evaluate F G (f x).val (pair F G y c)) := by
    let := smoothChartedSpace F G hG
    intro x _ c
    exact ((mem_finitePlotSmoothRationalSubrepresentation_iff_contMDiff F G hG (f x).val).mp
      (f x).prop).1 c
  have hlev : ∀ x ∈ S, ∀ l ∈ L, ∀ y,
      evaluate F G (f x).val (y * ofFinite F G l) = evaluate F G (f x).val y :=
    fun x hx l hl y => congrArg (fun z : FinitePlotSmoothRationalFunctions F G =>
      evaluate F G z.val y) (hgrowth.1 x hx l hl)
  have hsh : ∀ J J' : Idx, J'.1 ⊆ J.1 → ∀ x ∈ S,
      HasTorusShiftEquations 𝓕 J.1 m (𝓕.constantTerm J' (evaluate F G (f x).val)) :=
    fun J J' hJ x hx => hasTorusShiftEquations_of_le hHM hJ (hexp J' x hx)
  set lt : ℝ := Real.log ((t : ℝ≥0) : ℝ) with hlt
  set θ : ℝ := |lt| * ∑ α : Δ, (Fr.step α)⁻¹ with hθdef
  have hθ : 0 ≤ θ := mul_nonneg (abs_nonneg _)
    (Finset.sum_nonneg fun α _ => (inv_pos.mpr (Fr.step_pos α)).le)
  obtain ⟨C, hC0, hC⟩ := constantTerm_chamber_bound Fr hG (fun x => (f x).val) S m L hL hsm
    hlev hsh hgr hdgr 𝓕.top Ω hΩ θ hθ
  obtain ⟨Ah, Bh, hAh, hBh, hcrd⟩ := Fr.exists_crd_le_log_height rho hN hrho
  obtain ⟨H, hH⟩ :=
    (hΩ.image ((continuous_adelicHeight F G rho hN).comp continuous_inv)).bddAbove
  set H' : ℝ := max 1 H with hH'def
  have hH'1 : 1 ≤ H' := le_max_left _ _
  set cN : ℝ := (N : ℝ) ^ (∑ v : InfinitePlace F, v.mult) with hcNdef
  have hcN1 : 1 ≤ cN := one_le_pow₀ (by exact_mod_cast hN)
  set c₀ : ℝ := 2 * (m : ℝ) * (Ah * (Real.log cN + Real.log H') + Bh) + 3 with hc₀def
  have hc₀ : 0 ≤ c₀ := by
    have := Real.log_nonneg hcN1
    have := Real.log_nonneg hH'1
    positivity
  set c₁ : ℝ := 2 * (m : ℝ) * Ah + c₀ with hc₁def
  have hc₁ : 0 ≤ c₁ := by positivity
  refine ⟨C * c₁ ^ (2 * m), fun x hx z hz b hb ϖ hϖ => ?_⟩
  obtain ⟨u, hu, hpt, hroot⟩ := exists_torusPoint_eq_mul j zc hzc hz b
  have hchamber : ∀ α : Δ, -θ ≤ (Fr.crd u).1 α := by
    intro α
    have hstep := Fr.step_pos α
    have h1 : Fr.step α * (Fr.crd u).1 α =
        Real.log ((normCharacter F T₀ (j ≫ α.val) b : ℝ≥0) : ℝ) := by
      rw [← Fr.characterLog_root, ← log_normCharacter,
        hroot α.val (simpleRelativeRoots_subset_relativeRoots _ _ α.prop)]
    have h2 : lt ≤ Real.log ((normCharacter F T₀ (j ≫ α.val) b : ℝ≥0) : ℝ) := by
      refine Real.log_le_log (by exact_mod_cast pos_iff_ne_zero.mpr t.ne_zero) ?_
      exact NNReal.coe_le_coe.mpr (Units.val_le_val.mpr (hb α.val α.prop))
    have h4 : |lt| * (Fr.step α)⁻¹ ≤ θ :=
      mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun α => (Fr.step α)⁻¹)
        (fun α _ => (inv_pos.mpr (Fr.step_pos α)).le) (Finset.mem_univ α)) (abs_nonneg _)
    have h5 : -(|lt| * (Fr.step α)⁻¹) ≤ (Fr.crd u).1 α := by
      have e : -(|lt| * (Fr.step α)⁻¹) = (-|lt|) / Fr.step α := by ring
      rw [e, div_le_iff₀ hstep]
      have := neg_abs_le lt
      nlinarith
    linarith
  have hmod : torusModulus 𝓕 u = siegelModulus F G 𝓕.T 𝓕.i 𝓕.ν T₀ j b := by
    unfold torusModulus siegelModulus
    refine finprod_congr fun β => finprod_congr fun hβ => ?_
    rw [hroot β (positiveRelativeRoots_subset_relativeRoots _ _ hβ)]
  have hmain := hC x hx u hu hchamber ϖ hϖ
  rw [constantTerm_top, hpt, hmod] at hmain
  set y := z * positiveMap F G 𝓕.T 𝓕.i T₀ j b * ϖ with hydef
  have hlh1 : 1 ≤ adelicLogHeight F G rho y := by
    unfold adelicLogHeight
    have := Real.log_nonneg (le_max_left 1 (adelicSourceNorm F G rho y))
    linarith
  have hty : torusPoint (𝓕 := 𝓕) u = y * ϖ⁻¹ := by
    rw [hpt, hydef, mul_inv_cancel_right]
  have hpoly : 2 * (m : ℝ) * ‖Fr.crd u‖ + 3 ≤ c₁ * adelicLogHeight F G rho y := by
    have hy1 := one_le_adelicHeight F G rho hN y
    have hHϖ : adelicHeight F G rho ϖ⁻¹ ≤ H' := (hH ⟨ϖ, hϖ, rfl⟩).trans (le_max_right _ _)
    have hht : adelicHeight F G rho (torusPoint (𝓕 := 𝓕) u) ≤ adelicHeight F G rho y * H' := by
      rw [hty]
      exact (adelicHeight_mul_le F G rho hN _ _).trans
        (mul_le_mul_of_nonneg_left hHϖ (zero_le_one.trans hy1))
    have hlog1 : Real.log (adelicHeight F G rho (torusPoint (𝓕 := 𝓕) u)) ≤
        Real.log (adelicHeight F G rho y) + Real.log H' := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      have ht1 := one_le_adelicHeight F G rho hN (torusPoint (𝓕 := 𝓕) u)
      exact Real.log_le_log (by linarith) hht
    have hlog2 := log_adelicHeight_le rho hN y
    have hc := hcrd u hu
    have hcrd' : ‖Fr.crd u‖ ≤
        Ah * adelicLogHeight F G rho y + (Ah * (Real.log cN + Real.log H') + Bh) := by
      have : Real.log (adelicHeight F G rho (torusPoint (𝓕 := 𝓕) u)) ≤
          Real.log cN + adelicLogHeight F G rho y + Real.log H' := by linarith
      nlinarith
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hK0 : 0 ≤ Ah * (Real.log cN + Real.log H') + Bh := by
      have := Real.log_nonneg hcN1
      have := Real.log_nonneg hH'1
      positivity
    have step1 : 2 * (m : ℝ) * ‖Fr.crd u‖ + 3 ≤
        2 * (m : ℝ) * Ah * adelicLogHeight F G rho y + c₀ := by
      have := mul_le_mul_of_nonneg_left hcrd' (by positivity : (0 : ℝ) ≤ 2 * (m : ℝ))
      rw [hc₀def]
      nlinarith
    have step2 : c₀ ≤ c₀ * adelicLogHeight F G rho y := le_mul_of_one_le_right hc₀ hlh1
    rw [hc₁def]
    nlinarith
  calc ‖evaluate F G (f x).val y‖
      ≤ C * (2 * (m : ℝ) * ‖Fr.crd u‖ + 3) ^ (2 * m) *
          Real.sqrt (siegelModulus F G 𝓕.T 𝓕.i 𝓕.ν T₀ j b) := hmain
    _ ≤ C * (c₁ * adelicLogHeight F G rho y) ^ (2 * m) *
          Real.sqrt (siegelModulus F G 𝓕.T 𝓕.i 𝓕.ν T₀ j b) := by
        gcongr
    _ = C * c₁ ^ (2 * m) * Real.sqrt (siegelModulus F G 𝓕.T 𝓕.i 𝓕.ν T₀ j b) *
          adelicLogHeight F G rho y ^ (2 * m) := by
        rw [mul_pow]
        ring

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints PositiveRealTorus RepresentationGrowth AdelicSiegelFactors

/-- **The criterion for a trivial group.** If `rho` is a closed matrix embedding of size `0`,
then `G(𝔸)` is a point, and for a family with uniform moderate growth the bound holds with every
exponent. -/
theorem siegel_bound_of_size_zero {F : Type} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] {d : ℕ}
    (rho : MatrixRepresentation G (Fin 0)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (hrho : IsClosedSubgroup rho) {Ix : Type}
    (f : Ix → FinitePlotSmoothRationalFunctions F G) (S : Set Ix)
    (L : Subgroup (FiniteAdelicGroupPoints F G)) (R : ℝ)
    (hgrowth : IsUniformGrowthFamily rho hsmooth hcalc L R f S)
    {T T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) (j : T₀ ⟶ T) (t : ℝ≥0ˣ)
    (Ω : Set (AdelicGroupPoints F G)) (k : ℕ) :
    ∃ B : ℝ, ∀ x ∈ S, ∀ z ∈ RestrictionSplitCentre.canonicalSubgroup F G,
      ∀ b ∈ weakSimpleRootChamber F T₀ T j G i ν t, ∀ ϖ ∈ Ω,
        ‖evaluate F G (f x).val (z * positiveMap F G T i T₀ j b * ϖ)‖ ≤
          B * Real.sqrt (siegelModulus F G T i ν T₀ j b) *
            adelicLogHeight F G rho (z * positiveMap F G T i T₀ j b * ϖ) ^ k := by
  have : Subsingleton (AdelicGL F 0) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  have hsub : Subsingleton (AdelicGroupPoints F G) :=
    (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective.subsingleton
  have hinj : Function.Injective (map F T.toGrp G i) := by
    intro a a' h
    simp only [map_apply, GroupScheme.affinePointsTarget_apply] at h
    have := hi.isSplitSubtorus.mono
    have : Mono i.hom.hom := Over.mono_of_mono_left _
    exact (cancel_mono i.hom.hom).mp h
  have hTsub : Subsingleton (AdelicGroupPoints F T.toGrp) := hinj.subsingleton
  obtain ⟨M, hM⟩ := hgrowth.2 1
  refine ⟨max 0 (M * adelicSourceNorm F G rho 1 ^ R), fun x hx z _ b _ ϖ _ => ?_⟩
  set y := z * positiveMap F G T i T₀ j b * ϖ with hydef
  have hy : y = 1 := Subsingleton.elim _ _
  have h1 := hM x hx y
  rw [map_one, Module.End.one_apply] at h1
  have hsieg : siegelModulus F G T i ν T₀ j b = 1 := by
    unfold siegelModulus
    have hβ1 : ∀ β : characterLattice T, normCharacter F T₀ (j ≫ β) b = 1 := by
      intro β
      rw [normCharacter_pullback]
      have : pointMap F T₀.toGrp T.toGrp (Adeles F) (CommGroupScheme.groupHom j) b =
          (1 : AdelicGroupPoints F T.toGrp) := Subsingleton.elim _ _
      rw [this, map_one]
    simp [hβ1]
  have hlh : 1 ≤ adelicLogHeight F G rho y := by
    unfold adelicLogHeight
    have := Real.log_nonneg (le_max_left 1 (adelicSourceNorm F G rho y))
    linarith
  rw [hsieg, Real.sqrt_one, mul_one]
  calc ‖evaluate F G (f x).val y‖ ≤ M * adelicSourceNorm F G rho y ^ R := h1
    _ = M * adelicSourceNorm F G rho 1 ^ R := by rw [hy]
    _ ≤ max 0 (M * adelicSourceNorm F G rho 1 ^ R) := le_max_right _ _
    _ ≤ max 0 (M * adelicSourceNorm F G rho 1 ^ R) * adelicLogHeight F G rho y ^ k :=
        le_mul_of_one_le_right (le_max_left _ _) (one_le_pow₀ hlh)

/-- **The uniform temperedness criterion on Siegel sets** (Mœglin–Waldspurger 1995,
Lemma I.4.1; Delorme 2023, Proposition 3.6), from the comparison of half-modulus characters
with positive-root products (`HalfModulusRootProductStatement`). -/
theorem uniformTemperednessCriterion_of_halfModulusRootProduct
    (hHM : HalfModulusRootProductStatement.{0}) : UniformTemperednessCriterionStatement := by
  intro F _ _ G _ _ _ hG N d rho hsmooth hcalc hrho Ix f S L R m hL hgrowth hexp
  refine ⟨2 * m, ?_⟩
  intro T i ν T₀ j hsetup t Ω hΩ
  obtain ⟨hi, hν, -, -, -, -, -, -, Z₀, zc, hzc, -⟩ := id hsetup
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact siegel_bound_of_size_zero rho hsmooth hcalc hrho f S L R hgrowth i hi ν j t Ω (2 * m)
  · let 𝓕 : StandardParabolicFamily F G := StandardParabolicFamily.ofMaximalSplitTorus hG i hi ν hν
    let : Fintype (simpleRelativeRoots 𝓕.i 𝓕.ν) :=
      (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).fintype
    obtain ⟨Fr⟩ := StandardParabolicFamily.TorusFrame.nonempty (𝓕 := 𝓕)
    exact StandardParabolicFamily.siegel_bound_of_family (𝓕 := 𝓕) hHM Fr rho hsmooth hcalc hN
      hrho f S L R m hL hgrowth (fun J x hx => hexp 𝓕 J x hx) j zc hzc t Ω hΩ

end Langlands.Global

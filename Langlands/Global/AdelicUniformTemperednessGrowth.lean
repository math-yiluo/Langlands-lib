import Langlands.Global.AdelicUniformTemperednessInduction
import Langlands.Global.AdelicEisensteinUnitaryGrowthStatement
import Langlands.Global.AdelicUniformDirectionalGrowth

/-! # Growth of the constant terms of a family with uniform moderate growth

Let the height `‖g‖` be defined by a matrix representation of size `N > 0`. For a family with
uniform moderate growth of exponent `R` (`IsUniformGrowthFamily`), every derivative of every
constant term along a standard parabolic is bounded by `C ‖g‖^{max R 0}`
with `C` independent of the member of the family. At points `t ϖ` with `t` a positive point of
the maximal split torus and `ϖ` in a compact set, this is at most `M e^{K ‖t‖}`, where `‖t‖` is
the norm of the coordinates of `t` and `K` depends on neither the compact set nor the
derivative. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry NumberField Set
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints InfiniteAdelicGroupPoints PositiveRealTorus RepresentationGrowth
  Langlands.Geometry.Manifold

section DirectionalSub

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] {d : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom)

local notation "A" => AdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)

/-- A real right-orbit derivative word commutes with differences of functions that are smooth
on each archimedean slice. -/
theorem adelicIteratedDirectionalValue_sub (s : List W) (f₁ f₂ : A → ℂ) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    (∀ b : Gf, ContMDiff IG IC ∞ (fun y : G∞ => f₁ (pair F G y b))) →
    (∀ b : Gf, ContMDiff IG IC ∞ (fun y : G∞ => f₂ (pair F G y b))) →
    adelicIteratedDirectionalValue hG s (f₁ - f₂) =
      adelicIteratedDirectionalValue hG s f₁ - adelicIteratedDirectionalValue hG s f₂ := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  intro h₁ h₂
  let B := manifoldSmoothFunctions F G hG
  let d₀ (X : W) : Module.End ℂ B :=
    { toFun := fun h => ⟨groupDirectionalValue IG X h.val,
        contMDiff_groupDirectionalValue IG X h.prop⟩
      map_add' := fun h k => Subtype.ext (funext fun x =>
        groupDirectionalValue_add IG X h.prop k.prop x)
      map_smul' := fun c h => Subtype.ext (funext fun x =>
        groupDirectionalValue_const_smul IG X c h.prop x) }
  let D (s : List W) : Module.End ℂ B := s.foldr (fun X g => (d₀ X).comp g) LinearMap.id
  funext x
  rw [← pair_projections F G x]
  let b := finite F G x
  let a := infinite F G x
  have hslice (s : List W) (f : A → ℂ) (h : B) (heq : h.val = fun y => f (pair F G y b)) :
      (D s h).val = fun y => adelicIteratedDirectionalValue hG s f (pair F G y b) := by
    induction s with
    | nil => exact heq
    | cons X s ih =>
      funext y
      change groupDirectionalValue IG X (D s h).val y = _
      rw [adelicIteratedDirectionalValue_cons, adelicDirectionalValue_pair, ih]
  let fs₁ : B := ⟨fun y => f₁ (pair F G y b), h₁ b⟩
  let fs₂ : B := ⟨fun y => f₂ (pair F G y b), h₂ b⟩
  have hh : (fs₁ - fs₂).val = fun y => (f₁ - f₂) (pair F G y b) := rfl
  change adelicIteratedDirectionalValue hG s (f₁ - f₂) (pair F G a b) = _
  rw [← show (D s (fs₁ - fs₂)).val a = _ from congrFun (hslice s _ _ hh) a, map_sub]
  change (D s fs₁).val a - (D s fs₂).val a = _
  rw [congrFun (hslice s f₁ fs₁ rfl) a, congrFun (hslice s f₂ fs₂ rfl) a]
  rfl

end DirectionalSub

section Growth

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {𝓕 : StandardParabolicFamily F G}
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hG : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hG)

local notation "A" => AdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "Δ" => simpleRelativeRoots 𝓕.i 𝓕.ν

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- For a matrix representation of size `N > 0`, a power `R` of the source norm is bounded by
`c^{-R}` times the power `max R 0` of the height, where `c = N^{∑ mult}`. -/
theorem rpow_adelicSourceNorm_le (hN : 0 < N) (R : ℝ) (g : A) :
    adelicSourceNorm F G rho g ^ R ≤
      ((N : ℝ) ^ (∑ v : InfinitePlace F, v.mult)) ^ (-R) * adelicHeight F G rho g ^ max R 0 := by
  set c : ℝ := (N : ℝ) ^ (∑ v : InfinitePlace F, v.mult) with hcdef
  have hc : 0 < c := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hh := one_le_adelicHeight F G rho hN g
  have hs : adelicSourceNorm F G rho g = adelicHeight F G rho g / c := by
    rw [adelicHeight_eq_scalar_mul_sourceNorm, ← hcdef]
    field_simp
  rw [hs, Real.div_rpow (by linarith) hc.le, div_eq_mul_inv, ← Real.rpow_neg hc.le, mul_comm]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hh (le_max_left _ _))
    (Real.rpow_nonneg hc.le _)

/-- **Derivatives of constant terms of a uniform family.** Let the height be defined by a matrix
representation of size `N > 0`. For a family with uniform moderate growth of exponent `R` at an
open level, the constant term along every standard parabolic of
every member is smooth on archimedean slices, and each of its derivatives is bounded by
`C ‖g‖^{max R 0}` with one constant `C` for the whole family. -/
theorem constantTerm_family_growth (hN : 0 < N) {Ix : Type}
    (f : Ix → FinitePlotSmoothRationalFunctions F G) (S : Set Ix)
    (L : Subgroup Gf) (R : ℝ) (hL : IsOpen (L : Set Gf))
    (hgrowth : IsUniformGrowthFamily rho hG hcalc L R f S) (Q : Idx) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    (∀ x ∈ S, ∀ b : Gf, ContMDiff IG IC ∞
      (fun y : G∞ => 𝓕.constantTerm Q (evaluate F G (f x).val) (pair F G y b))) ∧
    ∀ s : List W, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ g : A,
      ‖adelicIteratedDirectionalValue hG s (𝓕.constantTerm Q (evaluate F G (f x).val)) g‖ ≤
        C * adelicHeight F G rho g ^ max R 0 := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  set c : ℝ := (N : ℝ) ^ (∑ v : InfinitePlace F, v.mult) with hcdef
  have hc : 0 < c := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  let φ (q : S) : A → ℂ := evaluate F G (f q.1).val
  have hf (q : S) : Continuous (φ q) := (f q.1).val.property
  have hfS (q : S) (b : Gf) : ContMDiff IG IC ∞ (fun y : G∞ => φ q (pair F G y b)) :=
    ((mem_finitePlotSmoothRationalSubrepresentation_iff_contMDiff F G hG (f q.1).val).mp
      (f q.1).prop).1 b
  have hfL (q : S) : ∀ l ∈ L, ∀ x, φ q (x * ofFinite F G l) = φ q x := by
    intro l hl x
    exact congrArg (fun z : FinitePlotSmoothRationalFunctions F G => evaluate F G z.val x)
      (hgrowth.1 q.1 q.2 l hl)
  have hU := (𝓕.isUnipotentRadical Q).isGeometricUnipotentRadical
  have hinv (q : S) (r : RationalGroupPoints F (𝓕.U Q)) (x : A) :
      φ q (map F (𝓕.U Q) G (𝓕.iU Q ≫ 𝓕.p Q) (rational F (𝓕.U Q) r) * x) = φ q x := by
    rw [map_rational]
    exact evaluate_rational_mul F G (f q.1).val _ x
  have hgrow : ∀ s : List W, ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : S) (x : A),
      ‖adelicIteratedDirectionalValue hG s (φ q) x‖ ≤
        C * adelicHeight F G rho x ^ max R 0 * (fun _ : S => (1 : ℝ)) q := by
    intro s
    obtain ⟨M, hM⟩ := hgrowth.2 (adelicDirectionalWordEnveloping hG s)
    refine ⟨max M 0 * c ^ (-R), mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hc.le _),
      fun q x => ?_⟩
    have h1 := hM q.1 q.2 x
    rw [evaluate_adelicDirectionalWordEnveloping hG hcalc s (f q.1)] at h1
    have hs0 : 0 ≤ adelicSourceNorm F G rho x ^ R :=
      Real.rpow_nonneg (adelicSourceNorm_pos F G rho hN x).le _
    calc ‖adelicIteratedDirectionalValue hG s (φ q) x‖
        ≤ M * adelicSourceNorm F G rho x ^ R := h1
      _ ≤ max M 0 * adelicSourceNorm F G rho x ^ R :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hs0
      _ ≤ max M 0 * (c ^ (-R) * adelicHeight F G rho x ^ max R 0) :=
          mul_le_mul_of_nonneg_left (rpow_adelicSourceNorm_le rho hN R x) (le_max_right _ _)
      _ = max M 0 * c ^ (-R) * adelicHeight F G rho x ^ max R 0 * (fun _ : S => (1 : ℝ)) q := by
          simp only [mul_one]
          ring
  have h := adelicConstantTermDirectionalGrowth (𝓕.iU Q ≫ 𝓕.p Q) hG rho hU.2.1 hU.2.2.1
    hU.2.2.2.1 hN L hL S φ (fun _ => 1) (fun _ => zero_le_one) hf hfS hinv hfL (max R 0)
    (le_max_right _ _) hgrow
  refine ⟨fun x hx b => h.2.1 ⟨x, hx⟩ b, fun s => ?_⟩
  obtain ⟨C, hC, hCs⟩ := h.2.2.2.2 s
  refine ⟨C, hC, fun x hx g => ?_⟩
  have := hCs ⟨x, hx⟩ g
  rw [mul_one] at this
  exact this

/-- For a matrix representation of size `N > 0` and `R' ≥ 0`, the powers `R'` of heights at
`t ϖ`, `ϖ` in a compact set, grow at most exponentially in the coordinates of `t`, with a
nonnegative rate independent of the compact set. -/
theorem exists_height_rpow_le [Fintype Δ] (Fr : TorusFrame 𝓕) (hN : 0 < N) (R' : ℝ) (hR' : 0 ≤ R') :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Ω : Set A, IsCompact Ω → ∃ M : ℝ, 0 ≤ M ∧
      ∀ u ∈ intrinsicSubgroup F 𝓕.T, ∀ k ∈ Ω,
        adelicHeight F G rho (torusPoint (𝓕 := 𝓕) u * k) ^ R' ≤
          M * Real.exp (K * ‖Fr.crd u‖) := by
  obtain ⟨Ch, r, hCh, hr, hh⟩ := Fr.exists_height_le rho hN
  refine ⟨r * R', mul_nonneg hr hR', fun Ω hΩ => ?_⟩
  obtain ⟨B, hB⟩ := (hΩ.image (continuous_adelicHeight F G rho hN)).bddAbove
  set B' := max 1 B with hB'def
  have hB'1 : 1 ≤ B' := le_max_left _ _
  refine ⟨(Ch * B') ^ R', Real.rpow_nonneg (by positivity) _, fun u hu k hk => ?_⟩
  have h1 : adelicHeight F G rho (torusPoint (𝓕 := 𝓕) u * k) ≤
      Ch * B' * Real.exp (r * ‖Fr.crd u‖) := by
    have hk' : adelicHeight F G rho k ≤ B' := (hB ⟨k, hk, rfl⟩).trans (le_max_right _ _)
    calc adelicHeight F G rho (torusPoint (𝓕 := 𝓕) u * k)
        ≤ adelicHeight F G rho (torusPoint (𝓕 := 𝓕) u) * adelicHeight F G rho k :=
          adelicHeight_mul_le F G rho hN _ _
      _ ≤ (Ch * Real.exp (r * ‖Fr.crd u‖)) * B' :=
          mul_le_mul (hh u hu) hk' (zero_le_one.trans (one_le_adelicHeight F G rho hN k))
            (by positivity)
      _ = Ch * B' * Real.exp (r * ‖Fr.crd u‖) := by ring
  calc adelicHeight F G rho (torusPoint (𝓕 := 𝓕) u * k) ^ R'
      ≤ (Ch * B' * Real.exp (r * ‖Fr.crd u‖)) ^ R' :=
        Real.rpow_le_rpow (zero_le_one.trans (one_le_adelicHeight F G rho hN _)) h1 hR'
    _ = (Ch * B') ^ R' * Real.exp (r * R' * ‖Fr.crd u‖) := by
        rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
        congr 2
        ring

/-- **Growth hypotheses of the induction.** Let the height be defined by a matrix representation
of size `N > 0`. For a family with uniform moderate growth, the
constant terms at `t ϖ` and the derivatives of the constant-term steps at `t k` grow at most
exponentially in the coordinates of `t`, uniformly in the member of the family, the standard
index and the simple root, with a rate for the derivatives independent of the compact set and
the order of differentiation. -/
theorem family_growth_bounds [Fintype Δ] (Fr : TorusFrame 𝓕) (hN : 0 < N) {Ix : Type}
    (f : Ix → FinitePlotSmoothRationalFunctions F G) (S : Set Ix)
    (L : Subgroup Gf) (R : ℝ) (hL : IsOpen (L : Set Gf))
    (hgrowth : IsUniformGrowthFamily rho hG hcalc L R f S) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    (∀ Ω : Set A, IsCompact Ω → ∃ M K : ℝ, 0 ≤ M ∧ 0 ≤ K ∧ ∀ J : Idx, ∀ x ∈ S,
      ∀ u ∈ intrinsicSubgroup F 𝓕.T, ∀ ϖ ∈ Ω,
        ‖𝓕.constantTerm J (evaluate F G (f x).val) (torusPoint (𝓕 := 𝓕) u * ϖ)‖ ≤
          M * Real.exp (K * ‖Fr.crd u‖)) ∧
    (∃ K : ℝ, 0 ≤ K ∧ ∀ Ω : Set A, IsCompact Ω → ∀ n : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ (J : Idx) (α : characterLattice 𝓕.T), ∀ x ∈ S, ∀ u ∈ intrinsicSubgroup F 𝓕.T,
      ∀ k ∈ Ω, ∀ s : List (Fin (Module.finrank ℝ W)), s.length = n →
        ‖adelicIteratedDirectionalValue hG (s.map (Module.finBasis ℝ W))
          (𝓕.constantTermStep J α (evaluate F G (f x).val)) (torusPoint (𝓕 := 𝓕) u * k)‖ ≤
            M * Real.exp (K * ‖Fr.crd u‖)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  have hIdx : Finite Idx :=
    (Set.Finite.finite_subsets (Set.toFinite (simpleRelativeRoots 𝓕.i 𝓕.ν))).to_subtype
  let : Fintype Idx := Fintype.ofFinite Idx
  have hCT := fun Q : Idx => constantTerm_family_growth rho hG hcalc hN f S L R hL hgrowth Q
  choose hsm hCT using hCT
  choose C hC0 hC using hCT
  obtain ⟨K, hK, hH⟩ := exists_height_rpow_le rho Fr hN (max R 0) (le_max_right _ _)
  refine ⟨fun Ω hΩ => ?_, ⟨K, hK, fun Ω hΩ n => ?_⟩⟩
  · obtain ⟨M₀, hM₀, hM⟩ := hH Ω hΩ
    refine ⟨(∑ Q : Idx, C Q []) * M₀, K, mul_nonneg (Finset.sum_nonneg fun Q _ => hC0 Q [])
      hM₀, hK, fun J x hx u hu ϖ hϖ => ?_⟩
    have h1 := hC J [] x hx (torusPoint (𝓕 := 𝓕) u * ϖ)
    rw [adelicIteratedDirectionalValue_nil] at h1
    have hle : C J [] ≤ ∑ Q : Idx, C Q [] :=
      Finset.single_le_sum (f := fun Q => C Q []) (fun Q _ => hC0 Q []) (Finset.mem_univ J)
    calc _ ≤ C J [] * adelicHeight F G rho (torusPoint (𝓕 := 𝓕) u * ϖ) ^ max R 0 := h1
      _ ≤ (∑ Q : Idx, C Q []) * (M₀ * Real.exp (K * ‖Fr.crd u‖)) :=
          mul_le_mul hle (hM u hu ϖ hϖ) (Real.rpow_nonneg (zero_le_one.trans
            (one_le_adelicHeight F G rho hN _)) _)
            (Finset.sum_nonneg fun Q _ => hC0 Q [])
      _ = _ := by ring
  · obtain ⟨M₀, hM₀, hM⟩ := hH Ω hΩ
    have hfin := List.finite_length_eq (Fin (Module.finrank ℝ W)) n
    set Ssum : ℝ := ∑ Q : Idx, ∑ s ∈ hfin.toFinset, C Q (s.map (Module.finBasis ℝ W)) with hSsum
    have hSsum0 : 0 ≤ Ssum := Finset.sum_nonneg fun Q _ => Finset.sum_nonneg fun s _ => hC0 Q _
    have hle (Q : Idx) (s : List (Fin (Module.finrank ℝ W))) (hs : s.length = n) :
        C Q (s.map (Module.finBasis ℝ W)) ≤ Ssum := by
      have h1 : C Q (s.map (Module.finBasis ℝ W)) ≤
          ∑ s ∈ hfin.toFinset, C Q (s.map (Module.finBasis ℝ W)) :=
        Finset.single_le_sum (f := fun s => C Q (s.map (Module.finBasis ℝ W)))
          (fun s _ => hC0 Q _) (hfin.mem_toFinset.mpr hs)
      exact h1.trans (Finset.single_le_sum
        (f := fun Q => ∑ s ∈ hfin.toFinset, C Q (s.map (Module.finBasis ℝ W)))
        (fun Q _ => Finset.sum_nonneg fun s _ => hC0 Q _) (Finset.mem_univ Q))
    refine ⟨2 * Ssum * M₀, by positivity, fun J α x hx u hu k hk s hs => ?_⟩
    let J' := 𝓕.removeSimpleRoot J α
    have hsub := adelicIteratedDirectionalValue_sub hG (s.map (Module.finBasis ℝ W))
      (𝓕.constantTerm J (evaluate F G (f x).val)) (𝓕.constantTerm J' (evaluate F G (f x).val))
      (hsm J x hx) (hsm J' x hx)
    have hHt := hM u hu k hk
    have hpos : 0 ≤ adelicHeight F G rho (torusPoint (𝓕 := 𝓕) u * k) ^ max R 0 :=
      Real.rpow_nonneg (zero_le_one.trans (one_le_adelicHeight F G rho hN _)) _
    have e1 := hC J (s.map (Module.finBasis ℝ W)) x hx (torusPoint (𝓕 := 𝓕) u * k)
    have e2 := hC J' (s.map (Module.finBasis ℝ W)) x hx (torusPoint (𝓕 := 𝓕) u * k)
    change ‖adelicIteratedDirectionalValue hG (s.map (Module.finBasis ℝ W))
      (𝓕.constantTerm J (evaluate F G (f x).val) - 𝓕.constantTerm J' (evaluate F G (f x).val))
      (torusPoint (𝓕 := 𝓕) u * k)‖ ≤ _
    rw [hsub, Pi.sub_apply]
    calc _ ≤ ‖adelicIteratedDirectionalValue hG (s.map (Module.finBasis ℝ W))
            (𝓕.constantTerm J (evaluate F G (f x).val)) (torusPoint (𝓕 := 𝓕) u * k)‖ +
          ‖adelicIteratedDirectionalValue hG (s.map (Module.finBasis ℝ W))
            (𝓕.constantTerm J' (evaluate F G (f x).val)) (torusPoint (𝓕 := 𝓕) u * k)‖ :=
          norm_sub_le _ _
      _ ≤ Ssum * adelicHeight F G rho (torusPoint (𝓕 := 𝓕) u * k) ^ max R 0 +
          Ssum * adelicHeight F G rho (torusPoint (𝓕 := 𝓕) u * k) ^ max R 0 :=
          add_le_add (e1.trans (mul_le_mul_of_nonneg_right (hle J s hs) hpos))
            (e2.trans (mul_le_mul_of_nonneg_right (hle J' s hs) hpos))
      _ = 2 * Ssum * adelicHeight F G rho (torusPoint (𝓕 := 𝓕) u * k) ^ max R 0 := by ring
      _ ≤ 2 * Ssum * (M₀ * Real.exp (K * ‖Fr.crd u‖)) :=
          mul_le_mul_of_nonneg_left hHt (by positivity)
      _ = _ := by ring

end Growth

end Langlands.Global.StandardParabolicFamily

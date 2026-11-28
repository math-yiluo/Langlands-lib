import Langlands.Global.AdelicNormOneCuspidalFamilyRapidDecay

/-! # Cuspidal rapid decay on norm-one representatives, uniformly in compact right translates -/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj Manifold ContDiff NNReal Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints InfiniteAdelicGroupPoints AdelicSiegelFactors
  RepresentationGrowth Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] {N d : ℕ}
  (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "A" => AdelicGroupPoints F G
local notation "A∞" => InfiniteAdelicGroupPoints F G
local notation "Af" => FiniteAdelicGroupPoints F G

private theorem StandardParabolicFamily.isCuspidalAlong_top_of_constantTerms'
    (P : StandardParabolicFamily F G) {f : A → ℂ}
    (hf : ArthurTruncation.HasCuspidalConstantTerms f) : P.IsCuspidalAlong P.top f := by
  intro Q hQ
  have hproper : SubgroupFunctor.range (P.p Q) ≠ ⊤ := by
    intro htop
    have hle : SubgroupFunctor.range (P.p P.top) ≤ SubgroupFunctor.range (P.p Q) := by
      rw [htop]
      intro Z a _
      trivial
    exact (not_le_of_gt hQ) ((P.le_iff_range_le P.top Q).mpr hle)
  exact hf _ _ (P.p Q) (P.iU Q) (P.isCompatible Q).parabolic (P.isUnipotentRadical Q) hproper

private theorem StandardParabolicFamily.map_top_radical_eq_one'
    (P : StandardParabolicFamily F G) (x : AdelicGroupPoints F (P.U P.top)) :
    map F (P.U P.top) G (P.iU P.top ≫ P.p P.top) x = 1 := by
  have hm : map F (P.U P.top) G (P.iU P.top ≫ P.p P.top) x ∈
      (SubgroupFunctor.range (P.iU P.top ≫ P.p P.top)).carrier _ := ⟨x, rfl⟩
  rw [P.range_radical_eq_standardUnipotent] at hm
  change _ ∈ (standardUnipotent P.i P.ν (simpleRelativeRoots P.i P.ν)).carrier _ at hm
  rw [standardUnipotent_simple_eq_bot] at hm
  exact Subgroup.mem_bot.mp hm

set_option maxHeartbeats 800000 in
/-- The norm-one quotient admits a common set of representatives `S` with the following
property. For every compact set `Bc` of right translations, every family with vanishing
proper constant terms and uniform derivative growth is rapidly decreasing at the points
`x y` with `x ∈ S` and `y ∈ Bc`, measured by the height of `x`, with one constant for the
whole family. The proof is that of `adelicNormOneCuspidalFamilyRapidDecay`, with the compact
right factor of the Siegel set enlarged by `Bc`. -/
theorem adelicNormOneCuspidalFamilyTranslateDecay (hG : IsConnectedReductive G) (hN : 0 < N) :
    ∃ S : Set A, S ⊆ (normOneSubgroup F G : Set A) ∧
      (∀ x : normOneSubgroup F G, ∃ q : RationalGroupPoints F G, rational F G q * x.val ∈ S) ∧
      letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      ∀ (Bc : Set A), IsCompact Bc →
      ∀ L : OpenSubgroup Af, ∀ (B : Type v) (f : B → A → ℂ) (s : B → ℝ),
      (∀ b, 0 ≤ s b) → (∀ b, Continuous (f b)) →
      (∀ b c, ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (fun x : A∞ => f b (pair F G x c))) →
      (∀ b, IsLeftInvariantUnder F G (rationalSubgroup F G) (f b)) →
      (∀ b, ∀ l ∈ L.toSubgroup, ∀ x, f b (x * ofFinite F G l) = f b x) →
      (∀ b, ArthurTruncation.HasCuspidalConstantTerms (f b)) →
      ∀ R : ℝ, 0 ≤ R →
      (∀ w : List (smoothModel F d), ∃ C : ℝ, 0 ≤ C ∧ ∀ b x,
        ‖adelicIteratedDirectionalValue hsmooth w (f b) x‖ ≤
          C * adelicHeight F G rho x ^ R * s b) →
      ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ b x, x ∈ S → ∀ y ∈ Bc,
        ‖f b (x * y)‖ * adelicHeight F G rho x ^ m ≤ C * s b := by
  classical
  obtain ⟨T, i, nu, T₀, j, hS, C, t, W, hW, hcover⟩ :=
    hasFiniteRightSiegelCover_of_connectedReductive F G hG
  let D := canonicalStandardFactors F G T i nu
  let S₀ := weakSiegelProduct F G T i nu D C T₀ j t
  let S : Set A := (S₀ * W) ∩ normOneSubgroup F G
  refine ⟨S, Set.inter_subset_right, ?_, ?_⟩
  · intro x
    obtain ⟨q, hq⟩ := hcover x
    exact ⟨q, hq, (normOneSubgroup F G).mul_mem (rationalNormOne F G q).property x.property⟩
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  intro Bc hBc L B f s hs hf hfS hfR hfL hfC R hR hGrowth m
  let P := StandardParabolicFamily.ofMaximalSplitTorus hG i hS.1 nu hS.2.1
  let B₀ : StandardIndex F G P.i P.ν := ⟨∅, Set.empty_subset _⟩
  have hT₀ : IsSplitTorus T₀.toGrp := by
    obtain ⟨_, _, _, _, ht₀, _⟩ := hS.2.2.2.2.2.2.2.1
    exact ht₀.1.1
  have hspan : Langlands.LinearAlgebra.RationalSpan.ratSpan
      (((fun a : characterLattice P.T => j ≫ a) '' simpleRelativeRoots P.i P.ν) ∪ ∅) = ⊤ := by
    rw [Set.union_empty]
    exact ratSpan_restrict_simpleRelativeRoots_eq_top relativeRootNegation
      relativeCharacterRootComplement hG hS
  let Ω := compactPrefix F G T i nu D C
  let K := (C.compactSubgroup : Set A) * W * Bc
  have hΩ : IsCompact Ω := isCompact_compactPrefix F G T i nu D C
  have hK : IsCompact K := (C.compact_compactSubgroup.mul hW.isCompact).mul hBc
  have hΩP : Ω ⊆ (map F (P.P B₀) G (P.p B₀)).toMonoidHom.range := by
    rintro _ ⟨_, ⟨n, _, rfl⟩, _, ⟨md, _, rfl⟩, rfl⟩
    exact (standardParabolicImage F G T i nu).mul_mem
      (standardUnipotentImage_le_parabolic F G T i nu ⟨n, rfl⟩)
      (standardLeviImage_le_parabolic F G T i nu ⟨md.val, rfl⟩)
  obtain ⟨Ωf, hΩf, hSf⟩ := exists_isCompact_finite_weakSiegelProduct F G T i nu T₀ j hT₀ D C t
  let Y := Ωf * (finite F G '' W) * (finite F G '' Bc)
  have hY : IsCompact Y := (hΩf.mul (hW.isCompact.image (finite F G).continuous)).mul
    (hBc.image (finite F G).continuous)
  have hRat (b : B) : ∀ r ∈ rationalImage F (P.p B₀), ∀ x, f b (r * x) = f b x := by
    intro r hr x
    obtain ⟨q, rfl⟩ := (mem_rationalImage_iff _ _).mp hr
    rw [map_rational]
    exact hfR b _ ⟨_, rfl⟩ x
  have hU (b : B) (u : AdelicGroupPoints F (P.U P.top)) (x : A) :
      f b (map F (P.U P.top) G (P.iU P.top ≫ P.p P.top) u * x) = f b x := by
    rw [P.map_top_radical_eq_one', one_mul]
  obtain ⟨c, hc, hdecay⟩ :=
    StandardParabolicFamily.adelicRelativeCuspidalRapidDecay (𝓕 := P) j hsmooth rho hT₀ hN
      P.top ∅ hspan t 0 le_rfl Ω K hΩ hK hΩP Y hY L.toSubgroup L.isOpen
      B f s hs hf hfS hRat hU hfL
      (fun b => P.isCuspidalAlong_top_of_constantTerms' (hfC b)) R hR hGrowth m
  obtain ⟨Mb, hMb⟩ := (hBc.inv.image (continuous_adelicHeight F G rho hN)).bddAbove
  let M : ℝ := max 1 Mb
  have hM : 1 ≤ M := le_max_left _ _
  have hHpos (z : A) : 0 ≤ adelicHeight F G rho z :=
    zero_le_one.trans (one_le_adelicHeight F G rho hN z)
  refine ⟨M ^ m * c, mul_nonneg (pow_nonneg (zero_le_one.trans hM) _) hc,
    fun b x hx z hz => ?_⟩
  obtain ⟨y, hy, w, hw, rfl⟩ := hx.1
  have hfy : finite F G (y * w * z) ∈ Y := by
    rw [map_mul, map_mul]
    exact ⟨_, ⟨_, hSf y hy, _, ⟨w, hw, rfl⟩, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩
  change y ∈ (Ω * (positiveMap F G T i T₀ j ''
    PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i nu t)) * C.compactSubgroup at hy
  obtain ⟨_, ⟨p, hp, _, ⟨a, ha, rfl⟩, rfl⟩, k, hk, rfl⟩ := hy
  have hY' : finite F G (p * positiveMap F G T i T₀ j a * (k * w * z)) ∈ Y := by
    simpa only [mul_assoc] using hfy
  have hdec := hdecay b p hp a ha (fun _ h => h.elim)
    (fun _ h => (h.2 h.1).elim) (k * w * z) ⟨k * w, ⟨k, hk, w, hw, rfl⟩, z, hz, rfl⟩ hY'
  set x := p * positiveMap F G T i T₀ j a * k * w with hxdef
  have hxz : x * z = p * positiveMap F G T i T₀ j a * (k * w * z) := by
    simp only [hxdef, mul_assoc]
  have hdec' : ‖f b (x * z)‖ * adelicHeight F G rho (x * z) ^ m ≤ c * s b := by
    rw [hxz]
    exact hdec
  have hHx : adelicHeight F G rho x ≤ M * adelicHeight F G rho (x * z) := by
    calc adelicHeight F G rho x = adelicHeight F G rho (x * z * z⁻¹) := by
          rw [mul_inv_cancel_right]
      _ ≤ adelicHeight F G rho (x * z) * adelicHeight F G rho z⁻¹ :=
          adelicHeight_mul_le F G rho hN _ _
      _ ≤ adelicHeight F G rho (x * z) * M := by
          apply mul_le_mul_of_nonneg_left _ (hHpos _)
          exact (hMb ⟨z⁻¹, by simpa using hz, rfl⟩).trans (le_max_right _ _)
      _ = M * adelicHeight F G rho (x * z) := mul_comm _ _
  calc ‖f b (x * z)‖ * adelicHeight F G rho x ^ m
      ≤ ‖f b (x * z)‖ * (M * adelicHeight F G rho (x * z)) ^ m := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact pow_le_pow_left₀ (hHpos _) hHx m
    _ = M ^ m * (‖f b (x * z)‖ * adelicHeight F G rho (x * z) ^ m) := by ring
    _ ≤ M ^ m * (c * s b) :=
        mul_le_mul_of_nonneg_left hdec' (pow_nonneg (zero_le_one.trans hM) _)
    _ = M ^ m * c * s b := by ring

end Langlands.Global

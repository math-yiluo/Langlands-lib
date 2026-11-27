import Langlands.Global.AdelicRelativeCuspidalRapidDecay
import Langlands.Global.AdelicPositiveTorusSplitComponentProof
import Langlands.Global.AdelicLocalFinitenessGroupData
import Langlands.Global.AdelicConstantTermSplitComponent
import Langlands.Global.AdelicRationalHeightReduction

/-! # Maximal-parabolic decay on Levi Siegel regions, by a split-component shift

The decay of Mœglin–Waldspurger I.2.10 along a maximal parabolic of the Levi `M_J`, on regions
where only the simple roots of `J` are bounded below, and the resulting rapid decay of cuspidal
functions along `J` on Levi Siegel regions. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory NumberField Set TensorProduct
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.LinearAlgebra.RationalSpan
  AdelicGroupPoints InfiniteAdelicGroupPoints PositiveRealTorus AdelicSiegelFactors
  RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "A" => AdelicGroupPoints F G
local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "Δ" => simpleRelativeRoots 𝓕.i 𝓕.ν
local notation "aG" => positiveMap F G 𝓕.T 𝓕.i 𝓕.T (𝟙 𝓕.T)

/-- For a standard index `J` and a positive torus point `a` whose roots in `J` are at least `b`,
there is a positive split-component point `s` of `P_J` whose image in `G(𝔸)` is a positive torus
point `sT`, trivial on the roots of `J`, such that `sT a` lies in the weak simple-root chamber
with threshold `b`. -/
theorem exists_splitComponent_shift (J : Idx) (b : ℝ≥0ˣ) (a : intrinsicSubgroup F 𝓕.T)
    (ha : ∀ ρ₁ ∈ J.1, b ≤ normCharacter F 𝓕.T ρ₁ a) :
    ∃ s ∈ 𝓕.positiveSplitComponent J, ∃ sT : intrinsicSubgroup F 𝓕.T,
      map F (𝓕.P J) G (𝓕.p J) s = aG sT ∧
      (∀ ρ₁ ∈ J.1, normCharacter F 𝓕.T ρ₁ sT = 1) ∧
      sT * a ∈ weakSimpleRootChamber F 𝓕.T 𝓕.T (𝟙 𝓕.T) G 𝓕.i 𝓕.ν b := by
  obtain ⟨ζ, hζ, -, -⟩ := (𝓕.isCompatible J).realization
  have hT : IsSplitTorus 𝓕.T.toGrp := 𝓕.maximalSplit.1.1
  have hΔ : (simpleRelativeRoots 𝓕.i 𝓕.ν).Finite :=
    𝓕.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots 𝓕.i 𝓕.ν
  let lg : characterLattice 𝓕.T → ℝ := fun ρ₁ => Real.log ((normCharacter F 𝓕.T ρ₁ a : ℝ≥0) : ℝ)
  let t : ℝ := ∑ ρ₁ ∈ hΔ.toFinset, max 0 (Real.log ((b : ℝ≥0) : ℝ) - lg ρ₁)
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun _ _ => le_max_left _ _
  have htρ (ρ₁ : characterLattice 𝓕.T) (hρ : ρ₁ ∈ simpleRelativeRoots 𝓕.i 𝓕.ν) :
      Real.log ((b : ℝ≥0) : ℝ) - lg ρ₁ ≤ t :=
    (le_max_right _ _).trans (Finset.single_le_sum (f := fun ρ₁ =>
      max 0 (Real.log ((b : ℝ≥0) : ℝ) - lg ρ₁)) (fun _ _ => le_max_left _ _)
      (hΔ.mem_toFinset.mpr hρ))
  obtain ⟨x, hx, hlog⟩ := exists_characterLog_eq hT (cocharacterFunctional (t ⊗ₜ[ℤ] ζ))
  let sT : intrinsicSubgroup F 𝓕.T := ⟨x, hx⟩
  have hlogx (ρ₁ : characterLattice 𝓕.T) :
      characterLog F 𝓕.T.toGrp x ρ₁ = t * (latticePairing 𝓕.T ρ₁ ζ : ℝ) := by
    have h := congrArg (fun ℓ : RealCharacterDual F 𝓕.T.toGrp => ℓ ρ₁) hlog
    simpa only [cocharacterFunctional_apply, pair_tmul_tmul, one_mul] using h
  have hnorm (ρ₁ : characterLattice 𝓕.T) :
      Real.log ((normCharacter F 𝓕.T ρ₁ sT : ℝ≥0) : ℝ) = t * (latticePairing 𝓕.T ρ₁ ζ : ℝ) :=
    hlogx ρ₁
  have hJ1 (ρ₁ : characterLattice 𝓕.T) (hρ : ρ₁ ∈ J.1) : characterLog F 𝓕.T.toGrp x ρ₁ = 0 := by
    rw [hlogx, hζ.2.1 ρ₁ hρ, Int.cast_zero, mul_zero]
  have hnorm1 (ρ₁ : characterLattice 𝓕.T) (hρ : ρ₁ ∈ J.1) :
      normCharacter F 𝓕.T ρ₁ sT = 1 := by
    have h0 : Real.log ((normCharacter F 𝓕.T ρ₁ sT : ℝ≥0) : ℝ) = 0 := hJ1 ρ₁ hρ
    have hpos : (0 : ℝ) < ((normCharacter F 𝓕.T ρ₁ sT : ℝ≥0) : ℝ) := by
      exact_mod_cast (normCharacter F 𝓕.T ρ₁ sT).ne_zero.bot_lt
    exact Units.ext (NNReal.eq (by simpa using Real.eq_one_of_pos_of_log_eq_zero hpos h0))
  obtain ⟨s, hs, hsmap⟩ := positiveTorusSplitComponent F G 𝓕 J x hx
    (fun β hβ => characterValue_eq_one_of_characterLog_eq_zero hx (hJ1 β hβ))
  refine ⟨s, hs, sT, ?_, hnorm1, ?_⟩
  · rw [hsmap]
    change _ = map F 𝓕.T.toGrp G (CommGroupScheme.groupHom (𝟙 𝓕.T) ≫ 𝓕.i) x
    rw [show CommGroupScheme.groupHom (𝟙 𝓕.T) = 𝟙 𝓕.T.toGrp from rfl, Category.id_comp]
  · intro ρ₁ hρ
    rw [Category.id_comp, Subgroup.coe_mul, map_mul]
    show b ≤ _
    by_cases hρJ : ρ₁ ∈ J.1
    · rw [hnorm1 ρ₁ hρJ, one_mul]
      exact ha ρ₁ hρJ
    · have hpair : (1 : ℝ) ≤ (latticePairing 𝓕.T ρ₁ ζ : ℝ) := by
        exact_mod_cast hζ.2.2 ρ₁ hρ hρJ
      have hb0 : (0 : ℝ) < ((b : ℝ≥0) : ℝ) := by exact_mod_cast b.ne_zero.bot_lt
      have hs0 : (0 : ℝ) < ((normCharacter F 𝓕.T ρ₁ sT : ℝ≥0) : ℝ) := by
        exact_mod_cast (normCharacter F 𝓕.T ρ₁ sT).ne_zero.bot_lt
      have ha0 : (0 : ℝ) < ((normCharacter F 𝓕.T ρ₁ a : ℝ≥0) : ℝ) := by
        exact_mod_cast (normCharacter F 𝓕.T ρ₁ a).ne_zero.bot_lt
      have hle : Real.log ((b : ℝ≥0) : ℝ) ≤
          Real.log (((normCharacter F 𝓕.T ρ₁ sT : ℝ≥0) : ℝ) *
            ((normCharacter F 𝓕.T ρ₁ a : ℝ≥0) : ℝ)) := by
        rw [Real.log_mul hs0.ne' ha0.ne', hnorm]
        have h1 := htρ ρ₁ hρ
        have h2 : t ≤ t * (latticePairing 𝓕.T ρ₁ ζ : ℝ) := le_mul_of_one_le_right ht0 hpair
        dsimp only [lg] at h1
        linarith
      have hle' := (Real.log_le_log_iff hb0 (mul_pos hs0 ha0)).mp hle
      change ((b : ℝ≥0) : ℝ) ≤ _ at hle'
      exact Units.val_le_val.mp (by exact_mod_cast hle')

/-- The adelic image of a standard parabolic lies in the image of every larger one. -/
theorem range_map_le_of_le {Q P : Idx} (h : Q ≤ P) :
    (map F (𝓕.P Q) G (𝓕.p Q)).toMonoidHom.range ≤ (map F (𝓕.P P) G (𝓕.p P)).toMonoidHom.range := by
  let S := (algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F (Adeles F)))
  change (SubgroupFunctor.range (𝓕.p Q)).carrier S ≤ (SubgroupFunctor.range (𝓕.p P)).carrier S
  exact (𝓕.le_iff_range_le Q P).mp h S

/-- For a function left invariant under the adelic radical of `P_J`, a positive split-component
point of `P_J` and a point of `P_J(𝔸)` may be interchanged on the left. -/
theorem IsRadicalInvariant.splitComponent_mul_comm {J : Idx} {f : A → ℂ}
    (hf : 𝓕.IsRadicalInvariant J f) (s : 𝓕.positiveSplitComponent J) {x : A}
    (hx : x ∈ (map F (𝓕.P J) G (𝓕.p J)).toMonoidHom.range) (g : A) :
    f (map F (𝓕.P J) G (𝓕.p J) s * (x * g)) = f (x * (map F (𝓕.P J) G (𝓕.p J) s * g)) := by
  obtain ⟨y, rfl⟩ := hx
  have hxP : map F (𝓕.P J) G (𝓕.p J) y ∈ (SubgroupFunctor.range (𝓕.p J)).carrier _ :=
    SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
  obtain ⟨a', -, ha'⟩ := s.2
  have hcomm := 𝓕.commutator_mem_radical_of_splitComponent J _ a' hxP
  let b := map F (𝓕.P J) G (𝓕.p J) s
  let x := map F (𝓕.P J) G (𝓕.p J) y
  have haG : b = map F (𝓕.A J).toGrp G (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J) a' := by
    change map F (𝓕.A J).toGrp (𝓕.P J) (𝓕.a J ≫ 𝓕.l J) a' =
      (s : AdelicGroupPoints F (𝓕.P J)) at ha'
    change map F (𝓕.P J) G (𝓕.p J) s = _
    rw [← ha', ← map_comp_apply_of_hom, Category.assoc]
  let u : AdelicSubgroupPoints.adelicPoints F G
      (SubgroupFunctor.range (𝓕.iU J ≫ 𝓕.p J)) :=
    ⟨x * b * x⁻¹ * b⁻¹, by rw [haG]; exact hcomm⟩
  have heq : x * (b * g) = (u : A) * (b * (x * g)) := by
    change x * (b * g) = x * b * x⁻¹ * b⁻¹ * (b * (x * g))
    group
  change f (b * (x * g)) = f (x * (b * g))
  rw [heq, hf u]

section Decay

variable {d N : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom) (rho : MatrixRepresentation G (Fin N))

local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "Jw" => Fin (Module.finrank ℝ W)
local notation "basisG" => Module.finBasis ℝ W
local notation "B₀" => (Subtype.mk ∅ (empty_subset (simpleRelativeRoots 𝓕.i 𝓕.ν)) : Idx)
local notation "height" => adelicHeight F G rho

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Right-orbit derivative words commute with left translation. -/
theorem adelicIteratedDirectionalValue_leftTranslate (s : List W) (f : A → ℂ) (c x : A) :
    adelicIteratedDirectionalValue hG s (fun y => f (c * y)) x =
      adelicIteratedDirectionalValue hG s f (c * x) := by
  induction s generalizing x with
  | nil => rfl
  | cons X s ih =>
    simp only [adelicIteratedDirectionalValue_cons]
    have h : adelicIteratedDirectionalValue hG s (fun y => f (c * y)) =
        fun y => adelicIteratedDirectionalValue hG s f (c * y) := funext ih
    rw [h]
    unfold adelicDirectionalValue
    simp only [mul_assoc]

/-- **Maximal-parabolic decay on a relative chamber.** Let `J` be a standard index and
`β ∈ J`. For a continuous function `f` on `G(𝔸)`, smooth on the archimedean slices, left
invariant under `P_0(F)` and `U_J(𝔸)`, right invariant under an open finite level, whose
constant term along `J \ {β}` vanishes and whose derivative words of order `n` are bounded by
`M_w · ht(x)^R`, the value at `p a k` (with `p` in a compact subset of `P_0(𝔸)`, `a` a positive
torus point whose roots in `J` are at least `b`, `k` in a compact set and the finite part of
`p a k` in a compact set) is at most `C |β(a)|^{-n/[F:ℚ]} M_w ht(a)^R`, with `C` independent of
`f`. The chamber condition is required only for the roots in `J`: the point is first moved into
the weak simple-root chamber of `G` by a positive split-component point `s` of `P_J`, trivial on
the roots of `J`, and the decay of the published `adelicMaximalUnipotentDecay` is applied to the
left translate `f(s⁻¹ ·)`. Left `U_J(𝔸)`-invariance lets `s` pass every point of `P_J(𝔸)`. -/
theorem shiftedMaximalDecay (hN : 0 < N) (J : Idx) {β : characterLattice 𝓕.T} (hβ : β ∈ J.1)
    (b : ℝ≥0ˣ) (n : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (Ω K : Set A) (hΩ : IsCompact Ω) (hK : IsCompact K)
    (hΩP : Ω ⊆ ((map F (𝓕.P B₀) G (𝓕.p B₀)).toMonoidHom.range : Set A))
    (Yf : Set Gf) (hYf : IsCompact Yf) (L : Subgroup Gf) (hL : IsOpen (L : Set Gf)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : A → ℂ), Continuous f →
      (∀ c : Gf, ContMDiff IG IC ∞ (fun y : G∞ => f (pair F G y c))) →
      (∀ r ∈ rationalImage F (𝓕.p B₀), ∀ x, f (r * x) = f x) →
      𝓕.IsRadicalInvariant J f →
      (∀ l ∈ L, ∀ x, f (x * ofFinite F G l) = f x) →
      𝓕.constantTerm (𝓕.removeSimpleRoot J β) f = 0 →
      ∀ Mw : ℝ, 0 ≤ Mw →
      (∀ s : List Jw, s.length = n → ∀ x,
        ‖adelicIteratedDirectionalValue hG (s.map basisG) f x‖ ≤ Mw * height x ^ R) →
      ∀ p ∈ Ω, ∀ a : intrinsicSubgroup F 𝓕.T, (∀ ρ₁ ∈ J.1, b ≤ normCharacter F 𝓕.T ρ₁ a) →
      ∀ k ∈ K, finite F G (p * aG a * k) ∈ Yf →
      ‖f (p * aG a * k)‖ ≤
        C * relativeCharacterDecay (𝟙 𝓕.T) β a ^ n * Mw * height (aG a) ^ R := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  let M := 𝓕.omitSimpleRoot β
  let j := 𝓕.iU M ≫ 𝓕.p M
  let hgeom := (𝓕.isUnipotentRadical M).isGeometricUnipotentRadical
  obtain ⟨dU, hU⟩ := Classical.indefiniteDescription _
    (Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension (𝓕.U M).X.left _
      (𝓕.U M).X.hom hgeom.2.1 hgeom.2.2.1)
  obtain ⟨K', hK', hKK', Cd, hCd, hiter⟩ :=
    adelicMaximalUnipotentDecay hG (dU := dU) 𝓕.i 𝓕.ν (𝟙 𝓕.T) j
      𝓕.connectedReductive 𝓕.maximalSplit 𝓕.generic hU hgeom.2.2.1 hgeom.2.2.2.1
      β (J.2 hβ) (𝓕.range_radical_eq_standardUnipotent M) Ω hΩ
      (fun _ hp => 𝓕.minimalParabolic_adelicImage_le_normalizer_radical M (hΩP hp))
      Yf hYf L hL b n K hK
  obtain ⟨E, hE1, hE⟩ := exists_compact_factors_height_bound rho hN Ω K' hΩ hK'
  refine ⟨Cd * E ^ R, mul_nonneg hCd (Real.rpow_nonneg (zero_le_one.trans hE1) _), ?_⟩
  intro f hf hfS hfR hfU hfL hCT Mw hMw hW p hp a ha k hk hx
  have hT : IsSplitTorus 𝓕.T.toGrp := 𝓕.maximalSplit.1.1
  obtain ⟨s, hs, sT, hsmap, hsT1, hch⟩ := 𝓕.exists_splitComponent_shift J b a ha
  let s' : 𝓕.positiveSplitComponent J := ⟨s⁻¹, (𝓕.positiveSplitComponent J).inv_mem hs⟩
  let S := map F (𝓕.P J) G (𝓕.p J) s
  have hS' : map F (𝓕.P J) G (𝓕.p J) s'.1 = S⁻¹ := map_inv _ _
  let fs : A → ℂ := 𝓕.unnormalizedAction J s'.1 f
  have hfs (y : A) : fs y = f (S⁻¹ * y) := by
    change f (map F (𝓕.P J) G (𝓕.p J) s'.1 * y) = _
    rw [hS']
  have hB₀J : B₀ ≤ J := empty_subset _
  have hfsR : ∀ r ∈ rationalImage F (𝓕.p B₀), ∀ x, fs (r * x) = fs x := by
    intro r hr x
    have hrP : r ∈ (map F (𝓕.P J) G (𝓕.p J)).toMonoidHom.range := by
      obtain ⟨q, rfl⟩ := hr
      exact 𝓕.range_map_le_of_le hB₀J ⟨rational F (𝓕.P B₀) q, rfl⟩
    have h := IsRadicalInvariant.splitComponent_mul_comm 𝓕 hfU s' hrP x
    change f (map F (𝓕.P J) G (𝓕.p J) s'.1 * (r * x)) = f (map F (𝓕.P J) G (𝓕.p J) s'.1 * x)
    rw [h, hfR r hr]
  have hfsU : ∀ u : AdelicGroupPoints F (𝓕.U J), ∀ x,
      fs (map F (𝓕.U J) G (𝓕.iU J ≫ 𝓕.p J) u * x) = fs x := fun u x =>
    (IsRadicalInvariant.unnormalizedAction 𝓕 hfU s') ⟨_, SubgroupFunctor.mem_range.mpr ⟨u, rfl⟩⟩ x
  have hfsC : Continuous fs := hf.comp (continuous_const.mul continuous_id)
  have hCTs : subgroupConstantTerm F j fs = 0 := by
    have h1 := adelicRelativeCuspidalConstantTerm 𝓕 J β hβ fs hfsC hfsR hfsU
    have h2 := 𝓕.constantTerm_unnormalizedAction_of_radicalInvariant
      (Q := 𝓕.removeSimpleRoot J β) inter_subset_left s' hfU
    change 𝓕.constantTerm (𝓕.omitSimpleRoot β) fs = 0
    rw [h1]
    change 𝓕.constantTerm (𝓕.removeSimpleRoot J β) (𝓕.unnormalizedAction J s' f) = 0
    rw [h2, hCT]
    rfl
  have hfsS : ∀ c : Gf, ContMDiff IG IC ∞ (fun y : G∞ => fs (pair F G y c)) := by
    intro c
    have h := hfS (finite F G S⁻¹ * c)
    have heq : (fun y : G∞ => fs (pair F G y c)) =
        (fun y => f (pair F G y (finite F G S⁻¹ * c))) ∘ (fun y => infinite F G S⁻¹ * y) := by
      funext y
      simp only [Function.comp, hfs]
      rw [← AdelicGroupPoints.pair_mul, pair_projections]
    rw [heq]
    exact h.comp contMDiff_mul_left
  have hfsRat : ∀ (q : RationalGroupPoints F (𝓕.U M)) x,
      fs (map F (𝓕.U M) G j (rational F (𝓕.U M) q) * x) = fs x := fun q x =>
    hfsR _ (𝓕.radical_rationalImage_le_minimalParabolic M
      ((mem_rationalImage_iff j _).mpr ⟨q, rfl⟩)) x
  have hfsL : ∀ l ∈ L, ∀ x, fs (x * ofFinite F G l) = fs x := by
    intro l hl x
    rw [hfs, hfs, ← mul_assoc, hfL l hl]
  have hpJ : p ∈ (map F (𝓕.P J) G (𝓕.p J)).toMonoidHom.range :=
    𝓕.range_map_le_of_le hB₀J (hΩP hp)
  have hshift (φ : A → ℂ) (hφ : 𝓕.IsRadicalInvariant J φ) (k' : A) :
      φ (S⁻¹ * (p * aG (sT * a) * k')) = φ (p * aG a * k') := by
    rw [map_mul, ← hsmap]
    have h1 : S⁻¹ * (p * (S * aG a) * k') = map F (𝓕.P J) G (𝓕.p J) s'.1 *
        (p * (S * (aG a * k'))) := by
      rw [hS']
      group
    rw [h1, IsRadicalInvariant.splitComponent_mul_comm 𝓕 hφ s' hpJ, hS', inv_mul_cancel_left,
      mul_assoc]
  have hx' : finite F G (p * aG (sT * a) * k) ∈ Yf := by
    have h1 : finite F G (p * aG (sT * a) * k) = finite F G (p * aG a * k) := by
      simp only [map_mul, finite_positiveMap F G 𝓕.T 𝓕.i 𝓕.T (𝟙 𝓕.T) hT, mul_one]
    rw [h1]
    exact hx
  have hHt : 0 ≤ height (aG a) := zero_le_one.trans (one_le_adelicHeight F G rho hN _)
  let Mb := Mw * (E ^ R * height (aG a) ^ R)
  have hMb : 0 ≤ Mb := mul_nonneg hMw (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hE1) _)
    (Real.rpow_nonneg hHt _))
  have hDer : ∀ k' ∈ K', finite F G k' = finite F G k → ∀ w : List Jw, w.length = n →
      ‖adelicIteratedDirectionalValue hG (w.map basisG) fs (p * aG (sT * a) * k')‖ ≤ Mb := by
    intro k' hk' _ w hw
    have h := adelicIteratedDirectionalValue_leftTranslate hG (w.map basisG) f S⁻¹
      (p * aG (sT * a) * k')
    have hfun : (fun y => f (S⁻¹ * y)) = fs := funext fun y => (hfs y).symm
    have hWU : 𝓕.IsRadicalInvariant J (adelicIteratedDirectionalValue hG (w.map basisG) f) := by
      intro u g
      rw [← adelicIteratedDirectionalValue_leftTranslate hG (w.map basisG) f]
      congr 1
      funext y
      exact hfU u y
    rw [hfun, hshift _ hWU] at h
    rw [h]
    refine (hW w hw _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hMw
    rw [← Real.mul_rpow (zero_le_one.trans hE1) hHt]
    exact Real.rpow_le_rpow (zero_le_one.trans (one_le_adelicHeight F G rho hN _))
      (hE p hp _ k' hk') hR
  have hmain := hiter p hp (sT * a) hch k hk hx' fs hfsC hfsS hfsRat hfsL hCTs Mb hMb hDer
  rw [hfs, hshift f hfU] at hmain
  have hdec : relativeCharacterDecay (𝟙 𝓕.T) β (sT * a) = relativeCharacterDecay (𝟙 𝓕.T) β a := by
    unfold relativeCharacterDecay
    rw [Category.id_comp, Subgroup.coe_mul, map_mul, hsT1 β hβ, one_mul]
  rw [hdec] at hmain
  calc ‖f (p * aG a * k)‖ ≤ Cd * relativeCharacterDecay (𝟙 𝓕.T) β a ^ n * Mb := hmain
    _ = Cd * E ^ R * relativeCharacterDecay (𝟙 𝓕.T) β a ^ n * Mw * height (aG a) ^ R := by
      dsimp only [Mb]
      ring

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [NumberField F] in
/-- A finite generating set of an abelian group spans its rationalization. -/
theorem ratSpan_eq_top_of_span_eq_top {M : Type*} [AddCommGroup M] {S : Set M}
    (hS : Submodule.span ℤ S = ⊤) : ratSpan S = ⊤ := by
  have hm : ∀ m : M, toRat m ∈ ratSpan S := by
    intro m
    have hmS : m ∈ Submodule.span ℤ S := hS ▸ Submodule.mem_top
    induction hmS using Submodule.span_induction with
    | mem x hx => exact toRat_mem_ratSpan hx
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul z x _ hx => rw [map_zsmul]; exact zsmul_mem hx z
  have hall : ∀ x : ℚ ⊗[ℤ] M, x ∈ ratSpan S := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul q m =>
      have h : q ⊗ₜ[ℤ] m = q • toRat m := by
        rw [toRat_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h]
      exact Submodule.smul_mem _ q (hm m)
    | add x y hx hy => exact add_mem hx hy
  exact eq_top_iff.mpr fun x _ => hall x

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [NumberField F] in
/-- A vector in the real span of a set is bounded, under every linear functional, by a fixed
multiple of a bound on the set. -/
theorem exists_abs_le_of_mem_span {E : Type*} [AddCommGroup E] [Module ℝ E] {X : Set E} {v : E}
    (hv : v ∈ Submodule.span ℝ X) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ℓ : E →ₗ[ℝ] ℝ) (B : ℝ), (∀ x ∈ X, |ℓ x| ≤ B) → |ℓ v| ≤ K * B := by
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.mp hv
  refine ⟨∑ k, |f k|, Finset.sum_nonneg fun k _ => abs_nonneg _, fun ℓ B hB => ?_⟩
  rw [← hfg, map_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [map_smul, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hB _ (g k).2) (abs_nonneg _)

/-- On a region where the roots of `J` are at least `b` and have logarithms at most `t`, and the
real functionals of a set `Φ`, which together with the roots of `J` spans `𝔞_0^*`, are bounded by
`B` on the logarithm `H` of the point, the height of the positive torus point grows at most
exponentially in `t`. -/
theorem exists_regionHeight_bound (hN : 0 < N) (J : Set (characterLattice 𝓕.T))
    (Φ : Set (Vstar 𝓕.T))
    (hspan : Submodule.span ℝ (((fun χ₀ : characterLattice 𝓕.T => (1 : ℝ) ⊗ₜ[ℤ] χ₀) '' J) ∪ Φ) = ⊤)
    (b : ℝ≥0ˣ) :
    ∃ C₀ r : ℝ, 1 ≤ C₀ ∧ 0 ≤ r ∧ ∀ (a : intrinsicSubgroup F 𝓕.T) (H : V 𝓕.T) (B t : ℝ),
      cocharacterFunctional H = characterLog F 𝓕.T.toGrp a.val → 0 ≤ B → 0 ≤ t →
      (∀ ρ₁ ∈ J, b ≤ normCharacter F 𝓕.T ρ₁ a) →
      (∀ ρ₁ ∈ J, logNormHom F 𝓕.T a.val ρ₁ ≤ t) →
      (∀ φ ∈ Φ, |pair 𝓕.T φ H| ≤ B) →
      height (aG a) ≤ C₀ * Real.exp (r * (max B (-Real.log ((b : ℝ≥0) : ℝ)) + t)) := by
  have hT : IsSplitTorus 𝓕.T.toGrp := 𝓕.maximalSplit.1.1
  have : Module.Finite ℤ (characterLattice 𝓕.T) := hT.finite_characterLattice
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := characterLattice 𝓕.T)
  have hratS := ratSpan_eq_top_of_span_eq_top hS
  obtain ⟨C₀, r, hC₀, hr, htorus⟩ := adelicPositiveTorusLogHeightBound
    (CommGroupScheme.groupHom (𝟙 𝓕.T) ≫ 𝓕.i) rho _ hT hratS hN
  have hcoef (χ : S) := exists_abs_le_of_mem_span (X := ((fun χ₀ : characterLattice 𝓕.T =>
    (1 : ℝ) ⊗ₜ[ℤ] χ₀) '' J) ∪ Φ) (v := (1 : ℝ) ⊗ₜ[ℤ] (χ : characterLattice 𝓕.T))
    (hspan ▸ Submodule.mem_top)
  choose Kc hKc hKcb using hcoef
  let K := ∑ χ, Kc χ
  have hK : 0 ≤ K := Finset.sum_nonneg fun χ _ => hKc χ
  refine ⟨C₀, r * K, hC₀, mul_nonneg hr hK, fun a H B t hH hB ht hlo hhi hΦ => ?_⟩
  let B₁ := max B (-Real.log ((b : ℝ≥0) : ℝ))
  have hB₁ : 0 ≤ B₁ := hB.trans (le_max_left _ _)
  have hlog (χ : characterLattice 𝓕.T) :
      logNormHom F 𝓕.T a.val χ = pair 𝓕.T ((1 : ℝ) ⊗ₜ[ℤ] χ) H := by
    rw [← cocharacterFunctional_apply, hH]
    rfl
  have hgen : ∀ x ∈ ((fun χ₀ : characterLattice 𝓕.T => (1 : ℝ) ⊗ₜ[ℤ] χ₀) '' J) ∪ Φ,
      |(pair 𝓕.T).flip H x| ≤ B₁ + t := by
    rintro x (⟨α, hα, rfl⟩ | hx)
    · rw [LinearMap.flip_apply, ← hlog]
      have hb0 : 0 < ((b : ℝ≥0) : ℝ) := by exact_mod_cast b.ne_zero.bot_lt
      have hlower : Real.log ((b : ℝ≥0) : ℝ) ≤ logNormHom F 𝓕.T a.val α :=
        Real.log_le_log hb0 (by exact_mod_cast Units.val_le_val.mpr (hlo α hα))
      apply abs_le.mpr
      refine ⟨?_, (hhi α hα).trans (le_add_of_nonneg_left hB₁)⟩
      have hbB : -Real.log ((b : ℝ≥0) : ℝ) ≤ B₁ := le_max_right _ _
      linarith
    · rw [LinearMap.flip_apply]
      exact (hΦ x hx).trans ((le_max_left _ _).trans (le_add_of_nonneg_right ht))
  have hS' : ∀ χ ∈ (S : Set (characterLattice 𝓕.T)), |logNormHom F 𝓕.T a.val χ| ≤
      K * (B₁ + t) := by
    intro χ hχ
    rw [hlog]
    have h := hKcb ⟨χ, hχ⟩ ((pair 𝓕.T).flip H) (B₁ + t) hgen
    rw [LinearMap.flip_apply] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (add_nonneg hB₁ ht))
    exact Finset.single_le_sum (f := Kc) (fun χ _ => hKc χ) (Finset.mem_univ _)
  have h := htorus a (K * (B₁ + t)) (mul_nonneg hK (add_nonneg hB₁ ht)) hS'
  refine h.trans_eq ?_
  rw [mul_assoc]

private theorem relativeCharacterDecay_pow' (α : characterLattice 𝓕.T)
    (a : intrinsicSubgroup F 𝓕.T) (n : ℕ) :
    relativeCharacterDecay (𝟙 𝓕.T) α a ^ n =
      Real.exp (-(n : ℝ) / (Module.finrank ℚ F : ℝ) * logNormHom F 𝓕.T a.val α) := by
  have hpos : 0 < ((normCharacter F 𝓕.T (𝟙 𝓕.T ≫ α) a : ℝ≥0) : ℝ) := by
    exact_mod_cast (normCharacter F 𝓕.T (𝟙 𝓕.T ≫ α) a).ne_zero.bot_lt
  rw [relativeCharacterDecay, Real.rpow_def_of_pos hpos, ← Real.exp_nat_mul]
  change Real.exp (_ * (Real.log _ * _)) = Real.exp (_ * Real.log _)
  rw [Category.id_comp]
  congr 1
  ring

/-- **Rapid decay of cuspidal functions on Levi Siegel regions.** Let `J` be a standard index and
`Φ` a set of real linear forms on `𝔞_0` which together with the simple roots of `J` spans
`𝔞_0^*`. Let `f` be a continuous function on `G(𝔸)`, smooth on the
archimedean slices, left invariant under `P_0(F)` and `U_J(𝔸)`, right invariant under an open
finite level, whose constant terms along the maximal parabolics `J \ {β}` (`β ∈ J`) of `M_J`
vanish, and whose derivative words have a common polynomial growth exponent `R`. Then `f`
decays faster than every power of the height on the region of points `p a k` with `p` in a
compact subset of `P_0(𝔸)`, the roots of `J` at `a` at least `b`, the forms of `Φ` bounded by
`B` at the logarithm `H ∈ 𝔞_0` of `a`, `k` in a compact set and the finite part in a compact
set. No condition is imposed on the simple roots outside `J`. -/
def RelativeCuspidalRegionDecayStatement : Prop :=
  0 < N →
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hG
  ∀ (J : Idx) (Φ : Set (Vstar 𝓕.T)),
    Submodule.span ℝ (((fun χ₀ : characterLattice 𝓕.T => (1 : ℝ) ⊗ₜ[ℤ] χ₀) '' J.1) ∪ Φ) = ⊤ →
  ∀ (b : ℝ≥0ˣ) (B : ℝ), 0 ≤ B →
  ∀ (Ω K : Set A), IsCompact Ω → IsCompact K →
    Ω ⊆ ((map F (𝓕.P B₀) G (𝓕.p B₀)).toMonoidHom.range : Set A) →
  ∀ (Yf : Set Gf), IsCompact Yf → ∀ (L : Subgroup Gf), IsOpen (L : Set Gf) →
  ∀ f : A → ℂ, Continuous f →
  (∀ c : Gf, ContMDiff IG IC ∞ (fun y : G∞ => f (pair F G y c))) →
  (∀ r ∈ rationalImage F (𝓕.p B₀), ∀ x, f (r * x) = f x) →
  𝓕.IsRadicalInvariant J f →
  (∀ l ∈ L, ∀ x, f (x * ofFinite F G l) = f x) →
  (∀ ρ₁ ∈ J.1, 𝓕.constantTerm (𝓕.removeSimpleRoot J ρ₁) f = 0) →
  ∀ R : ℝ, 0 ≤ R →
  (∀ s : List W, ∃ C : ℝ, 0 ≤ C ∧
    ∀ x, ‖adelicIteratedDirectionalValue hG s f x‖ ≤ C * height x ^ R) →
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Ω, ∀ (a : intrinsicSubgroup F 𝓕.T) (H : V 𝓕.T),
    cocharacterFunctional H = characterLog F 𝓕.T.toGrp a.val →
    (∀ ρ₁ ∈ J.1, b ≤ normCharacter F 𝓕.T ρ₁ a) →
    (∀ φ ∈ Φ, |pair 𝓕.T φ H| ≤ B) →
    ∀ k ∈ K, finite F G (p * aG a * k) ∈ Yf →
    ‖f (p * aG a * k)‖ * height (p * aG a * k) ^ m ≤ C

theorem relativeCuspidalRegionDecay : 𝓕.RelativeCuspidalRegionDecayStatement hG rho := by
  intro hN
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  intro J Φ hspan b B hB Ω K hΩ hK hΩP Yf hYf L hL f hf hfS hfR hfU hfL hCusp R hR hGrowth m
  let logRoot (a : intrinsicSubgroup F 𝓕.T) (α : characterLattice 𝓕.T) :=
    logNormHom F 𝓕.T a.val α
  have hJf : J.val.Finite :=
    (𝓕.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots 𝓕.i 𝓕.ν).subset J.2
  let : Fintype J.val := hJf.fintype
  let B₁ := max B (-Real.log ((b : ℝ≥0) : ℝ))
  obtain ⟨C₀, r, hC₀, hr, hAheight⟩ := 𝓕.exists_regionHeight_bound rho hN J.1 Φ hspan b
  let D := (Module.finrank ℚ F : ℝ)
  have hD : 0 < D := Nat.cast_pos.mpr Module.finrank_pos
  let e := R + (m : ℝ)
  have he : 0 ≤ e := add_nonneg hR (Nat.cast_nonneg _)
  obtain ⟨n, hn⟩ := exists_nat_gt (D * (r * e))
  have hn' : r * e ≤ (n : ℝ) / D :=
    (le_div_iff₀ hD).mpr (by simpa only [mul_comm] using hn.le)
  have hFiniteWords := fun w : Fin n → Jw => hGrowth ((List.ofFn w).map basisG)
  choose Cw hCw hw using hFiniteWords
  let Wn := ∑ w, Cw w
  have hWn : 0 ≤ Wn := Finset.sum_nonneg fun w _ => hCw w
  have hWord (s : List Jw) (hs : s.length = n) (x : A) :
      ‖adelicIteratedDirectionalValue hG (s.map basisG) f x‖ ≤ Wn * height x ^ R := by
    let w : Fin n → Jw := fun j => s.get (Fin.cast hs.symm j)
    have hws : List.ofFn w = s := by
      subst n
      exact List.ofFn_get s
    rw [← hws]
    exact (hw w x).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := Cw) (fun w _ => hCw w) (Finset.mem_univ _))
      (Real.rpow_nonneg (zero_le_one.trans (one_le_adelicHeight F G rho hN x)) _))
  have hdecay (α : J.val) := 𝓕.shiftedMaximalDecay hG rho hN J α.2 b n R hR Ω K hΩ hK hΩP
    Yf hYf L hL
  choose Cα hCα hiter using hdecay
  obtain ⟨E₀, hE₀, hEbase⟩ := exists_compact_factors_height_bound rho hN Ω K hΩ hK
  let A₀ := C₀ * Real.exp (r * B₁)
  have hA₀ : 0 < A₀ := mul_pos (zero_lt_one.trans_le hC₀) (Real.exp_pos _)
  let D₀ := E₀ * A₀
  have hD₀ : 0 < D₀ := mul_pos (zero_lt_one.trans_le hE₀) hA₀
  obtain ⟨Cbase, hCbase, hbase⟩ := hGrowth []
  let Base := Cbase * D₀ ^ e
  let Tail (α : J.val) := Cα α * Wn * E₀ ^ m * A₀ ^ e
  have hBase : 0 ≤ Base := mul_nonneg hCbase (Real.rpow_nonneg hD₀.le _)
  have hTail (α : J.val) : 0 ≤ Tail α :=
    mul_nonneg (mul_nonneg (mul_nonneg (hCα α) hWn) (pow_nonneg (zero_le_one.trans hE₀) _))
      (Real.rpow_nonneg hA₀.le _)
  refine ⟨Base + ∑ α, Tail α, add_nonneg hBase (Finset.sum_nonneg fun α _ => hTail α), ?_⟩
  intro p hp a H hH hlo hza k hk hx
  let lb : Option J.val → ℝ := fun α => α.elim 0 (fun x => logRoot a x.val)
  obtain ⟨s, _, hs⟩ := Finset.exists_max_image Finset.univ lb ⟨none, Finset.mem_univ _⟩
  have hmax₀ : 0 ≤ lb s := hs none (Finset.mem_univ _)
  have hmaxJ : ∀ α ∈ J.val, logRoot a α ≤ lb s := fun α hα =>
    hs (some ⟨α, hα⟩) (Finset.mem_univ _)
  have hha := hAheight a H B (lb s) hH hB hmax₀ hlo hmaxJ hza
  have hha' : height (aG a) ≤ A₀ * Real.exp (r * lb s) := by
    rw [mul_assoc, ← Real.exp_add, ← mul_add]
    exact hha
  let x := p * aG a * k
  have hxH : 0 < height x := zero_lt_one.trans_le (one_le_adelicHeight F G rho hN x)
  have haH : 0 < height (aG a) := zero_lt_one.trans_le (one_le_adelicHeight F G rho hN _)
  have hxle : height x ≤ E₀ * height (aG a) := hEbase p hp _ k hk
  cases s with
  | none =>
    have hha0 : height (aG a) ≤ A₀ := by
      simpa only [lb, Option.elim_none, mul_zero, Real.exp_zero, mul_one] using hha'
    have hdx : height x ≤ D₀ := hxle.trans (mul_le_mul_of_nonneg_left hha0 (zero_le_one.trans hE₀))
    calc
      ‖f x‖ * height x ^ m ≤ Cbase * height x ^ R * height x ^ m :=
        mul_le_mul_of_nonneg_right (by simpa using hbase x) (pow_nonneg hxH.le _)
      _ = Cbase * height x ^ e := by rw [show e = R + (m : ℝ) by rfl,
        Real.rpow_add hxH, Real.rpow_natCast]; ring
      _ ≤ Base := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hxH.le hdx he) hCbase
      _ ≤ Base + ∑ α, Tail α := le_add_of_nonneg_right (Finset.sum_nonneg fun α _ => hTail α)
  | some α =>
    let t := logRoot a α.val
    have ht : 0 ≤ t := hmax₀
    have hfdec := hiter α f hf hfS hfR hfU hfL (hCusp α.val α.2) Wn hWn hWord p hp a hlo k hk hx
    have hHt : height (aG a) ≤ A₀ * Real.exp (r * t) := hha'
    have hExpo : relativeCharacterDecay (𝟙 𝓕.T) α.val a ^ n * height (aG a) ^ e ≤ A₀ ^ e := by
      have h1 : height (aG a) ^ e ≤ (A₀ * Real.exp (r * t)) ^ e :=
        Real.rpow_le_rpow haH.le hHt he
      rw [Real.mul_rpow hA₀.le (Real.exp_pos _).le, ← Real.exp_mul] at h1
      rw [relativeCharacterDecay_pow' 𝓕]
      calc Real.exp (-(n : ℝ) / D * logNormHom F 𝓕.T a.val α.val) * height (aG a) ^ e
          ≤ Real.exp (-(n : ℝ) / D * t) * (A₀ ^ e * Real.exp (r * t * e)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = A₀ ^ e * Real.exp (-(n : ℝ) / D * t + r * t * e) := by
            rw [Real.exp_add]; ring
        _ ≤ A₀ ^ e * 1 := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr ?_)
              (Real.rpow_nonneg hA₀.le _)
            calc
              _ = (r * e - (n : ℝ) / D) * t := by ring
              _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hn') ht
        _ = A₀ ^ e := mul_one _
    have hcoef : Tail α ≤ Base + ∑ β, Tail β :=
      (Finset.single_le_sum (f := Tail) (fun β _ => hTail β) (Finset.mem_univ α)).trans
        (le_add_of_nonneg_left hBase)
    have hrel := (relativeCharacterDecay_pos (𝟙 𝓕.T) α.val a).le
    calc
      ‖f x‖ * height x ^ m ≤ (Cα α * relativeCharacterDecay (𝟙 𝓕.T) α.val a ^ n * Wn *
          height (aG a) ^ R) * (E₀ * height (aG a)) ^ m :=
        mul_le_mul hfdec (pow_le_pow_left₀ hxH.le hxle _) (pow_nonneg hxH.le _)
          (mul_nonneg (mul_nonneg (mul_nonneg (hCα α) (pow_nonneg hrel _)) hWn)
            (Real.rpow_nonneg haH.le _))
      _ = Cα α * Wn * E₀ ^ m *
          (relativeCharacterDecay (𝟙 𝓕.T) α.val a ^ n * height (aG a) ^ e) := by
        rw [show e = R + (m : ℝ) by rfl, Real.rpow_add haH, Real.rpow_natCast, mul_pow]
        ring
      _ ≤ Cα α * Wn * E₀ ^ m * A₀ ^ e :=
        mul_le_mul_of_nonneg_left hExpo
          (mul_nonneg (mul_nonneg (hCα α) hWn) (pow_nonneg (zero_le_one.trans hE₀) _))
      _ = Tail α := rfl
      _ ≤ Base + ∑ β, Tail β := hcoef

end Decay

end Langlands.Global.StandardParabolicFamily

import Langlands.Global.AdelicTemperedComponentInputs
import Langlands.Global.AdelicSiegelDominatedIntegrabilityProof
import Langlands.Global.AdelicSiegelDiagonalHeightBound
import Langlands.Global.AdelicSiegelConjugationBound
import Langlands.Global.AdelicRepresentationHeightExhaustion
import Langlands.Global.LeftCosetConjugationCount

/-! # Summability of a power of the logarithmic height against conjugation counts

This module proves `Langlands.Global.RationalQuotientSummableLogHeightStatement`
(module `Langlands.Global.AdelicTemperedComponentInputs`): for a connected reductive group `G`
over a number field and a closed matrix embedding `rho`, there is `m` such that for every compact
`C ⊆ G(𝔸)` the integral over `[G]` of `#{q ∈ G(F) : x⁻¹ q x ∈ C} · σ_{[G]}^{-2m}` is finite.

The proof fixes one compact set `D` and torus points `y_κ`, indexed by the integer dyadic
coordinates `κ` of the torus factor of a Siegel set. Every coset `z ∈ [G]` has a Siegel
representative; let `κ` be the dyadic index of its torus factor. Then `z.out = g₀ y_κ d` with
`g₀ ∈ G(F)` and `d ∈ D`, and `max(1, c₀ ∑_c |κ_c| - C₀) ≤ σ_{[G]}(z)`
(`exists_siegelTranslateCover`). The lower bound is proved for `z` and the index of its own
Siegel representative, not on the whole image of `y_κ D`. The unfolding estimate
`LeftCosetSpace.lintegral_conjugationCount_mul_le` then bounds the integral by
`(∑_κ Φ_κ) μ(D C)`, where `Φ_κ = max(1, c₀ ∑_c |κ_c| - C₀)^{-2m}` has finite sum over `κ`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

/-- A group identity: if `z` is central and `x` commutes with `m`, then
`(z x)⁻¹ (n m) = (x⁻¹ n x) m (z x)⁻¹`. -/
theorem inv_mul_mul_eq_conj_mul {M : Type*} [Group M] (z x n m : M)
    (hz : ∀ g : M, Commute z g) (hxm : Commute x m) :
    (z * x)⁻¹ * (n * m) = (x⁻¹ * n * x) * m * (z * x)⁻¹ := by
  have h1 : z⁻¹ * (n * m) = (n * m) * z⁻¹ := ((hz (n * m)).inv_left).eq
  have h2 : x * m * x⁻¹ = m := by rw [hxm.eq, mul_inv_cancel_right]
  calc (z * x)⁻¹ * (n * m) = x⁻¹ * (z⁻¹ * (n * m)) := by group
    _ = x⁻¹ * ((n * m) * z⁻¹) := by rw [h1]
    _ = x⁻¹ * n * (x * m * x⁻¹) * z⁻¹ := by rw [h2]; group
    _ = (x⁻¹ * n * x) * m * (z * x)⁻¹ := by group

/-- Submultiplicativity of the height for a product of five factors. -/
theorem adelicHeight_mul_five_le {F : Type} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hN : 0 < N) {g₁ g₂ g₃ g₄ g₅ : AdelicGroupPoints F G} {b₁ b₂ b₃ b₄ b₅ : ℝ}
    (h₁ : RepresentationGrowth.adelicHeight F G rho g₁ ≤ b₁)
    (h₂ : RepresentationGrowth.adelicHeight F G rho g₂ ≤ b₂)
    (h₃ : RepresentationGrowth.adelicHeight F G rho g₃ ≤ b₃)
    (h₄ : RepresentationGrowth.adelicHeight F G rho g₄ ≤ b₄)
    (h₅ : RepresentationGrowth.adelicHeight F G rho g₅ ≤ b₅) :
    RepresentationGrowth.adelicHeight F G rho (g₁ * g₂ * g₃ * g₄ * g₅) ≤
      b₁ * b₂ * b₃ * b₄ * b₅ := by
  have h0 : ∀ g, 0 ≤ RepresentationGrowth.adelicHeight F G rho g := fun g =>
    zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN g)
  have hmul := RepresentationGrowth.adelicHeight_mul_le F G rho hN
  calc RepresentationGrowth.adelicHeight F G rho (g₁ * g₂ * g₃ * g₄ * g₅)
      ≤ RepresentationGrowth.adelicHeight F G rho g₁ *
          RepresentationGrowth.adelicHeight F G rho g₂ *
          RepresentationGrowth.adelicHeight F G rho g₃ *
          RepresentationGrowth.adelicHeight F G rho g₄ *
          RepresentationGrowth.adelicHeight F G rho g₅ :=
        (hmul _ _).trans (mul_le_mul_of_nonneg_right ((hmul _ _).trans
          (mul_le_mul_of_nonneg_right ((hmul _ _).trans
            (mul_le_mul_of_nonneg_right (hmul _ _) (h0 _))) (h0 _))) (h0 _))
    _ ≤ b₁ * b₂ * b₃ * b₄ * b₅ := by
        have hb₁ := (h0 g₁).trans h₁
        have hb₂ := (h0 g₂).trans h₂
        have hb₃ := (h0 g₃).trans h₃
        have hb₄ := (h0 g₄).trans h₄
        exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h₁ h₂ (h0 _) hb₁) h₃ (h0 _)
          (mul_nonneg hb₁ hb₂)) h₄ (h0 _) (mul_nonneg (mul_nonneg hb₁ hb₂) hb₃)) h₅ (h0 _)
          (mul_nonneg (mul_nonneg (mul_nonneg hb₁ hb₂) hb₃) hb₄)

/-- **Lower bound of the quotient height by the height of a representative.** If
`‖X‖ ≤ L ‖q u‖` for every `q ∈ G(F)` (heights `‖·‖ = adelicHeight`), with `L ≥ 1`, then
`σ(X) - log L ≤ σ_{[G]}(G(F) u)`. -/
theorem adelicLogHeight_sub_log_le_rationalLogHeight {F : Type} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hN : 0 < N) {X : AdelicGroupPoints F G} {z : RationalQuotient F G} {L : ℝ} (hL : 1 ≤ L)
    (hX : ∀ q ∈ rationalSubgroup F G, RepresentationGrowth.adelicHeight F G rho X ≤
      L * RepresentationGrowth.adelicHeight F G rho (q * z.out)) :
    adelicLogHeight F G rho X - Real.log L ≤ rationalLogHeight F G rho z := by
  set s : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
  have hs : 0 < s := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hsrc : ∀ g, RepresentationGrowth.adelicHeight F G rho g =
      s * RepresentationGrowth.adelicSourceNorm F G rho g :=
    RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho
  set x := RepresentationGrowth.adelicSourceNorm F G rho X
  set y := ⨅ q : rationalSubgroup F G,
    RepresentationGrowth.adelicSourceNorm F G rho ((q : AdelicGroupPoints F G) * z.out)
  have hinf : x ≤ y * L := by
    rw [← div_le_iff₀ hL0]
    refine le_ciInf fun q => ?_
    have h := hX q q.2
    rw [hsrc, hsrc] at h
    rw [div_le_iff₀ hL0]
    have h' : s * x ≤ s * (RepresentationGrowth.adelicSourceNorm F G rho
        ((q : AdelicGroupPoints F G) * z.out) * L) := by linarith
    exact le_of_mul_le_mul_left h' hs
  have hmax : max 1 x / L ≤ max 1 y := by
    rw [div_le_iff₀ hL0]
    have h1 : 1 ≤ max 1 y := le_max_left _ _
    have h2 : y ≤ max 1 y := le_max_right _ _
    refine max_le ?_ ?_ <;> nlinarith
  have hpos : 0 < max 1 x / L := div_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) hL0
  have hlog := Real.log_le_log hpos hmax
  rw [Real.log_div (lt_of_lt_of_le one_pos (le_max_left _ _)).ne' hL0.ne'] at hlog
  unfold adelicLogHeight rationalLogHeight
  linarith

section Cover

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- **Siegel translates with quotient height bounds.** For connected reductive `G` and a closed
matrix embedding `rho` of positive size there are a countable family `y_κ` of points of `G(𝔸)`,
a height bound `R`, an exponent `m` and weights `Φ_κ` with finite sum such that every coset
`z ∈ [G]` has a representative `z.out = g₀ y_κ d` with `g₀ ∈ G(F)`, `‖d‖ ≤ R` and
`σ_{[G]}(z)^{-2m} ≤ Φ_κ`. The indices are the integer dyadic coordinates of the torus factor of
a Siegel set, and the index of `z` is that of its own Siegel representative. For an index of a
torus point in the chamber, `y_κ` is such a torus point; for the other indices, which are never
the index of a coset, `y_κ = 1`. The weight is `Φ_κ = max(1, c₀ ∑_c |κ_c| - C₀)^{-2m}`. -/
theorem exists_siegelTranslateCover (hG : IsConnectedReductive G) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho) :
    ∃ (Idx : Type) (_ : Countable Idx) (y : Idx → AdelicGroupPoints F G) (R : ℝ) (m : ℕ)
      (Φ : Idx → ℝ≥0∞), ∑' κ, Φ κ ≠ ∞ ∧
      ∀ z : RationalQuotient F G, ∃ κ, ∃ g₀ ∈ rationalSubgroup F G,
        ∃ d ∈ RepresentationGrowth.adelicHeightSublevel F G rho R,
          z.out = g₀ * y κ * d ∧
          ENNReal.ofReal ((rationalLogHeight F G rho z ^ (2 * m))⁻¹) ≤ Φ κ := by
  classical
  obtain ⟨T, i, ν, T₀, j, hS⟩ := siegelAlgebraicSetupExistence_of_structural
    genericMinimalParabolic derivedMaximalSplitTorus derivedCentralSplitTorusProduct F G hG
  obtain ⟨K, H₁, W, hKc, hH₁, hKH₁, hH₁P, hcompat, hW, hW1, hcov⟩ :=
    exists_compact_openSubgroup_finite_cover F G hG T i ν T₀ j hS
  obtain ⟨C, t, rfl, hcover⟩ :=
    exists_rational_mul_mem_weakSiegelProduct_mul F G hG T i ν T₀ j hS K hKc W hW hW1 hcov
  obtain ⟨hTmax, -, -, -, -, hlevi, -, -, Z₀, zc, hzsplit, -⟩ := id hS
  have hzc : IsCentral (CommGroupScheme.groupHom zc ≫ i) := hzsplit.1.2
  have hZ : IsSplitTorus Z₀.toGrp := hzsplit.1.1.1
  obtain ⟨I, hI, ⟨e⟩⟩ := id hZ
  have : Fintype I := Fintype.ofFinite I
  have : (characterRestrict (CommGroupScheme.groupHom zc ≫ i)).range.FiniteIndex :=
    characterRestrictionFiniteIndexStatement F G hG Z₀ _ hzsplit
  obtain ⟨m₀, hm₀, hχ⟩ := RepresentationGrowth.exists_characterNorm_full F Z₀
    (CommGroupScheme.groupHom zc ≫ i) e
  choose χ hχ using hχ
  have : Fintype (simpleRelativeRoots i ν) := (hTmax.1.1.finite_simpleRelativeRoots i ν).fintype
  have hbox := isCompact_dyadicBox_siegelCoordinates zc hG hS e χ
    (Nat.mul_pos hm₀ Module.finrank_pos) hχ
  obtain ⟨A, B, hA, hAB⟩ := exists_abs_zIndex_le zc hzc hS rho hN hrho hZ C t hW hW1 χ
  set lam := siegelCoordinates (i := i) (ν := ν) (j := j) zc χ with hlam
  set chamber := PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t with hchamber
  have hHc : Continuous (RepresentationGrowth.adelicHeight F G rho) :=
    RepresentationGrowth.continuous_adelicHeight F G rho hN
  -- height bounds for the factors
  obtain ⟨BN, hBN⟩ := exists_adelicHeight_conj_unipotent_le F G T i ν T₀ j hG hS rho hN
    C.omegaN C.compact_omegaN t
  obtain ⟨BM, hBM⟩ := (C.compact_omegaM.image (hHc.comp
    ((map F _ G (Standard.leviHom i ν ∅)).continuous.comp continuous_subtype_val))).bddAbove
  obtain ⟨BX, hBX⟩ := (hbox.image (hHc.comp (continuous_siegelTorusMap (j := j) zc hzc))).bddAbove
  obtain ⟨BK, hBK⟩ := (C.compact_compactSubgroup.image hHc).bddAbove
  obtain ⟨BW, hBW⟩ := (hW.image (RepresentationGrowth.adelicHeight F G rho)).bddAbove
  set R := max BN 1 * max BM 1 * max BX 1 * max BK 1 * max BW 1 with hR
  have hR1 : 1 ≤ R := by
    have := le_max_right BN 1
    have := le_max_right BM 1
    have := le_max_right BX 1
    have := le_max_right BK 1
    have := le_max_right BW 1
    rw [hR]
    calc (1 : ℝ) = 1 * 1 * 1 * 1 * 1 := by ring
      _ ≤ max BN 1 * max BM 1 * max BX 1 * max BK 1 * max BW 1 := by gcongr
  -- norm minimality on the torus
  obtain ⟨cA, -, hcA⟩ := exists_adelicHeight_map_le_rational_mul F G rho hN T hTmax.1.1 i
  set L := max cA 1 * R * R with hLdef
  have hL1 : 1 ≤ L := by
    have := le_max_right cA 1
    rw [hLdef]
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ max cA 1 * R * R := by gcongr
  -- the family of torus points
  let Idx := I ⊕ simpleRelativeRoots i ν → ℤ
  let P : Idx → Prop := fun κ => ∃ p : PositiveRealTorus.intrinsicSubgroup F Z₀ ×
    PositiveRealTorus.intrinsicSubgroup F T₀, p.2 ∈ chamber ∧ SiegelSetMeasure.zIndex lam p = κ
  let pκ : Idx → PositiveRealTorus.intrinsicSubgroup F Z₀ ×
      PositiveRealTorus.intrinsicSubgroup F T₀ := fun κ => if h : P κ then h.choose else 1
  have hpκ : ∀ κ (h : P κ), (pκ κ).2 ∈ chamber ∧ SiegelSetMeasure.zIndex lam (pκ κ) = κ := by
    intro κ h
    simp only [pκ, h, dite_true]
    exact h.choose_spec
  -- the weights
  set nι := Fintype.card (I ⊕ simpleRelativeRoots i ν) with hnι
  set B' : ℝ := A * Real.log L + B with hB'
  set c₀ : ℝ := 1 / ((nι + 1) * (A + 1)) with hc₀def
  set C₀ : ℝ := |B'| / (A + 1) with hC₀def
  have hc₀ : 0 < c₀ := by positivity
  let Φ : Idx → ℝ≥0∞ := fun κ =>
    ENNReal.ofReal ((max 1 (c₀ * ∑ c, |(κ c : ℝ)| - C₀))⁻¹ ^ (2 * nι))
  have hΦ : ∑' κ, Φ κ ≠ ∞ := SiegelSetMeasure.tsum_decay_ne_top hc₀ C₀
  refine ⟨Idx, inferInstance, fun κ => siegelTorusMap (j := j) zc hzc (pκ κ), R, nι, Φ, hΦ,
    fun z => ?_⟩
  -- a Siegel representative of `z`
  obtain ⟨r, hr, hrX⟩ :=
    exists_rational_mul_mem_centralSiegelSet_mul zc hzc hG hzsplit C t W hcover z.out
  obtain ⟨s, hs, w, hw, hsw⟩ := hrX
  rw [centralSiegelSet] at hs
  obtain ⟨s₁, hs₁, k, hk, rfl⟩ := hs
  obtain ⟨s₂, hs₂, _, ⟨p, hp, rfl⟩, rfl⟩ := hs₁
  obtain ⟨_, ⟨n, hn, rfl⟩, _, ⟨m, hm, rfl⟩, rfl⟩ := hs₂
  set ιN := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n with hιN
  set ιM := map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m with hιM
  set X := ιN * ιM * siegelTorusMap (j := j) zc hzc p * k * w with hX
  have hXz : X = r * z.out := hsw
  set κ := SiegelSetMeasure.zIndex lam p with hκ
  obtain ⟨hp'c, hp'z⟩ := hpκ κ ⟨p, hp.2, rfl⟩
  set p' := pκ κ with hp'
  set y := siegelTorusMap (j := j) zc hzc p' with hy
  set d := y⁻¹ * X with hd
  have hyd : y * d = X := by rw [hd, mul_inv_cancel_left]
  have hzout : z.out = r⁻¹ * y * d := by
    rw [mul_assoc, hyd, hXz, inv_mul_cancel_left]
  -- the height of `d`
  set z' := positiveMap F G T i Z₀ zc p'.1 with hz'
  set x' := positiveMap F G T i T₀ j p'.2 with hx'
  have hyzx : y = z' * x' := siegelTorusMap_apply (j := j) zc hzc p'
  have hcent : ∀ g, Commute z' g := positiveMap_central zc hzc p'.1
  have hxm : Commute x' ιM :=
    positiveMap_commute_of_mem_standardLevi hlevi j p'.2 (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hdeq : d = (x'⁻¹ * ιN * x') * ιM * siegelTorusMap (j := j) zc hzc (p'⁻¹ * p) * k * w := by
    rw [map_mul, map_inv, ← hy, hyzx, hd, hX, hyzx]
    have key := inv_mul_mul_eq_conj_mul z' x' ιN ιM hcent hxm
    calc (z' * x')⁻¹ * (ιN * ιM * siegelTorusMap (j := j) zc hzc p * k * w)
        = ((z' * x')⁻¹ * (ιN * ιM)) * siegelTorusMap (j := j) zc hzc p * k * w := by
          simp only [mul_assoc]
      _ = _ := by rw [key]; simp only [mul_assoc]
  have hdR : RepresentationGrowth.adelicHeight F G rho d ≤ R := by
    rw [hdeq]
    have hboxmem : p'⁻¹ * p ∈ SiegelSetMeasure.dyadicBox lam :=
      SiegelSetMeasure.inv_mul_mem_dyadicBox_of_zIndex_eq lam (hp'z.trans hκ).symm
    exact adelicHeight_mul_five_le rho hN
      ((hBN n hn p'.2 hp'c).trans (le_max_left _ _))
      ((hBM ⟨m, hm, rfl⟩).trans (le_max_left _ _))
      ((hBX ⟨p'⁻¹ * p, hboxmem, rfl⟩).trans (le_max_left _ _))
      ((hBK ⟨k, hk, rfl⟩).trans (le_max_left _ _))
      ((hBW ⟨w, hw, rfl⟩).trans (le_max_left _ _))
  -- `y` is the image of a positive point of `T`
  have hyT : ∃ τ : PositiveRealTorus.intrinsicSubgroup F T,
      AdelicGroupPoints.map F T.toGrp G i τ = y := by
    have h1 : map F Z₀.toGrp T.toGrp (CommGroupScheme.groupHom zc) p'.1.val ∈
        PositiveRealTorus.intrinsicSubgroup F T :=
      PositiveRealTorus.map_intrinsicSubgroup_le F Z₀ T zc ⟨p'.1.val, p'.1.property, rfl⟩
    have h2 : map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) p'.2.val ∈
        PositiveRealTorus.intrinsicSubgroup F T :=
      PositiveRealTorus.map_intrinsicSubgroup_le F T₀ T j ⟨p'.2.val, p'.2.property, rfl⟩
    refine ⟨⟨_, (PositiveRealTorus.intrinsicSubgroup F T).mul_mem h1 h2⟩, ?_⟩
    have hcomp : ∀ {H : GroupScheme (Spec (CommRingCat.of F))} (f : H ⟶ T.toGrp)
        (u : AdelicGroupPoints F H),
        map F H G (f ≫ i) u = map F T.toGrp G i (map F H T.toGrp f u) := by
      intro H f u
      simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom,
        Category.assoc]
    change map F T.toGrp G i (map F Z₀.toGrp T.toGrp (CommGroupScheme.groupHom zc) p'.1.val *
      map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) p'.2.val) = y
    rw [map_mul, hy, siegelTorusMap_apply]
    exact congrArg₂ (· * ·) (hcomp _ _).symm (hcomp _ _).symm
  obtain ⟨τ, hτ⟩ := hyT
  -- norm minimality at `X`
  have hmin : ∀ q ∈ rationalSubgroup F G, RepresentationGrowth.adelicHeight F G rho X ≤
      L * RepresentationGrowth.adelicHeight F G rho (q * z.out) := by
    intro q hq
    have hq₁ : q * r⁻¹ ∈ rationalSubgroup F G :=
      (rationalSubgroup F G).mul_mem hq ((rationalSubgroup F G).inv_mem hr)
    obtain ⟨q₂, hq₂⟩ := MonoidHom.mem_range.mp hq₁
    have h0 : ∀ g, 0 ≤ RepresentationGrowth.adelicHeight F G rho g := fun g =>
      zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN g)
    have hmul := RepresentationGrowth.adelicHeight_mul_le F G rho hN
    have hA' : RepresentationGrowth.adelicHeight F G rho y ≤
        max cA 1 * RepresentationGrowth.adelicHeight F G rho (q * r⁻¹ * y) := by
      have := hcA τ q₂
      rw [hτ] at this
      change RepresentationGrowth.adelicHeight F G rho y ≤
        cA * RepresentationGrowth.adelicHeight F G rho (rational F G q₂ * y) at this
      rw [show rational F G q₂ = q * r⁻¹ from hq₂] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (h0 _))
    have hB1 : RepresentationGrowth.adelicHeight F G rho (q * r⁻¹ * y) ≤
        RepresentationGrowth.adelicHeight F G rho (q * z.out) * R := by
      have he : q * r⁻¹ * y = q * z.out * d⁻¹ := by
        rw [hzout]
        group
      rw [he]
      refine (hmul _ _).trans (mul_le_mul_of_nonneg_left ?_ (h0 _))
      rw [RepresentationGrowth.adelicHeight_inv]
      exact hdR
    have hB2 : RepresentationGrowth.adelicHeight F G rho X ≤
        RepresentationGrowth.adelicHeight F G rho y * R := by
      rw [← hyd]
      exact (hmul _ _).trans (mul_le_mul_of_nonneg_left hdR (h0 _))
    have hR0 : 0 ≤ R := zero_le_one.trans hR1
    calc RepresentationGrowth.adelicHeight F G rho X
        ≤ RepresentationGrowth.adelicHeight F G rho y * R := hB2
      _ ≤ max cA 1 * (RepresentationGrowth.adelicHeight F G rho (q * z.out) * R) * R := by
          gcongr
          exact hA'.trans (mul_le_mul_of_nonneg_left hB1 (zero_le_one.trans (le_max_right _ _)))
      _ = L * RepresentationGrowth.adelicHeight F G rho (q * z.out) := by
          rw [hLdef]
          ring
  have hσ := adelicLogHeight_sub_log_le_rationalLogHeight rho hN hL1 hmin
  -- the weight bound
  have hσ1 : 1 ≤ rationalLogHeight F G rho z := one_le_rationalLogHeight rho z
  have hsum : ∑ c, |(κ c : ℝ)| ≤ nι * (A * rationalLogHeight F G rho z + |B'|) := by
    calc ∑ c, |(κ c : ℝ)| ≤ ∑ _c : I ⊕ simpleRelativeRoots i ν,
          (A * rationalLogHeight F G rho z + |B'|) := by
          refine Finset.sum_le_sum fun c _ => ?_
          have h1 := hAB p hp.2 n hn m hm k hk w hw c
          have h2 : A * adelicLogHeight F G rho X ≤
              A * (rationalLogHeight F G rho z + Real.log L) :=
            mul_le_mul_of_nonneg_left (by linarith) hA
          have h3 : B' ≤ |B'| := le_abs_self _
          rw [hB'] at h3
          change |(SiegelSetMeasure.zIndex lam p c : ℝ)| ≤ _
          nlinarith
      _ = nι * (A * rationalLogHeight F G rho z + |B'|) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hmax := max_le_of_sum_le hA hσ1 hsum
  have hmpos : 0 < max 1 (c₀ * ∑ c, |(κ c : ℝ)| - C₀) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨κ, r⁻¹, (rationalSubgroup F G).inv_mem hr, d, hdR, hzout, ?_⟩
  apply ENNReal.ofReal_le_ofReal
  rw [← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr (zero_le_one.trans hσ1)) (inv_anti₀ hmpos hmax) _

/-- **Main case, `N > 0`.** -/
theorem rationalQuotientSummableLogHeight_of_pos (hG : IsConnectedReductive G) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho) :
    ∃ m : ℕ, ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
      ∫⁻ y, (({q : AdelicGroupPoints F G | q ∈ rationalSubgroup F G ∧
          y.out⁻¹ * q * y.out ∈ C}.encard : ℕ∞) : ℝ≥0∞) *
        ENNReal.ofReal ((rationalLogHeight F G rho y ^ (2 * m))⁻¹)
          ∂(LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
            (isDiscrete_rationalSubgroup F G) Measure.haar) < ∞ := by
  obtain ⟨Idx, _, y, R, m, Φ, hΦ, hcov⟩ := exists_siegelTranslateCover hG rho hN hrho
  refine ⟨m, fun C hC => ?_⟩
  have hD : IsCompact (RepresentationGrowth.adelicHeightSublevel F G rho R) :=
    RepresentationGrowth.isCompact_adelicHeightSublevel F G rho hN hrho R
  have hDC : IsCompact (RepresentationGrowth.adelicHeightSublevel F G rho R * C) := hD.mul hC
  exact lt_of_le_of_lt (LeftCosetSpace.lintegral_conjugationCount_mul_le (rationalSubgroup F G)
    (isDiscrete_rationalSubgroup F G) Measure.haar y C
    (RepresentationGrowth.adelicHeightSublevel F G rho R) hDC.isClosed.measurableSet
    (fun z => ENNReal.ofReal ((rationalLogHeight F G rho z ^ (2 * m))⁻¹)) Φ hcov)
    (ENNReal.mul_lt_top hΦ.lt_top hDC.measure_lt_top)

omit [IsAffineHom G.X.hom] in
/-- **Degenerate case, `N = 0`.** A closed embedding into `GL_0` makes `G(𝔸)` trivial, so the
statement holds with `m = 0`. -/
theorem rationalQuotientSummableLogHeight_of_zero (rho : MatrixRepresentation G (Fin 0))
    (hrho : IsClosedSubgroup rho) :
    ∃ m : ℕ, ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
      ∫⁻ y, (({q : AdelicGroupPoints F G | q ∈ rationalSubgroup F G ∧
          y.out⁻¹ * q * y.out ∈ C}.encard : ℕ∞) : ℝ≥0∞) *
        ENNReal.ofReal ((rationalLogHeight F G rho y ^ (2 * m))⁻¹)
          ∂(LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
            (isDiscrete_rationalSubgroup F G) Measure.haar) < ∞ := by
  have : Subsingleton (AdelicGL F 0) :=
    ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  have hsub : Subsingleton (AdelicGroupPoints F G) :=
    (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective.subsingleton
  have : CompactSpace (AdelicGroupPoints F G) := Finite.compactSpace
  refine ⟨0, fun C hC => ?_⟩
  have hDC : IsCompact (Set.univ * C) := isCompact_univ.mul hC
  refine lt_of_le_of_lt (LeftCosetSpace.lintegral_conjugationCount_mul_le (rationalSubgroup F G)
    (isDiscrete_rationalSubgroup F G) Measure.haar (fun _ : Unit => (1 : AdelicGroupPoints F G))
    C Set.univ hDC.isClosed.measurableSet
    (fun z => ENNReal.ofReal ((rationalLogHeight F G rho z ^ (2 * 0))⁻¹)) (fun _ => 1) ?_) ?_
  · intro z
    refine ⟨(), 1, (rationalSubgroup F G).one_mem, z.out, Set.mem_univ _, by simp, ?_⟩
    simp
  · rw [tsum_fintype, Finset.univ_unique, Finset.sum_singleton, one_mul]
    exact hDC.measure_lt_top

end Cover

end Langlands.Global.AdelicSiegelFactors

namespace Langlands.Global

/-- **Summability of a power of the logarithmic height against the conjugation count on
`G(F) \ G(𝔸)`** (Bernstein 1988, §§3.2–3.4; Delorme 2023, (2.10) and Remark 3.4). -/
theorem rationalQuotientSummableLogHeight : RationalQuotientSummableLogHeightStatement := by
  intro F _ _ G _ _ _ hG K N rho _ hrho _
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact AdelicSiegelFactors.rationalQuotientSummableLogHeight_of_zero rho hrho
  · exact AdelicSiegelFactors.rationalQuotientSummableLogHeight_of_pos hG rho hN hrho

end Langlands.Global

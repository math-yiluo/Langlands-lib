import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingGroups
import Langlands.Global.Factors.CuspidalPairEisensteinConvergence
import Langlands.Global.EisensteinConstantTerm.Height

/-! # The twisted section and the Eisenstein sum of a cuspidal pair

For a section `φ` of the cuspidal pair and `s : ℂ`, the twisted section `φ_s = φ · H^s` is
continuous, left invariant under `P(F)` and under the unipotent radical `U(𝔸)`. The Eisenstein
sum is left invariant under `GL_N(F)`, it is continuous on the half-plane of normal convergence,
and it is the sum over the cells `J` and the cosets `Λ_J(F) \ N₀(F)` of the translates of `φ_s` by
the cell representatives. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.CuspidalPairEisenstein

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open AdelicBlockEisensteinGeometry AdelicGroupPoints GeneralLinearGroupPoints
open Langlands.Automorphic.GroupSchemeFunctions PrimitiveAdelicHeight RowEchelon

section Section

local instance seriesGLAffine {F : Type u} [Field F] (n : ℕ) :
    IsAffine (groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance seriesGLAffineHom {F : Type u} [Field F] (n : ℕ) :
    IsAffineHom (groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  isAffineHom_groupScheme (n := Fin n) (R := CommRingCat.of F)

local instance seriesParabolicAffine {F : Type u} [Field F] [NumberField F] (r t : ℕ) :
    IsAffine (blockParabolicScheme (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).X.left :=
  blockParabolic_isAffine F (blockShape r t)

local instance seriesParabolicClosed {F : Type u} [Field F] (r t : ℕ) :
    IsClosedImmersion (blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).hom.hom.left :=
  isClosedSubgroup_blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
    (blockShapeWeight (blockShape r t))

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r t : ℕ}
  {T : Automorphic.CuspidalOperatorRealization F r}
  {T' : Automorphic.CuspidalOperatorRealization F t} {φ : AdelicGL F (r + t + 2) → ℂ}

/-- The twisted section `φ_s = φ · H^s`. -/
def twisted (φ : AdelicGL F (r + t + 2) → ℂ) (s : ℂ) (g : AdelicGL F (r + t + 2)) : ℂ :=
  φ g * heightPower F r t s g

theorem continuous_of_isSection (hφ : IsSection T T' φ) : Continuous φ := by
  have hG := isConnectedReductive_generalLinear F (Fin (r + t + 2))
  have hs := hG.smoothDimension_spec
  have hc := adelicDifferentialCommutator_of_smooth F
    (groupScheme (Fin (r + t + 2)) (CommRingCat.of F)) hs
  have h := (isAutomorphicFunctionOn_of_isSection hφ hs hc).2.1.1
  have : φ = (φ ∘ adelicHomeomorph F (r + t + 2)) ∘ (adelicHomeomorph F (r + t + 2)).symm := by
    funext g
    simp
  rw [this]
  exact h.comp (adelicHomeomorph F (r + t + 2)).symm.continuous

omit [CompactSpace (AdeleQuotient F)] in
theorem continuous_heightPower (s : ℂ) : Continuous (heightPower F r t s) := by
  have h := (isIwasawaCompact_blockParabolic F (blockShape r t)).continuous_heightPower
    (s • lineParameter F r t)
  have : heightPower F r t s = (isIwasawaCompact_blockParabolic F (blockShape r t)).heightPower
      (s • lineParameter F r t) ∘ (adelicHomeomorph F (r + t + 2)).symm := by
    funext g
    simp only [Function.comp_apply]
    rw [← heightPower_eq_schemeHeightPower, ContinuousMulEquiv.apply_symm_apply]
  rw [this]
  exact h.comp (adelicHomeomorph F (r + t + 2)).symm.continuous

theorem continuous_twisted (hφ : IsSection T T' φ) (s : ℂ) : Continuous (twisted φ s) :=
  (continuous_of_isSection hφ).mul (continuous_heightPower s)

theorem twisted_rational_mul (hφ : IsSection T T' φ) (s : ℂ) (c0 : RationalGL F (r + t + 2))
    (hc0 : c0 ∈ (blockShape r t).parabolic F) (x : AdelicGL F (r + t + 2)) :
    twisted φ s (AdelicGL.rational F (r + t + 2) c0 * x) = twisted φ s x := by
  rw [twisted, twisted, isSection_rational_mul hφ c0 hc0, heightPower_rational_mul s c0 hc0]

omit [CompactSpace (AdeleQuotient F)] in
theorem heightPower_unipotent_mul (s : ℂ) {u : AdelicGL F (r + t + 2)}
    (hu : u ∈ (blockShape r t).unipotentSubgroup (Adeles F)) (x : AdelicGL F (r + t + 2)) :
    heightPower F r t s (u * x) = heightPower F r t s x := by
  obtain ⟨⟨u', hu'P⟩, hu'U, rfl⟩ := hu
  change heightPower F r t s (u' * x) = heightPower F r t s x
  obtain ⟨q, k, hqk⟩ := AdelicBlockScalarSections.exists_parabolic_mul_standardCompact F
    (blockShape r t) x
  let q' : AdelicBlockParabolic.Full F (blockShape r t) := ⟨u', hu'P⟩ * q
  have hq' : q'.val * k.val = u' * x := by
    rw [hqk, ← mul_assoc]
    rfl
  rw [heightPower_eq s q' k.property hq', heightPower_eq s q k.property hqk.symm, map_mul]
  have h1 : AdelicBlockDeterminantCharacter.parabolicCharacter F (blockShape r t) ⟨u', hu'P⟩ = 1 :=
    AdelicBlockDeterminantCharacter.parabolicCharacter_unipotent F (blockShape r t) ⟨⟨u', hu'P⟩, hu'U⟩
  rw [h1, one_mul]

theorem twisted_unipotent_mul (hφ : IsSection T T' φ) (s : ℂ) {u : AdelicGL F (r + t + 2)}
    (hu : u ∈ (blockShape r t).unipotentSubgroup (Adeles F)) (x : AdelicGL F (r + t + 2)) :
    twisted φ s (u * x) = twisted φ s x := by
  rw [twisted, twisted, hφ.2.2.2.1 ⟨u, hu⟩ x, heightPower_unipotent_mul s hu]

omit [CompactSpace (AdeleQuotient F)] in
theorem eisensteinSeries_eq_tsum (s : ℂ) (g : AdelicGL F (r + t + 2)) :
    eisensteinSeries F φ s g = ∑' c : Quotient (QuotientGroup.rightRel
      ((blockShape r t).parabolic F)),
      twisted φ s (AdelicGL.rational F (r + t + 2) (Quotient.out c) * g) := rfl

end Section

section Reindex

variable {G : Type*} [Group G] (P : Subgroup G)

/-- The chosen representative of `P (x c₁)` is `p x c₁` for some `p ∈ P`. -/
theorem exists_out_mul (x c₁ : G) :
    ∃ p ∈ P, (Quotient.out (Quotient.mk (QuotientGroup.rightRel P) (x * c₁)) : G) = p * (x * c₁) := by
  have h := Quotient.mk_out (s := QuotientGroup.rightRel P) (x * c₁)
  rw [QuotientGroup.rightRel_apply] at h
  exact ⟨_, P.inv_mem h, by group⟩

/-- Right translation of `P \ G` by `c₁`. -/
def rightTranslate (c₁ : G) : Quotient (QuotientGroup.rightRel P) ≃
    Quotient (QuotientGroup.rightRel P) where
  toFun := Quotient.map' (fun x => x * c₁) (fun a b h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_assoc] using h)
  invFun := Quotient.map' (fun x => x * c₁⁻¹) (fun a b h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_assoc] using h)
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']

/-- Reindexing a sum over `P \ G` of a left `P`-invariant function by right translation. -/
theorem tsum_out_mul_right {E : Type*} [AddCommMonoid E] [TopologicalSpace E] {g : G → E}
    (hg : ∀ p ∈ P, ∀ x, g (p * x) = g x) (c₁ : G) :
    ∑' c : Quotient (QuotientGroup.rightRel P), g (Quotient.out c * c₁) =
      ∑' c : Quotient (QuotientGroup.rightRel P), g (Quotient.out c) := by
  conv_rhs => rw [← (rightTranslate P c₁).tsum_eq]
  congr 1
  funext c
  have hc : rightTranslate P c₁ c = Quotient.mk _ (Quotient.out c * c₁) := by
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  rw [hc]
  obtain ⟨p, hp, h⟩ := exists_out_mul P (Quotient.out c) c₁
  rw [h, hg p hp]

end Reindex

section Series

local instance seriesGLSmooth {F : Type u} [Field F] (n : ℕ) :
    Smooth (groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

local instance seriesGLAffine' {F : Type u} [Field F] (n : ℕ) :
    IsAffine (groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  isAffine_groupScheme (Fin n) (CommRingCat.of F)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r t : ℕ}
  {T : Automorphic.CuspidalOperatorRealization F r}
  {T' : Automorphic.CuspidalOperatorRealization F t} {φ : AdelicGL F (r + t + 2) → ℂ}

/-- The Eisenstein sum is left invariant under `GL_N(F)`. -/
theorem eisensteinSeries_rational_mul (hφ : IsSection T T' φ) (s : ℂ)
    (c₁ : RationalGL F (r + t + 2)) (g : AdelicGL F (r + t + 2)) :
    eisensteinSeries F φ s (AdelicGL.rational F (r + t + 2) c₁ * g) = eisensteinSeries F φ s g := by
  rw [eisensteinSeries_eq_tsum, eisensteinSeries_eq_tsum]
  have := tsum_out_mul_right ((blockShape r t).parabolic F)
    (g := fun y => twisted φ s (AdelicGL.rational F (r + t + 2) y * g))
    (fun p hp x => by
      simp only [map_mul, mul_assoc]
      exact twisted_rational_mul hφ s p hp _) c₁
  simpa [map_mul, mul_assoc] using this

/-- Normal convergence of the Eisenstein sum at `s` on compact sets, for `Re s > σ`. -/
def NormalBound (φ : AdelicGL F (r + t + 2) → ℂ) (σ : ℝ) : Prop :=
  ∀ s : ℂ, σ < s.re → ∀ C : Set (AdelicGL F (r + t + 2)), IsCompact C →
    ∃ b : Quotient (QuotientGroup.rightRel ((blockShape r t).parabolic F)) → ℝ, Summable b ∧
      ∀ c, ∀ g ∈ C, ‖twisted φ s (AdelicGL.rational F (r + t + 2) (Quotient.out c) * g)‖ ≤ b c

theorem exists_normalBound (hφ : IsSection T T' φ) : ∃ σ : ℝ, NormalBound φ σ := by
  obtain ⟨σ, hσ⟩ := exists_summable_eisensteinTerm_bound hφ
  refine ⟨σ, fun s hs C hC => ?_⟩
  obtain ⟨b, hb, hbound⟩ := hσ C hC {s} isCompact_singleton (by simpa using hs)
  exact ⟨b, hb, fun c g hg => hbound c g hg s rfl⟩

variable {σ : ℝ}

omit [CompactSpace (AdeleQuotient F)] in
theorem summable_norm_twisted (hσ : NormalBound φ σ) {s : ℂ} (hs : σ < s.re)
    (g : AdelicGL F (r + t + 2)) :
    Summable fun c : Quotient (QuotientGroup.rightRel ((blockShape r t).parabolic F)) =>
      ‖twisted φ s (AdelicGL.rational F (r + t + 2) (Quotient.out c) * g)‖ := by
  obtain ⟨b, hb, hbound⟩ := hσ s hs {g} isCompact_singleton
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun c => hbound c g rfl) hb

/-- The Eisenstein sum is continuous on the half-plane of normal convergence. -/
theorem continuous_eisensteinSeries (hφ : IsSection T T' φ) (hσ : NormalBound φ σ) {s : ℂ}
    (hs : σ < s.re) : Continuous (eisensteinSeries F φ s) := by
  let h := adelicHomeomorph F (r + t + 2)
  suffices hc : Continuous (eisensteinSeries F φ s ∘ h) by
    have : eisensteinSeries F φ s = (eisensteinSeries F φ s ∘ h) ∘ h.symm := by
      funext g
      simp
    rw [this]
    exact hc.comp h.symm.continuous
  rw [continuous_iff_continuousAt]
  intro y
  obtain ⟨K, hK, hKy⟩ := exists_compact_mem_nhds y
  obtain ⟨b, hb, hbound⟩ := hσ s hs (h '' K) (hK.image h.continuous)
  have hon : ContinuousOn (eisensteinSeries F φ s ∘ h) K := by
    have : eisensteinSeries F φ s ∘ h = fun z => ∑' c : Quotient (QuotientGroup.rightRel
        ((blockShape r t).parabolic F)),
        twisted φ s (AdelicGL.rational F (r + t + 2) (Quotient.out c) * h z) := by
      funext z
      rfl
    rw [this]
    refine continuousOn_tsum (fun c => ?_) hb (fun c z hz => hbound c (h z) ⟨z, hz, rfl⟩)
    exact ((continuous_twisted hφ s).comp (continuous_const.mul h.continuous)).continuousOn
  exact hon.continuousAt hKy

/-- The term of the Eisenstein sum at the coset `P(F) γ_J δ`. -/
def cellTerm (φ : AdelicGL F (r + t + 2) → ℂ) (s : ℂ) (J : PivotIndex (r + t + 2) (r + 1))
    (q : StabilizerCosets (K := F) J.1) (g : AdelicGL F (r + t + 2)) : ℂ :=
  twisted φ s (AdelicGL.rational F (r + t + 2)
    (cellRep r t F J.1 * ((Quotient.out q : GeneralLinear.upperUnipotent (r + t + 2) F) :
      RationalGL F (r + t + 2))) * g)

theorem cellTerm_eq (hφ : IsSection T T' φ) (s : ℂ)
    (x : Σ J : PivotIndex (r + t + 2) (r + 1), StabilizerCosets (K := F) J.1)
    (g : AdelicGL F (r + t + 2)) :
    twisted φ s (AdelicGL.rational F (r + t + 2)
      (Quotient.out (Equiv.ofBijective _ (cellOrbitMap_bijective r t F) x)) * g) =
      cellTerm φ s x.1 x.2 g := by
  obtain ⟨p, hp, hpx⟩ := exists_out_mul ((blockShape r t).parabolic F) (cellRep r t F x.1.1)
    ((Quotient.out x.2 : GeneralLinear.upperUnipotent (r + t + 2) F) : RationalGL F (r + t + 2))
  change twisted φ s (AdelicGL.rational F (r + t + 2) (Quotient.out (Quotient.mk _ _)) * g) = _
  rw [hpx, map_mul, mul_assoc, twisted_rational_mul hφ s p hp]
  rfl

theorem summable_norm_cellTerm_sigma (hφ : IsSection T T' φ) (hσ : NormalBound φ σ) {s : ℂ}
    (hs : σ < s.re) (g : AdelicGL F (r + t + 2)) :
    Summable (fun x : Σ J : PivotIndex (r + t + 2) (r + 1), StabilizerCosets (K := F) J.1 =>
      ‖cellTerm φ s x.1 x.2 g‖) ∧
    ∑' x : Σ J : PivotIndex (r + t + 2) (r + 1), StabilizerCosets (K := F) J.1,
      ‖cellTerm φ s x.1 x.2 g‖ =
      ∑' c : Quotient (QuotientGroup.rightRel ((blockShape r t).parabolic F)),
        ‖twisted φ s (AdelicGL.rational F (r + t + 2) (Quotient.out c) * g)‖ := by
  let e := Equiv.ofBijective _ (cellOrbitMap_bijective r t F)
  have h1 := summable_norm_twisted hσ hs g
  have heq : (fun x : Σ J : PivotIndex (r + t + 2) (r + 1), StabilizerCosets (K := F) J.1 =>
      ‖cellTerm φ s x.1 x.2 g‖) = (fun c => ‖twisted φ s (AdelicGL.rational F (r + t + 2)
        (Quotient.out c) * g)‖) ∘ e := by
    funext x
    exact congrArg norm (cellTerm_eq hφ s x g).symm
  rw [heq]
  exact ⟨e.summable_iff.mpr h1, e.tsum_eq (fun c => ‖twisted φ s (AdelicGL.rational F
    (r + t + 2) (Quotient.out c) * g)‖)⟩

theorem cellTerm_fiber_le (hφ : IsSection T T' φ) (hσ : NormalBound φ σ) {s : ℂ}
    (hs : σ < s.re) (J : PivotIndex (r + t + 2) (r + 1)) (g : AdelicGL F (r + t + 2)) :
    Summable (fun q : StabilizerCosets (K := F) J.1 => ‖cellTerm φ s J q g‖) ∧
    ∑' q : StabilizerCosets (K := F) J.1, ‖cellTerm φ s J q g‖ ≤
      ∑' c : Quotient (QuotientGroup.rightRel ((blockShape r t).parabolic F)),
        ‖twisted φ s (AdelicGL.rational F (r + t + 2) (Quotient.out c) * g)‖ := by
  obtain ⟨hsum, htsum⟩ := summable_norm_cellTerm_sigma hφ hσ hs g
  have hf : Summable (fun q : StabilizerCosets (K := F) J.1 => ‖cellTerm φ s J q g‖) :=
    hsum.sigma_factor J
  refine ⟨hf, ?_⟩
  rw [← htsum]
  exact Summable.tsum_le_tsum_of_inj (fun q => (⟨J, q⟩ : Σ J : PivotIndex (r + t + 2) (r + 1),
      StabilizerCosets (K := F) J.1)) (fun q q' h => eq_of_heq (Sigma.mk.inj h).2)
    (fun _ _ => norm_nonneg _) (fun _ => le_rfl) hf hsum

/-- **The Eisenstein sum over the cells.** -/
theorem eisensteinSeries_eq_sum_cells (hφ : IsSection T T' φ) (hσ : NormalBound φ σ) {s : ℂ}
    (hs : σ < s.re) (g : AdelicGL F (r + t + 2)) :
    eisensteinSeries F φ s g = ∑ J : PivotIndex (r + t + 2) (r + 1),
      ∑' q : StabilizerCosets (K := F) J.1, cellTerm φ s J q g := by
  have hsum : Summable (fun x : Σ J : PivotIndex (r + t + 2) (r + 1),
      StabilizerCosets (K := F) J.1 => cellTerm φ s x.1 x.2 g) :=
    Summable.of_norm (summable_norm_cellTerm_sigma hφ hσ hs g).1
  rw [eisensteinSeries_eq_tsum, ← (Equiv.ofBijective _ (cellOrbitMap_bijective r t F)).tsum_eq]
  have hfun := fun x => cellTerm_eq hφ s x g
  simp only [hfun]
  rw [hsum.tsum_sigma, tsum_fintype]

/-- **A uniform bound on `N₀(𝔸)`.** -/
theorem exists_bound_unipotent (hφ : IsSection T T' φ) (hσ : NormalBound φ σ) {s : ℂ}
    (hs : σ < s.re) : ∃ B : ℝ, ∀ x : RankinSelbergGlobal.unipotentAdelic F (r + t + 2),
      ∑' c : Quotient (QuotientGroup.rightRel ((blockShape r t).parabolic F)),
        ‖twisted φ s (AdelicGL.rational F (r + t + 2) (Quotient.out c) *
          Unfolding.toMat F (r + t + 2) x)‖ ≤ B := by
  obtain ⟨K, hK, hcover⟩ := Unfolding.exists_isCompact_pattern_cover F (r + t + 2) ∅
  let C := (fun y : Unfolding.pattern F (r + t + 2) ∅ => Unfolding.toMat F (r + t + 2) y.1) '' K
  have hC : IsCompact C :=
    hK.image ((Unfolding.continuous_toMat F (r + t + 2)).comp continuous_subtype_val)
  obtain ⟨b, hb, hbound⟩ := hσ s hs C hC
  refine ⟨∑' c, b c, fun x => ?_⟩
  have hx : x ∈ Unfolding.pattern F (r + t + 2) ∅ :=
    (Unfolding.mem_pattern_iff F (r + t + 2) ∅ x).mpr (by simp)
  obtain ⟨c, hc, hcK⟩ := hcover ⟨x, hx⟩
  obtain ⟨δ, hδ⟩ := (Unfolding.mem_Γ₀_iff F (r + t + 2) (c : RankinSelbergGlobal.unipotentAdelic
    F (r + t + 2))).mp hc
  set y := Unfolding.toMat F (r + t + 2) ((c * ⟨x, hx⟩ : Unfolding.pattern F (r + t + 2) ∅) :
    RankinSelbergGlobal.unipotentAdelic F (r + t + 2)) with hy
  have hyC : y ∈ C := ⟨_, hcK, rfl⟩
  have hxy : Unfolding.toMat F (r + t + 2) x =
      AdelicGL.rational F (r + t + 2) ((δ : RationalGL F (r + t + 2))⁻¹) * y := by
    rw [hy, Subgroup.coe_mul, map_mul, ← hδ, Unfolding.toMat_ratHom, ← mul_assoc, ← map_mul,
      inv_mul_cancel, map_one, one_mul]
  have hreindex := tsum_out_mul_right ((blockShape r t).parabolic F)
    (g := fun z => ‖twisted φ s (AdelicGL.rational F (r + t + 2) z * y)‖)
    (fun p hp z => by
      simp only [map_mul, mul_assoc]
      rw [twisted_rational_mul hφ s p hp]) ((δ : RationalGL F (r + t + 2))⁻¹)
  simp only [map_mul, mul_assoc] at hreindex
  rw [hxy, hreindex]
  exact Summable.tsum_le_tsum (fun q => hbound q y hyC) (summable_norm_twisted hσ hs y) hb

end Series

end Langlands.Global.CuspidalPairEisenstein

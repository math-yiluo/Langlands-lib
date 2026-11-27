import Langlands.Global.AdelicCuspidalExponentLineBound
import Langlands.Global.AdelicConstantTermAutomorphyProof
import Langlands.Global.AdelicLeviCuspFormRapidDecayProof
import Langlands.Automorphic.GroupSchemeInvariantFunctionGrowth

/-! # Boundedness on Levi Siegel regions of a form with only negative maximal cuspidal exponents

An automorphic function `f` on `U_R(𝔸) M_R(F) \ G(𝔸)` whose constant terms along the maximal
parabolics `R \ {α}` of `M_R` decompose into cuspidal components with exponents pairing negatively
with the remaining simple coroot is bounded on Siegel regions of `M_R`. Where the root `α` is the
largest simple root of `R` at the torus point, `f - C_{R \ {α}} f` is small by the maximal-parabolic
decay (`shiftedMaximalDecay`) and each component of `C_{R \ {α}} f` is bounded
(`cuspidalExponentLineBound`); where all simple roots of `R` are at most `1`, the height is
bounded. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry NumberField Set TensorProduct
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints InfiniteAdelicGroupPoints PositiveRealTorus AdelicSiegelFactors
  RepresentationGrowth Langlands.Geometry.Manifold

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "A" => AdelicGroupPoints F G
local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "aG" => positiveMap F G 𝓕.T 𝓕.i 𝓕.T (𝟙 𝓕.T)

section Data

variable {d N : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom) (rho : MatrixRepresentation G (Fin N))

local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "B₀" => (Subtype.mk ∅ (empty_subset (simpleRelativeRoots 𝓕.i 𝓕.ν)) : Idx)
local notation "height" => adelicHeight F G rho

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- A derivative word of the difference of two functions which are smooth on the archimedean
slices is the difference of the derivative words. -/
theorem adelicIteratedDirectionalValue_sub_of_smoothSlices (s : List W) (f g : A → ℂ) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    (∀ b : Gf, ContMDiff IG IC ∞ (fun y : G∞ => f (pair F G y b))) →
    (∀ b : Gf, ContMDiff IG IC ∞ (fun y : G∞ => g (pair F G y b))) →
    adelicIteratedDirectionalValue hG s (f - g) =
      adelicIteratedDirectionalValue hG s f - adelicIteratedDirectionalValue hG s g := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  intro hf hg
  let B := manifoldSmoothFunctions F G hG
  let d₀ (X : W) : Module.End ℂ B :=
    { toFun := fun h => ⟨groupDirectionalValue IG X h.val, contMDiff_groupDirectionalValue IG X h.prop⟩
      map_add' := fun h k => Subtype.ext (funext fun x => groupDirectionalValue_add IG X h.prop k.prop x)
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
  let fs : B := ⟨fun y => f (pair F G y b), hf b⟩
  let gs : B := ⟨fun y => g (pair F G y b), hg b⟩
  have hh : (fs - gs).val = fun y => (f - g) (pair F G y b) := rfl
  change adelicIteratedDirectionalValue hG s (f - g) (pair F G a b) = _
  rw [← show (D s (fs - gs)).val a = _ from congrFun (hslice s _ _ hh) a, map_sub]
  change (D s fs).val a - (D s gs).val a = _
  rw [congrFun (hslice s f fs rfl) a, congrFun (hslice s g gs rfl) a]
  rfl

/-- The derivative words of an automorphic function on `U_P(𝔸) M_P(F) \ G(𝔸)` have a common
polynomial growth exponent in the height (`exists_uniformGrowth_functionInfiniteSlices`). -/
theorem exists_derivativeGrowth_of_automorphicOn (hN : 0 < N)
    {Kinf : Subgroup G∞} (hKinf : Langlands.CompactIwasawa.IsMaximalCompact Kinf) (P : Idx)
    {φ : A → ℂ} (hφ : 𝓕.IsAutomorphicOn hG Kinf rho P φ) :
    ∃ e : ℝ, 0 ≤ e ∧ ∀ s : List W, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, ‖adelicIteratedDirectionalValue hG s φ x‖ ≤ C * height x ^ e := by
  obtain ⟨-, hsm, hKfin, hZ, hgrowth⟩ := hφ
  obtain ⟨e, he, hderiv⟩ := exists_uniformGrowth_functionInfiniteSlices F G hG
    (adelicDifferentialCommutator_of_smooth F G hG) rho hN 𝓕.connectedReductive Kinf hKinf φ
    hsm.2.1 hKfin hZ hgrowth
  refine ⟨e, he, fun s => ?_⟩
  obtain ⟨C, hC, hb⟩ := hderiv (adelicDirectionalWordEnveloping hG s)
  refine ⟨C, hC, fun x => ?_⟩
  rw [← pair_projections F G x, plotSmoothEnvelopingAction_directionalWord_slice hG
    (adelicDifferentialCommutator_of_smooth F G hG) s φ _ (hsm.2.1 _)]
  exact hb _ _

/-- The elementary properties of an automorphic function on `U_P(𝔸) M_P(F) \ G(𝔸)` used by the
decay estimates: continuity, smoothness on the archimedean slices, left invariance under `P_0(F)`
and `U_P(𝔸)`, and right invariance under an open finite level. -/
theorem IsAutomorphicOn.regularData {Kinf : Subgroup G∞} {P : Idx} {φ : A → ℂ}
    (hφ : 𝓕.IsAutomorphicOn hG Kinf rho P φ) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    Continuous φ ∧ (∀ b : Gf, ContMDiff IG IC ∞ (fun y : G∞ => φ (pair F G y b))) ∧
      (∀ r ∈ rationalImage F (𝓕.p B₀), ∀ x, φ (r * x) = φ x) ∧ 𝓕.IsRadicalInvariant P φ ∧
      ∃ L : Subgroup Gf, IsOpen (L : Set Gf) ∧ ∀ l ∈ L, ∀ x, φ (x * ofFinite F G l) = φ x := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  obtain ⟨hinv, ⟨hc, hs, L, hL, hlev⟩, -⟩ := hφ
  refine ⟨hc, fun b => (InfiniteAdelicGroupPoints.isPlotSmooth_iff_contMDiff F G hG _).mp (hs b),
    fun r hr x => hinv r (𝓕.rationalImage_le_parabolicQuotientSubgroup_of_le
      (empty_subset P.1) hr) x, fun u x => ?_, L, hL, hlev⟩
  obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp u.property
  exact hinv _ (Subgroup.mem_sup_left ⟨w, hw⟩) x

/-- The constant term along `Q` of the difference of two continuous functions, invariant under
`U_P(𝔸) M_P(F)` and `U_{P'}(𝔸) M_{P'}(F)` for standard `P, P' ⊇ Q`, is the difference of their
constant terms. -/
theorem constantTerm_sub_of_le {Q P P' : Idx} (hQP : Q ≤ P) (hQP' : Q ≤ P') {f₁ f₂ : A → ℂ}
    (h₁ : Continuous f₁)
    (h₁i : ∀ y ∈ parabolicQuotientSubgroup F (𝓕.p P) (𝓕.iU P) (𝓕.l P), ∀ x, f₁ (y * x) = f₁ x)
    (h₂ : Continuous f₂)
    (h₂i : ∀ y ∈ parabolicQuotientSubgroup F (𝓕.p P') (𝓕.iU P') (𝓕.l P'), ∀ x, f₂ (y * x) = f₂ x) :
    𝓕.constantTerm Q (f₁ - f₂) = 𝓕.constantTerm Q f₁ - 𝓕.constantTerm Q f₂ := by
  funext x
  have hif := 𝓕.integrable_constantTermIntegrand_of_le P Q hQP h₁ h₁i x
  have hig := 𝓕.integrable_constantTermIntegrand_of_le P' Q hQP' h₂ h₂i x
  unfold constantTerm subgroupConstantTerm
  simpa only [Pi.sub_apply] using MeasureTheory.integral_sub hif hig

end Data

section Region

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

/-- The `n`-th power of the decay factor `|α(a)|^{-1/[F:ℚ]}` as an exponential of the root
logarithm. -/
theorem relativeCharacterDecay_pow_eq_exp (α : characterLattice 𝓕.T)
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

/-- **Boundedness on Levi Siegel regions of a form with only negative maximal cuspidal
exponents.** Let `rho` be a closed matrix embedding of positive size, `Kinf` a maximal compact
subgroup of `G(F_∞)` and `f` an automorphic function on `U_R(𝔸) M_R(F) \ G(𝔸)`. Suppose that for
every simple root `α ∈ R` the constant term of `f` along the maximal parabolic `Q_α = R \ {α}` of
`M_R` has an exponent decomposition `C_{Q_α} f = ∑_{μ ∈ s} c μ` whose nonzero components have
unnormalized exponents `μ` with `R = Q_α ∪ {β}`, `β ∉ Q_α`, and `⟨Re μ, β^∨⟩ < 0`. Let `Φ` be a
set of real linear forms on `𝔞_0`, annihilated by the coroots of `R`, which together with the
simple roots of `R` spans `𝔞_0^*`. Then `f` is bounded on the region of points `p a k` with `p` in
a compact subset of `P_0(𝔸)`, the normalized adelic norms of the simple roots of `R` at the
positive torus point `a` at least a fixed `b > 0`, the forms of `Φ` bounded by `B ≥ 0` at the
logarithm of `a`, `k` in a compact set and the finite part in a compact set. -/
def CuspidalExponentRegionBoundStatement : Prop :=
  0 < N → IsClosedSubgroup rho →
  ∀ (Kinf : Subgroup G∞), Langlands.CompactIwasawa.IsMaximalCompact Kinf →
  ∀ (R : Idx) (f : A → ℂ), 𝓕.IsAutomorphicOn hG Kinf rho R f →
  ∀ (s : ∀ Q : Idx, Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (c : ∀ Q : Idx, ComplexCharacterParameter F (𝓕.P Q) → A → ℂ),
    (∀ α ∈ R.1, 𝓕.IsExponentDecomposition hG Kinf rho (𝓕.removeSimpleRoot R α)
      (𝓕.constantTerm (𝓕.removeSimpleRoot R α) f) (s (𝓕.removeSimpleRoot R α))
      (c (𝓕.removeSimpleRoot R α))) →
    (∀ α ∈ R.1, ∀ mu ∈ s (𝓕.removeSimpleRoot R α), c (𝓕.removeSimpleRoot R α) mu ≠ 0 →
      ∃ β : relativeRoots 𝓕.i, β.1 ∉ (𝓕.removeSimpleRoot R α).1 ∧
        insert β.1 (𝓕.removeSimpleRoot R α).1 = R.1 ∧
        pair 𝓕.T (𝓕.realExponent (𝓕.removeSimpleRoot R α) mu)
          ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot β) < 0) →
  ∀ (Φ : Set (Vstar 𝓕.T)),
    Submodule.span ℝ (((fun χ₀ : characterLattice 𝓕.T => (1 : ℝ) ⊗ₜ[ℤ] χ₀) '' R.1) ∪ Φ) = ⊤ →
    Φ ⊆ corootAnnihilator 𝓕.i 𝓕.coroots R.1 →
  ∀ (b : ℝ≥0ˣ) (B : ℝ), 0 ≤ B →
  ∀ (Ω K : Set A), IsCompact Ω → IsCompact K →
    Ω ⊆ ((map F (𝓕.P B₀) G (𝓕.p B₀)).toMonoidHom.range : Set A) →
  ∀ (Yf : Set Gf), IsCompact Yf →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Ω, ∀ (a : intrinsicSubgroup F 𝓕.T) (H : V 𝓕.T),
      cocharacterFunctional H = characterLog F 𝓕.T.toGrp a.val →
      (∀ ρ₁ ∈ R.1, b ≤ normCharacter F 𝓕.T ρ₁ a) →
      (∀ φ ∈ Φ, |pair 𝓕.T φ H| ≤ B) →
      ∀ k ∈ K, finite F G (p * aG a * k) ∈ Yf → ‖f (p * aG a * k)‖ ≤ C

theorem cuspidalExponentRegionBound : 𝓕.CuspidalExponentRegionBoundStatement hG rho := by
  intro hN hrho Kinf hKinf R f hf s c hdec hexp Φ hspan hΦR b B hB Ω K hΩ hK hΩP Yf hYf
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  have hRf : R.val.Finite :=
    (𝓕.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots 𝓕.i 𝓕.ν).subset R.2
  let : Fintype R.val := hRf.fintype
  let Qα (α : R.val) : Idx := 𝓕.removeSimpleRoot R α.1
  have hQR (α : R.val) : Qα α ≤ R := (𝓕.removeSimpleRoot_lt R α.2).le
  -- the data of `f` and of its constant terms
  obtain ⟨hfc, hfS, hfR, hfU, Lf, hLf, hfL⟩ := IsAutomorphicOn.regularData 𝓕 hG rho hf
  obtain ⟨ef, hef, hfgrowth⟩ := 𝓕.exists_derivativeGrowth_of_automorphicOn hG rho hN hKinf R hf
  have hCQ (α : R.val) : 𝓕.IsAutomorphicOn hG Kinf rho (Qα α) (𝓕.constantTerm (Qα α) f) :=
    constantTermAutomorphy F G 𝓕 Kinf rho hG hrho R (Qα α) (hQR α) f hf
  have hCdata (α : R.val) := IsAutomorphicOn.regularData 𝓕 hG rho (hCQ α)
  choose hCc hCS hCR hCU hCdataL using hCdata
  choose LC hLC hCL using hCdataL
  have hCgrowth (α : R.val) :=
    𝓕.exists_derivativeGrowth_of_automorphicOn hG rho hN hKinf (Qα α) (hCQ α)
  choose eC heC hCgr using hCgrowth
  let e : ℝ := ef + ∑ α, eC α
  have hsumC : 0 ≤ ∑ α, eC α := Finset.sum_nonneg fun α _ => heC α
  have he : 0 ≤ e := add_nonneg hef hsumC
  have hH1 (x : A) : 1 ≤ height x := one_le_adelicHeight F G rho hN x
  have hraise {e' : ℝ} (he' : e' ≤ e) (C : ℝ) (hC : 0 ≤ C) (x : A) :
      C * height x ^ e' ≤ C * height x ^ e :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hH1 x) he') hC
  -- the remainders `g_α = f - C_{Q_α} f`
  let g (α : R.val) : A → ℂ := f - 𝓕.constantTerm (Qα α) f
  have hgGrowth (α : R.val) (w : List W) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, ‖adelicIteratedDirectionalValue hG w (g α) x‖ ≤ C * height x ^ e := by
    obtain ⟨C₁, hC₁, h₁⟩ := hfgrowth w
    obtain ⟨C₂, hC₂, h₂⟩ := hCgr α w
    refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun x => ?_⟩
    have hsub := adelicIteratedDirectionalValue_sub_of_smoothSlices hG w f (𝓕.constantTerm (Qα α) f) hfS (hCS α)
    have hle1 : ef ≤ e := le_add_of_nonneg_right hsumC
    have hle2 : eC α ≤ e := (Finset.single_le_sum (f := eC) (fun α _ => heC α)
      (Finset.mem_univ α)).trans (le_add_of_nonneg_left hef)
    calc ‖adelicIteratedDirectionalValue hG w (g α) x‖
        = ‖adelicIteratedDirectionalValue hG w f x -
            adelicIteratedDirectionalValue hG w (𝓕.constantTerm (Qα α) f) x‖ := by
          rw [show g α = f - 𝓕.constantTerm (Qα α) f from rfl, hsub, Pi.sub_apply]
      _ ≤ C₁ * height x ^ ef + C₂ * height x ^ eC α := (norm_sub_le _ _).trans (add_le_add (h₁ x) (h₂ x))
      _ ≤ C₁ * height x ^ e + C₂ * height x ^ e :=
          add_le_add (hraise hle1 C₁ hC₁ x) (hraise hle2 C₂ hC₂ x)
      _ = (C₁ + C₂) * height x ^ e := by ring
  let Lα (α : R.val) : Subgroup Gf := Lf ⊓ LC α
  have hLα (α : R.val) : IsOpen (Lα α : Set Gf) := hLf.inter (hLC α)
  have hgc (α : R.val) : Continuous (g α) := hfc.sub (hCc α)
  have hgS (α : R.val) (y : Gf) : ContMDiff IG IC ∞ (fun x : G∞ => g α (pair F G x y)) :=
    (hfS y).sub (hCS α y)
  have hgR (α : R.val) : ∀ r ∈ rationalImage F (𝓕.p B₀), ∀ x, g α (r * x) = g α x := by
    intro r hr x
    simp only [g, Pi.sub_apply]
    rw [hfR r hr x, hCR α r hr x]
  have hgU (α : R.val) : 𝓕.IsRadicalInvariant R (g α) := by
    intro u x
    simp only [g, Pi.sub_apply]
    rw [hfU u x, hCU α ⟨u.1, 𝓕.radical_le_of_le (hQR α) _ u.2⟩ x]
  have hgL (α : R.val) : ∀ l ∈ Lα α, ∀ x, g α (x * ofFinite F G l) = g α x := by
    intro l hl x
    simp only [g, Pi.sub_apply]
    rw [hfL l hl.1 x, hCL α l hl.2 x]
  have hgCT (α : R.val) : 𝓕.constantTerm (𝓕.removeSimpleRoot R α.1) (g α) = 0 := by
    change 𝓕.constantTerm (Qα α) (f - 𝓕.constantTerm (Qα α) f) = 0
    rw [𝓕.constantTerm_sub_of_le (hQR α) le_rfl hfc hf.1 (hCc α) (hCQ α).1,
      𝓕.constantTerm_eq_self_of_automorphicOn (Qα α) (hCQ α), sub_self]
  -- the bounds of the cuspidal exponent components
  have hline (α : R.val) (mu : ComplexCharacterParameter F (𝓕.P (Qα α))) : ∃ C : ℝ, 0 ≤ C ∧
      (mu ∈ s (Qα α) → ∀ p ∈ Ω, ∀ (a : intrinsicSubgroup F 𝓕.T) (H : V 𝓕.T),
        cocharacterFunctional H = characterLog F 𝓕.T.toGrp a.val →
        (∀ ρ₁ ∈ R.1, b ≤ normCharacter F 𝓕.T ρ₁ a) →
        (∀ φ ∈ Φ, |pair 𝓕.T φ H| ≤ B) →
        ∀ k ∈ K, finite F G (p * aG a * k) ∈ Yf → ‖c (Qα α) mu (p * aG a * k)‖ ≤ C) := by
    by_cases hmu : mu ∈ s (Qα α)
    swap
    · exact ⟨0, le_rfl, fun h => absurd h hmu⟩
    by_cases hc0 : c (Qα α) mu = 0
    · exact ⟨0, le_rfl, fun _ p _ a H _ _ _ k _ _ => by rw [hc0]; simp⟩
    obtain ⟨β, hβQ, hins, hneg⟩ := hexp α.1 α.2 mu hmu hc0
    have hdα := hdec α.1 α.2
    have hcA := hdα.automorphic mu hmu
    obtain ⟨hcc, hcS, hcR, hcU, Lc, hLc, hcL⟩ := IsAutomorphicOn.regularData 𝓕 hG rho hcA
    obtain ⟨ec, hec, hcgrowth⟩ :=
      𝓕.exists_derivativeGrowth_of_automorphicOn hG rho hN hKinf (Qα α) hcA
    obtain ⟨C, hC, hbd⟩ := 𝓕.cuspidalExponentLineBound hG rho hN (Qα α) R β hβQ hins Φ hspan
      hΦR b B hB Ω K hΩ hK hΩP Yf hYf Lc hLc mu (c (Qα α) mu) hcc hcS hcR hcU hcL
      (fun ρ₁ hρ₁ => hdα.cuspidal mu hmu _ (𝓕.removeSimpleRoot_lt _ hρ₁)) ec hec hcgrowth
      (hdα.exponent mu hmu) hneg
    exact ⟨C, hC, fun _ => hbd⟩
  choose Cl hCl hlb using hline
  let Sα (α : R.val) : ℝ := ∑ mu ∈ s (Qα α), Cl α mu
  have hSα (α : R.val) : 0 ≤ Sα α := Finset.sum_nonneg fun mu _ => hCl α mu
  -- the decay of the remainders
  let B₁ := max B (-Real.log ((b : ℝ≥0) : ℝ))
  obtain ⟨C₀, r, hC₀, hr, hAheight⟩ := 𝓕.exists_regionHeight_bound rho hN R.1 Φ hspan b
  let D := (Module.finrank ℚ F : ℝ)
  have hD : 0 < D := Nat.cast_pos.mpr Module.finrank_pos
  obtain ⟨n, hn⟩ := exists_nat_gt (D * (r * e))
  have hn' : r * e ≤ (n : ℝ) / D :=
    (le_div_iff₀ hD).mpr (by simpa only [mul_comm] using hn.le)
  have hFiniteWords := fun (α : R.val) (w : Fin n → Jw) => hgGrowth α ((List.ofFn w).map basisG)
  choose Cw hCw hw using hFiniteWords
  let Wn (α : R.val) := ∑ w, Cw α w
  have hWn (α : R.val) : 0 ≤ Wn α := Finset.sum_nonneg fun w _ => hCw α w
  have hWord (α : R.val) (l : List Jw) (hl : l.length = n) (x : A) :
      ‖adelicIteratedDirectionalValue hG (l.map basisG) (g α) x‖ ≤ Wn α * height x ^ e := by
    let w : Fin n → Jw := fun j => l.get (Fin.cast hl.symm j)
    have hws : List.ofFn w = l := by
      subst n
      exact List.ofFn_get l
    rw [← hws]
    exact (hw α w x).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := Cw α) (fun w _ => hCw α w) (Finset.mem_univ _))
      (Real.rpow_nonneg (zero_le_one.trans (hH1 x)) _))
  have hdecay (α : R.val) := 𝓕.shiftedMaximalDecay hG rho hN R α.2 b n e he Ω K hΩ hK hΩP
    Yf hYf (Lα α) (hLα α)
  choose Cα hCα hiter using hdecay
  obtain ⟨E₀, hE₀, hEbase⟩ := exists_compact_factors_height_bound rho hN Ω K hΩ hK
  let A₀ := C₀ * Real.exp (r * B₁)
  have hA₀ : 0 < A₀ := mul_pos (zero_lt_one.trans_le hC₀) (Real.exp_pos _)
  let D₀ := E₀ * A₀
  have hD₀ : 0 < D₀ := mul_pos (zero_lt_one.trans_le hE₀) hA₀
  obtain ⟨Cbase, hCbase, hbase⟩ := hfgrowth []
  let Base := Cbase * D₀ ^ ef
  let Tail (α : R.val) := Cα α * Wn α * A₀ ^ e + Sα α
  have hBase : 0 ≤ Base := mul_nonneg hCbase (Real.rpow_nonneg hD₀.le _)
  have hTail (α : R.val) : 0 ≤ Tail α :=
    add_nonneg (mul_nonneg (mul_nonneg (hCα α) (hWn α)) (Real.rpow_nonneg hA₀.le _)) (hSα α)
  refine ⟨Base + ∑ α, Tail α, add_nonneg hBase (Finset.sum_nonneg fun α _ => hTail α), ?_⟩
  intro p hp a H hH hlo hza k hk hx
  let lb : Option R.val → ℝ := fun α => α.elim 0 (fun y => logNormHom F 𝓕.T a.val y.val)
  obtain ⟨o, _, ho⟩ := Finset.exists_max_image Finset.univ lb ⟨none, Finset.mem_univ _⟩
  have hmax₀ : 0 ≤ lb o := ho none (Finset.mem_univ _)
  have hmaxR : ∀ α ∈ R.val, logNormHom F 𝓕.T a.val α ≤ lb o := fun α hα =>
    ho (some ⟨α, hα⟩) (Finset.mem_univ _)
  have hha := hAheight a H B (lb o) hH hB hmax₀ hlo hmaxR hza
  have hha' : height (aG a) ≤ A₀ * Real.exp (r * lb o) := by
    rw [mul_assoc, ← Real.exp_add, ← mul_add]
    exact hha
  let x := p * aG a * k
  have hxH : 0 < height x := zero_lt_one.trans_le (hH1 x)
  have haH : 0 < height (aG a) := zero_lt_one.trans_le (hH1 _)
  have hxle : height x ≤ E₀ * height (aG a) := hEbase p hp _ k hk
  cases o with
  | none =>
    have hha0 : height (aG a) ≤ A₀ := by
      simpa only [lb, Option.elim_none, mul_zero, Real.exp_zero, mul_one] using hha'
    have hdx : height x ≤ D₀ :=
      hxle.trans (mul_le_mul_of_nonneg_left hha0 (zero_le_one.trans hE₀))
    calc
      ‖f x‖ ≤ Cbase * height x ^ ef := by simpa using hbase x
      _ ≤ Base := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hxH.le hdx hef) hCbase
      _ ≤ Base + ∑ α, Tail α := le_add_of_nonneg_right (Finset.sum_nonneg fun α _ => hTail α)
  | some α =>
    let t := logNormHom F 𝓕.T a.val α.val
    have ht : 0 ≤ t := hmax₀
    have hgdec := hiter α (g α) (hgc α) (hgS α) (hgR α) (hgU α) (hgL α) (hgCT α) (Wn α) (hWn α)
      (hWord α) p hp a hlo k hk hx
    have hHt : height (aG a) ≤ A₀ * Real.exp (r * t) := hha'
    have hExpo : relativeCharacterDecay (𝟙 𝓕.T) α.val a ^ n * height (aG a) ^ e ≤ A₀ ^ e := by
      have h1 : height (aG a) ^ e ≤ (A₀ * Real.exp (r * t)) ^ e :=
        Real.rpow_le_rpow haH.le hHt he
      rw [Real.mul_rpow hA₀.le (Real.exp_pos _).le, ← Real.exp_mul] at h1
      rw [relativeCharacterDecay_pow_eq_exp 𝓕]
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
    have hrel := (relativeCharacterDecay_pos (𝟙 𝓕.T) α.val a).le
    have hgbound : ‖g α x‖ ≤ Cα α * Wn α * A₀ ^ e :=
      calc ‖g α x‖ ≤ Cα α * relativeCharacterDecay (𝟙 𝓕.T) α.val a ^ n * Wn α *
            height (aG a) ^ e := hgdec
        _ = Cα α * Wn α * (relativeCharacterDecay (𝟙 𝓕.T) α.val a ^ n * height (aG a) ^ e) := by
            ring
        _ ≤ Cα α * Wn α * A₀ ^ e :=
            mul_le_mul_of_nonneg_left hExpo (mul_nonneg (hCα α) (hWn α))
    have hCbound : ‖𝓕.constantTerm (Qα α) f x‖ ≤ Sα α := by
      rw [(hdec α.1 α.2).sum_eq, Finset.sum_apply]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun mu hmu =>
        hlb α mu hmu p hp a H hH hlo hza k hk hx)
    have hfx : f x = g α x + 𝓕.constantTerm (Qα α) f x := by
      simp only [g, Pi.sub_apply, sub_add_cancel]
    calc
      ‖f x‖ ≤ ‖g α x‖ + ‖𝓕.constantTerm (Qα α) f x‖ := by rw [hfx]; exact norm_add_le _ _
      _ ≤ Tail α := add_le_add hgbound hCbound
      _ ≤ ∑ β, Tail β := Finset.single_le_sum (f := Tail) (fun β _ => hTail β) (Finset.mem_univ α)
      _ ≤ Base + ∑ β, Tail β := le_add_of_nonneg_left hBase

end Region

end Langlands.Global.StandardParabolicFamily

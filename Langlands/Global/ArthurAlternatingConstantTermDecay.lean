import Langlands.Global.ArthurAlternatingConstantTermGrowth
import Langlands.Global.ArthurSigmaTorusBounds
import Langlands.Global.AdelicStandardLeviContractionModulo
import Langlands.Global.AdelicRelativeCuspidalRapidDecay

/-! # Rapid decay of the alternating terms on the truncated sigma region -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory NumberField Set
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal Pointwise

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints InfiniteAdelicGroupPoints RepresentationGrowth PositiveRealTorus
  AdelicSiegelFactors ArthurParabolicSpaces StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {K : Subgroup (AdelicGroupPoints F G)}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (D : RelativeRootReflectionData i) (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))
  {d N : ℕ} (hSmooth : SmoothOfRelativeDimension d G.X.hom) (ρ : MatrixRepresentation G (Fin N))

local notation "A" => AdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "H" => adelicHeight F G ρ
local notation "Δ" => simpleFinset ν hG hi
local notation "J" => Finset (characterLattice T)
local notation "Pts" => intrinsicSubgroup F T
local notation "P₀" => MonoidHom.range
  (ContinuousMonoidHom.toMonoidHom (map F _ G (Standard.parabolicHom i ν ∅)))
local notation "aG" => positiveTorusMap F i

private theorem relativeCharacterDecay_pow_log (α : characterLattice T) (a : Pts) (n : ℕ) :
    relativeCharacterDecay (𝟙 T) α a ^ n =
      Real.exp (-(n : ℝ) / (Module.finrank ℚ F : ℝ) * logNormHom F T a.val α) := by
  have hpos : 0 < ((normCharacter F T ((𝟙 T) ≫ α) a : ℝ≥0) : ℝ) := by
    exact_mod_cast (normCharacter F T ((𝟙 T) ≫ α) a).ne_zero.bot_lt
  rw [relativeCharacterDecay, Real.rpow_def_of_pos hpos, ← Real.exp_nat_mul, Category.id_comp]
  change Real.exp (_ * (Real.log _ * _)) = Real.exp (_ * Real.log _)
  congr 1
  ring

include hν in
/-- On the cutoff region over the lower standard parabolic, each signed
interval of constant terms has arbitrary inverse powers of height. -/
theorem alternatingConstantTerm_rapidDecay (hN : 0 < N)
    (R S : J) (hRS : R ⊆ S) (hS : S ⊆ Δ) (T₁ Tp : V T)
    (Ω K' : Set A) (hΩ : IsCompact Ω) (hK' : IsCompact K') (hΩP : Ω ⊆ P₀)
    (f : FinitePlotSmoothRationalFunctions F G)
    (hf : HasAdelicUniformModerateGrowth F G ρ hSmooth
      (adelicDifferentialCommutator_of_smooth F G hSmooth) f) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Ω,
      ∀ a ∈ sigmaTorusRegion hG hi D hK hρ R S T₁ Tp, ∀ k ∈ K',
        ‖alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f.val) (p * aG a * k)‖ *
          H (p * aG a * k) ^ m ≤ C := by
  classical
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hSmooth
  let (v : InfinitePlace F) : FiniteDimensional ℝ v.Completion := inferInstance
  let g := alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f.val)
  obtain ⟨L, r, hL, hr, hg, hgSmooth, hgL, hGrowth⟩ :=
    alternatingConstantTerm_uniformGrowth hG hi hν hSmooth ρ hN R S hS f hf
  obtain ⟨B, C₀, t₀, hB, hC₀, ht₀, hTorus⟩ :=
    sigmaTorusRegion_bounds hG hi hν D hK hρ ρ hN R S hRS hS T₁ Tp
  let A₀ := simpleRelativeRoots i ν
  have hS₀ : (S : Set (characterLattice T)) ⊆ A₀ := fun α hα => (mem_simpleFinset hG hi).mp (hS hα)
  let b₀ : ℝ≥0 := ⟨Real.exp (-B), (Real.exp_pos _).le⟩
  have hb₀ : 0 < b₀ := NNReal.coe_pos.mp (Real.exp_pos _)
  let b : ℝ≥0ˣ := Units.mk0 b₀ hb₀.ne'
  let Ch := standardLeviWeakChamber F T (S : Set (characterLattice T)) b
  have hbLog : Real.log ((b : ℝ≥0) : ℝ) = -B := Real.log_exp _
  have hch (a : Pts) (ha : a ∈ sigmaTorusRegion hG hi D hK hρ R S T₁ Tp) : a ∈ Ch := by
    intro α hα
    rw [Category.id_comp]
    apply Units.val_le_val.mp
    apply NNReal.coe_le_coe.mp
    have ha0 : 0 < ((normCharacter F T α a : ℝ≥0) : ℝ) := by
      exact_mod_cast (normCharacter F T α a).ne_zero.bot_lt
    change Real.exp (-B) ≤ _
    rw [← Real.exp_log ha0]
    exact Real.exp_le_exp.mpr ((hTorus a ha).1 α hα)
  let Yf := (finite F G '' Ω) * (finite F G '' K')
  have hYf : IsCompact Yf := (hΩ.image (finite F G).continuous).mul (hK'.image (finite F G).continuous)
  have hxfin (p : A) (hp : p ∈ Ω) (a : Pts) (k : A) (hk : k ∈ K') :
      finite F G (p * aG a * k) ∈ Yf := by
    have ha := finite_positiveMap F G T i T (𝟙 T) hi.isSplitSubtorus.1 a
    rw [map_mul, map_mul, show finite F G (aG a) = 1 from ha, mul_one]
    exact Set.mul_mem_mul (mem_image_of_mem _ hp) (mem_image_of_mem _ hk)
  let Df : ℝ := Module.finrank ℚ F
  have hDf : 0 < Df := Nat.cast_pos.mpr Module.finrank_pos
  let e := r + (m : ℝ)
  have he : 0 ≤ e := add_nonneg hr (Nat.cast_nonneg _)
  obtain ⟨n, hn⟩ := exists_nat_gt (Df * (t₀ * e))
  have hn' : t₀ * e ≤ (n : ℝ) / Df := (le_div_iff₀ hDf).mpr (by simpa only [mul_comm] using hn.le)
  let I := Fin (Module.finrank ℝ W)
  let basisG := Module.finBasis ℝ W
  choose Cw hCw hw using fun w : Fin n → I => hGrowth ((List.ofFn w).map basisG)
  let Cword := ∑ w, Cw w
  have hCword : 0 ≤ Cword := Finset.sum_nonneg fun w _ => hCw w
  have hWord (s : List I) (hs : s.length = n) (x : A) :
      ‖adelicIteratedDirectionalValue hSmooth (s.map basisG) g x‖ ≤ Cword * H x ^ r := by
    let word : Fin n → I := fun j => s.get (Fin.cast hs.symm j)
    have hwEq : List.ofFn word = s := by subst n; exact List.ofFn_get s
    rw [← hwEq]
    exact (hw word x).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := Cw) (fun w _ => hCw w) (Finset.mem_univ _))
      (Real.rpow_nonneg (zero_le_one.trans (one_le_adelicHeight F G ρ hN x)) _))
  let R₀ := (map F _ G (Standard.unipotentHom i ν (S : Set (characterLattice T)))).toMonoidHom.range
  have hRad (z : A) (hz : z ∈ R₀) (x : A) : g (z * x) = g x :=
    alternatingConstantTerm_radical_mul hG hi hν hS f.val z hz x
  have hdecay (α : (S \ R : Finset (characterLattice T))) :
      ∃ K₁ : Set A, IsCompact K₁ ∧ K' ⊆ K₁ ∧ ∃ C₁ : ℝ, 0 ≤ C₁ ∧
        ∀ p ∈ Ω, ∀ a : Ch, ∀ k ∈ K', ∀ M : ℝ, 0 ≤ M →
          (∀ k₁ ∈ K₁, finite F G k₁ = finite F G k → ∀ s : List I, s.length = n →
            ‖adelicIteratedDirectionalValue hSmooth (s.map basisG) g (p * aG a.val * k₁)‖ ≤ M) →
          ‖g (p * aG a.val * k)‖ ≤ C₁ * (relativeCharacterDecay (𝟙 T) α.val a.val) ^ n * M := by
    let M := A₀ \ {α.val}
    let U := Standard.unipotentScheme i ν M
    let j := Standard.unipotentHom i ν M
    let : IsAffine U.X.left := @isAffine_of_isAffineHom _ _ U.X.hom
      (Standard.isClosedSubgroup_unipotentHom i ν M).isAffineHom_source inferInstance
    let : IsClosedImmersion j.hom.hom.left := Standard.isClosedSubgroup_unipotentHom i ν M
    let ε (a : Ch) := relativeCharacterDecay (𝟙 T) α.val a.val
    have hε (a : Ch) : 0 ≤ ε a := (relativeCharacterDecay_pos (𝟙 T) α.val a.val).le
    have hεB (a : Ch) : ε a ≤ Real.exp (B / Df) := by
      have ha := a.prop α.val (Finset.mem_sdiff.mp α.2).1
      rw [Category.id_comp] at ha
      have hbpos : 0 < ((b : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr hb₀
      have hlo := Real.log_le_log hbpos (by exact_mod_cast Units.val_le_val.mpr ha)
      rw [hbLog] at hlo
      have hEq := relativeCharacterDecay_pow_log α.val a.val 1
      simp only [pow_one, Nat.cast_one] at hEq
      rw [show ε a = relativeCharacterDecay (𝟙 T) α.val a.val from rfl, hEq]
      apply Real.exp_le_exp.mpr
      change -B ≤ logNormHom F T a.val α.val at hlo
      rw [show -(1 : ℝ) / Df * logNormHom F T a.val α.val =
        (-logNormHom F T a.val α.val) / Df by ring]
      exact div_le_div_of_nonneg_right (by linarith) hDf.le
    obtain ⟨s, Ψ, hΨ₀, hΨ, hContraction⟩ := exists_standardLeviContractionModulo hG hi hν hSmooth
      (S : Set (characterLattice T)) hS₀ α.val (Finset.mem_sdiff.mp α.2).1 b Ω hΩ hΩP
    have hgeom := (Standard.parabolicStructure i ν hG hi hν M (sdiff_subset : M ⊆ A₀)).2.2.1
    obtain ⟨K₁, hK₁, hIncl, C₁, hC₁, hIter⟩ := adelicUnipotentDecayModulo j hSmooth Ω
      (fun a : Ch => aG a.val) R₀ Ψ ε inferInstance hgeom.1.smooth hgeom.1.connectedSpace
      hgeom.1.isUnipotent hε ⟨_, (Real.exp_pos _).le, hεB⟩ hContraction hΨ₀ hΨ Yf hYf L hL n K' hK'
    have hCT : subgroupConstantTerm F j g = 0 :=
      constantTerm_alternatingConstantTerm_eq_zero hG hi hν hRS hS α.2 f.val
    have hRat (q : RationalGroupPoints F U) (y : A) : g (map F U G j (rational F U q) * y) = g y := by
      let U₀ := SubgroupFunctor.range j
      let z : AdelicSubgroupPoints.adelicPoints F G U₀ := ⟨_, ⟨rational F U q, rfl⟩⟩
      have hz : z ∈ AdelicSubgroupPoints.rationalSubgroup F G U₀ :=
        (mem_rationalSubgroup_range_iff j z).mpr ((mem_rationalImage_iff j _).mpr ⟨q, rfl⟩)
      exact alternatingConstantTerm_isRationalInvariant hG hi hν hS ⟨M, sdiff_subset⟩ f.val z hz y
    refine ⟨K₁, hK₁, hIncl, C₁, hC₁, fun p hp a k hk M hM hDer => ?_⟩
    exact hIter p hp a k hk (hxfin p hp a.val k hk) g hg hgSmooth hRat hgL hRad hCT M hM hDer
  choose Kα hKα hKin Cα hCα hiter using hdecay
  have hcompact (α : (S \ R : Finset (characterLattice T))) :=
    exists_compact_factors_height_bound ρ hN Ω (Kα α) hΩ (hKα α)
  choose Eα hEα hE using hcompact
  let Dα (α : (S \ R : Finset (characterLattice T))) := Eα α * C₀
  have hDα (α : (S \ R : Finset (characterLattice T))) : 0 < Dα α :=
    mul_pos (zero_lt_one.trans_le (hEα α)) (zero_lt_one.trans_le hC₀)
  obtain ⟨E₀, hE₀, hEbase⟩ := exists_compact_factors_height_bound ρ hN Ω K' hΩ hK'
  let Cbase := E₀ * C₀
  have hCbase : 0 < Cbase := mul_pos (zero_lt_one.trans_le hE₀) (zero_lt_one.trans_le hC₀)
  obtain ⟨Cnil, hCnil, hnil⟩ := hGrowth []
  let Base := Cnil * Cbase ^ e
  let Tail (α : (S \ R : Finset (characterLattice T))) := Cα α * Cword * Dα α ^ e
  have hBase : 0 ≤ Base := mul_nonneg hCnil (Real.rpow_nonneg hCbase.le _)
  have hTail (α : (S \ R : Finset (characterLattice T))) : 0 ≤ Tail α :=
    mul_nonneg (mul_nonneg (hCα α) hCword) (Real.rpow_nonneg (hDα α).le _)
  refine ⟨Base + ∑ α, Tail α, add_nonneg hBase (Finset.sum_nonneg fun α _ => hTail α), ?_⟩
  intro p hp a ha k hk
  let logRoot (α : characterLattice T) := logNormHom F T a.val α
  let Lmax : Option (S \ R : Finset (characterLattice T)) → ℝ := fun α => α.elim 0 (fun x => logRoot x.val)
  obtain ⟨s, _, hs⟩ := Finset.exists_max_image Finset.univ Lmax ⟨none, Finset.mem_univ _⟩
  have hmax₀ : 0 ≤ Lmax s := hs none (Finset.mem_univ _)
  have hmax : ∀ α ∈ S \ R, logRoot α ≤ Lmax s := fun α hα => hs (some ⟨α, hα⟩) (Finset.mem_univ _)
  have hha := (hTorus a ha).2 (Lmax s) hmax₀ hmax
  let x := p * aG a * k
  have hxH : 0 < H x := zero_lt_one.trans_le (one_le_adelicHeight F G ρ hN x)
  change ‖g x‖ * H x ^ m ≤ _
  cases s with
  | none =>
    have hha' : H (aG a) ≤ C₀ := by simpa only [Lmax, Option.elim_none, mul_zero, Real.exp_zero, mul_one] using hha
    have hdx : H x ≤ Cbase := (hEbase p hp _ k hk).trans
      (mul_le_mul_of_nonneg_left hha' (zero_le_one.trans hE₀))
    calc
      ‖g x‖ * H x ^ m ≤ Cnil * H x ^ r * H x ^ m :=
        mul_le_mul_of_nonneg_right (by simpa only [adelicIteratedDirectionalValue_nil] using hnil x) (pow_nonneg hxH.le _)
      _ = Cnil * H x ^ e := by rw [show e = r + (m : ℝ) by rfl, Real.rpow_add hxH, Real.rpow_natCast, mul_assoc]
      _ ≤ Base := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hxH.le hdx he) hCnil
      _ ≤ _ := le_add_of_nonneg_right (Finset.sum_nonneg fun α _ => hTail α)
  | some α =>
    let t := logRoot α.val
    have ht : 0 ≤ t := hmax₀
    let Hmax := Dα α * Real.exp (t₀ * t)
    have hHmax : 0 < Hmax := mul_pos (hDα α) (Real.exp_pos _)
    have hcap (k₁ : A) (hk₁ : k₁ ∈ Kα α) : H (p * aG a * k₁) ≤ Hmax := by
      exact ((hE α p hp _ k₁ hk₁).trans
        (mul_le_mul_of_nonneg_left hha (zero_le_one.trans (hEα α)))).trans_eq
          (mul_assoc (Eα α) C₀ (Real.exp (t₀ * t))).symm
    let M₀ := Cword * Hmax ^ r
    have hM₀ : 0 ≤ M₀ := mul_nonneg hCword (Real.rpow_nonneg hHmax.le _)
    have hfdec := hiter α p hp ⟨a, hch a ha⟩ k hk M₀ hM₀ (fun k₁ hk₁ _ s hs =>
        (hWord s hs _).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (zero_le_one.trans (one_le_adelicHeight F G ρ hN _)) (hcap k₁ hk₁) hr) hCword))
    let ε := relativeCharacterDecay (𝟙 T) α.val a
    have hε : 0 ≤ ε := (relativeCharacterDecay_pos (𝟙 T) α.val a).le
    have hExpo : ε ^ n * Hmax ^ e ≤ Dα α ^ e := by
      rw [show ε = relativeCharacterDecay (𝟙 T) α.val a from rfl, relativeCharacterDecay_pow_log,
        show Hmax = Dα α * Real.exp (t₀ * t) from rfl,
        Real.mul_rpow (hDα α).le (Real.exp_pos _).le, ← Real.exp_mul]
      change Real.exp (-(n : ℝ) / Df * t) * (Dα α ^ e * Real.exp (t₀ * t * e)) ≤ _
      rw [mul_left_comm, ← Real.exp_add]
      have h : -(n : ℝ) / Df * t + t₀ * t * e ≤ 0 := by
        calc
          _ = (t₀ * e - (n : ℝ) / Df) * t := by ring
          _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hn') ht
      exact (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr h)
        (Real.rpow_nonneg (hDα α).le _)).trans_eq (mul_one _)
    calc
      ‖g x‖ * H x ^ m ≤ (Cα α * ε ^ n * M₀) * Hmax ^ m := by
        exact mul_le_mul hfdec (pow_le_pow_left₀ hxH.le (hcap k (hKin α hk)) _) (pow_nonneg hxH.le _)
          (mul_nonneg (mul_nonneg (hCα α) (pow_nonneg hε _)) hM₀)
      _ = Cα α * Cword * (ε ^ n * Hmax ^ e) := by
        rw [show e = r + (m : ℝ) by rfl, Real.rpow_add hHmax, Real.rpow_natCast]
        dsimp only [M₀]
        ring
      _ ≤ Tail α := mul_le_mul_of_nonneg_left hExpo (mul_nonneg (hCα α) hCword)
      _ ≤ _ := (Finset.single_le_sum (f := Tail) (fun α _ => hTail α) (Finset.mem_univ α)).trans
        (le_add_of_nonneg_left hBase)

/-- The signed interval has arbitrary inverse powers of height on the
norm-one torus region selected by the two cutoffs. -/
def ArthurAlternatingConstantTermDecayStatement (R S : J) (T₁ Tp : V T) : Prop :=
  0 < N → R ⊆ S → S ⊆ Δ →
  ∀ Ω K' : Set A, IsCompact Ω → IsCompact K' → Ω ⊆ P₀ →
  ∀ f : FinitePlotSmoothRationalFunctions F G,
    HasAdelicUniformModerateGrowth F G ρ hSmooth
      (adelicDifferentialCommutator_of_smooth F G hSmooth) f →
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Ω,
    ∀ a ∈ sigmaTorusRegion hG hi D hK hρ R S T₁ Tp, ∀ k ∈ K',
      ‖alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f.val) (p * aG a * k)‖ *
        H (p * aG a * k) ^ m ≤ C

include hν in
theorem arthurAlternatingConstantTermDecay (R S : J) (T₁ Tp : V T) :
    ArthurAlternatingConstantTermDecayStatement hG hi D hK hρ hSmooth ρ R S T₁ Tp := by
  intro hN hRS hS Ω K' hΩ hK' hΩP f hf m
  exact alternatingConstantTerm_rapidDecay hG hi hν D hK hρ hSmooth ρ hN
    R S hRS hS T₁ Tp Ω K' hΩ hK' hΩP f hf m

end Langlands.Global.ArthurTruncation

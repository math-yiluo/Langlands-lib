import Langlands.Global.AdelicRelativeCuspidalConstantTerm
import Langlands.Global.AdelicMaximalUnipotentDecay
import Langlands.Global.AdelicPositiveTorusLogHeightBound
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof
import Mathlib.Data.List.OfFn

/-! # Relative cuspidal rapid decay with bounded complementary coordinates -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open AlgebraicGeometry CategoryTheory NumberField Set
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.LinearAlgebra.RationalSpan
  AdelicGroupPoints InfiniteAdelicGroupPoints PositiveRealTorus AdelicSiegelFactors
  RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (rT : T₀ ⟶ 𝓕.T)
  {d N : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom) (rho : MatrixRepresentation G (Fin N))

local notation "A" => AdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "J" => Fin (Module.finrank ℝ W)
local notation "basisG" => Module.finBasis ℝ W
local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "Δ" => simpleRelativeRoots 𝓕.i 𝓕.ν
local notation "B₀" => (Subtype.mk ∅ (empty_subset Δ) : Idx)
local notation "aG" => positiveMap F G 𝓕.T 𝓕.i T₀ rT
local notation "height" => adelicHeight F G rho

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem exists_compact_factors_height_bound (hN : 0 < N)
    (Ω K : Set A) (hΩ : IsCompact Ω) (hK : IsCompact K) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ p ∈ Ω, ∀ a : A, ∀ k ∈ K, height (p * a * k) ≤ C * height a := by
  have hc := continuous_adelicHeight F G rho hN
  obtain ⟨C₁, hC₁⟩ := (hΩ.image hc).bddAbove
  obtain ⟨C₂, hC₂⟩ := (hK.image hc).bddAbove
  let c₁ := max 1 C₁
  let c₂ := max 1 C₂
  have h₁ : 1 ≤ c₁ := le_max_left _ _
  have h₂ : 1 ≤ c₂ := le_max_left _ _
  have hpos (x : A) : 0 ≤ height x :=
    zero_le_one.trans (one_le_adelicHeight F G rho hN x)
  refine ⟨c₁ * c₂, one_le_mul_of_one_le_of_one_le h₁ h₂, fun p hp a k hk => ?_⟩
  calc
    height (p * a * k) ≤ height (p * a) * height k := adelicHeight_mul_le F G rho hN _ _
    _ ≤ (height p * height a) * height k :=
      mul_le_mul_of_nonneg_right (adelicHeight_mul_le F G rho hN _ _) (hpos _)
    _ ≤ (c₁ * height a) * c₂ :=
      mul_le_mul (mul_le_mul_of_nonneg_right ((hC₁ ⟨p, hp, rfl⟩).trans (le_max_right _ _)) (hpos _))
        ((hC₂ ⟨k, hk, rfl⟩).trans (le_max_right _ _)) (hpos _) (mul_nonneg (zero_le_one.trans h₁) (hpos _))
    _ = (c₁ * c₂) * height a := by ring

private theorem relativeCharacterDecay_pow (α : characterLattice 𝓕.T)
    (a : intrinsicSubgroup F T₀) (n : ℕ) :
    relativeCharacterDecay rT α a ^ n =
      Real.exp (-(n : ℝ) / (Module.finrank ℚ F : ℝ) * logNormHom F T₀ a.val (rT ≫ α)) := by
  have hpos : 0 < ((normCharacter F T₀ (rT ≫ α) a : ℝ≥0) : ℝ) := by
    exact_mod_cast (normCharacter F T₀ (rT ≫ α) a).ne_zero.bot_lt
  rw [relativeCharacterDecay, Real.rpow_def_of_pos hpos, ← Real.exp_nat_mul]
  change Real.exp (_ * (Real.log _ * _)) = Real.exp (_ * Real.log _)
  congr 1
  ring

/-- A common polynomial growth bound for each derivative word gives rapid decay,
uniformly in the family's size parameter, on a simple-root chamber whose other
spanning log character coordinates are bounded. -/
def AdelicRelativeCuspidalRapidDecayStatement : Prop :=
  IsSplitTorus T₀.toGrp → 0 < N →
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hG
  ∀ (P : Idx) (Zχ : Set (characterLattice T₀)),
    ratSpan (((fun α : characterLattice 𝓕.T => rT ≫ α) '' Δ) ∪ Zχ) = ⊤ →
  ∀ (b : ℝ≥0ˣ) (B : ℝ), 0 ≤ B →
  ∀ (Ω K : Set A), IsCompact Ω → IsCompact K →
    Ω ⊆ ((map F (𝓕.P B₀) G (𝓕.p B₀)).toMonoidHom.range : Set A) →
  ∀ (Yf : Set Gf), IsCompact Yf → ∀ (L : Subgroup Gf), IsOpen (L : Set Gf) →
  ∀ (I : Type v) (f : I → A → ℂ) (size : I → ℝ), (∀ q, 0 ≤ size q) →
  (∀ q, Continuous (f q)) →
  (∀ q (c : Gf), ContMDiff IG IC ∞ (fun y : G∞ => f q (pair F G y c))) →
  (∀ q, ∀ r ∈ rationalImage F (𝓕.p B₀), ∀ x, f q (r * x) = f q x) →
  (∀ q (u : AdelicGroupPoints F (𝓕.U P)), ∀ x,
    f q (map F (𝓕.U P) G (𝓕.iU P ≫ 𝓕.p P) u * x) = f q x) →
  (∀ q, ∀ l ∈ L, ∀ x, f q (x * ofFinite F G l) = f q x) →
  (∀ q, 𝓕.IsCuspidalAlong P (f q)) →
  ∀ R : ℝ, 0 ≤ R →
  (∀ s : List W, ∃ C : ℝ, 0 ≤ C ∧
    ∀ q x, ‖adelicIteratedDirectionalValue hG s (f q) x‖ ≤ C * height x ^ R * size q) →
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q, ∀ p ∈ Ω,
    ∀ a ∈ weakSimpleRootChamber F T₀ 𝓕.T rT G 𝓕.i 𝓕.ν b,
    (∀ χ ∈ Zχ, |logNormHom F T₀ a.val χ| ≤ B) →
    (∀ α ∈ Δ \ P.val, |logNormHom F T₀ a.val (rT ≫ α)| ≤ B) →
    ∀ k ∈ K, finite F G (p * aG a * k) ∈ Yf →
    ‖f q (p * aG a * k)‖ * height (p * aG a * k) ^ m ≤ C * size q

theorem adelicRelativeCuspidalRapidDecay :
    AdelicRelativeCuspidalRapidDecayStatement.{u, v} 𝓕 rT hG rho := by
  intro hT₀ hN
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let (v : InfinitePlace F) : FiniteDimensional ℝ v.Completion := inferInstance
  intro P Zχ hspan b B hB Ω K hΩ hK hΩB Yf hYf L hL I f size hsize hf hfS hfR hfU hfL hCusp R hR hGrowth m
  let logRoot (a : intrinsicSubgroup F T₀) (α : characterLattice 𝓕.T) :=
    logNormHom F T₀ a.val (rT ≫ α)
  have hPf : P.val.Finite := (𝓕.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots 𝓕.i 𝓕.ν).subset P.2
  let : Fintype P.val := hPf.fintype
  let B₁ := max B (-Real.log ((b : ℝ≥0) : ℝ))
  have hB₁ : 0 ≤ B₁ := hB.trans (le_max_left _ _)
  obtain ⟨C₀, r, hC₀, hr, htorus⟩ := adelicPositiveTorusLogHeightBound
    (CommGroupScheme.groupHom rT ≫ 𝓕.i) rho _ hT₀ hspan hN
  have hAheight (a : intrinsicSubgroup F T₀)
      (ha : a ∈ weakSimpleRootChamber F T₀ 𝓕.T rT G 𝓕.i 𝓕.ν b)
      (hz : ∀ χ ∈ Zχ, |logNormHom F T₀ a.val χ| ≤ B)
      (hOutside : ∀ α ∈ Δ \ P.val, |logRoot a α| ≤ B)
      (t : ℝ) (ht : 0 ≤ t) (hP : ∀ α ∈ P.val, logRoot a α ≤ t) :
      height (aG a) ≤ (C₀ * Real.exp (r * B₁)) * Real.exp (r * t) := by
    rw [mul_assoc, ← Real.exp_add, ← mul_add]
    refine htorus a (B₁ + t) (add_nonneg hB₁ ht) ?_
    rintro χ (⟨α, hα, rfl⟩ | hχ)
    · by_cases hαP : α ∈ P.val
      · have hb0 : 0 < ((b : ℝ≥0) : ℝ) := by exact_mod_cast b.ne_zero.bot_lt
        have hlower : Real.log ((b : ℝ≥0) : ℝ) ≤ logRoot a α :=
          Real.log_le_log hb0 (by exact_mod_cast Units.val_le_val.mpr (ha α hα))
        apply abs_le.mpr
        refine ⟨?_, (hP α hαP).trans (le_add_of_nonneg_left hB₁)⟩
        have hbB : -Real.log ((b : ℝ≥0) : ℝ) ≤ B₁ := le_max_right _ _
        linarith
      · exact (hOutside α ⟨hα, hαP⟩).trans ((le_max_left _ _).trans (le_add_of_nonneg_right ht))
    · exact (hz χ hχ).trans ((le_max_left _ _).trans (le_add_of_nonneg_right ht))
  let D := (Module.finrank ℚ F : ℝ)
  have hD : 0 < D := Nat.cast_pos.mpr Module.finrank_pos
  let e := R + (m : ℝ)
  have he : 0 ≤ e := add_nonneg hR (Nat.cast_nonneg _)
  obtain ⟨n, hn⟩ := exists_nat_gt (D * (r * e))
  have hn' : r * e ≤ (n : ℝ) / D :=
    (le_div_iff₀ hD).mpr (by simpa only [mul_comm] using hn.le)
  have hFiniteWords := fun w : Fin n → J => hGrowth ((List.ofFn w).map basisG)
  choose Cw hCw hw using hFiniteWords
  let Wn := ∑ w, Cw w
  have hWn : 0 ≤ Wn := Finset.sum_nonneg fun w _ => hCw w
  have hWord (s : List J) (hs : s.length = n) (q : I) (x : A) :
      ‖adelicIteratedDirectionalValue hG (s.map basisG) (f q) x‖ ≤ Wn * height x ^ R * size q := by
    let w : Fin n → J := fun j => s.get (Fin.cast hs.symm j)
    have hws : List.ofFn w = s := by
      subst n
      exact List.ofFn_get s
    rw [← hws]
    exact (hw w q x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := Cw) (fun w _ => hCw w) (Finset.mem_univ _))
        (Real.rpow_nonneg (zero_le_one.trans (one_le_adelicHeight F G rho hN x)) _)) (hsize q))
  have hdecay (α : P.val) :=
    let M := 𝓕.omitSimpleRoot α.val
    let j := 𝓕.iU M ≫ 𝓕.p M
    let hgeom := (𝓕.isUnipotentRadical M).isGeometricUnipotentRadical
    let ⟨dU, hU⟩ := Classical.indefiniteDescription _
      (Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension (𝓕.U M).X.left _
        (𝓕.U M).X.hom hgeom.2.1 hgeom.2.2.1)
    adelicMaximalUnipotentDecay hG (dU := dU) 𝓕.i 𝓕.ν rT j
      𝓕.connectedReductive 𝓕.maximalSplit 𝓕.generic hU hgeom.2.2.1 hgeom.2.2.2.1
      α.val (P.2 α.2) (𝓕.range_radical_eq_standardUnipotent M) Ω hΩ
      (fun _ hp => 𝓕.minimalParabolic_adelicImage_le_normalizer_radical M (hΩB hp))
      Yf hYf L hL b n K hK
  choose K' hK' hKin Cα hCα hiter using hdecay
  have hcompact : ∀ α : P.val, ∃ Eα : ℝ, 1 ≤ Eα ∧ ∀ p ∈ Ω, ∀ a : A, ∀ k ∈ K' α,
      height (p * a * k) ≤ Eα * height a :=
    fun α => exists_compact_factors_height_bound rho hN Ω (K' α) hΩ (hK' α)
  choose Eα hEα hE using hcompact
  let Dα (α : P.val) := Eα α * (C₀ * Real.exp (r * B₁))
  have hDα (α : P.val) : 0 < Dα α :=
    mul_pos (zero_lt_one.trans_le (hEα α)) (mul_pos (zero_lt_one.trans_le hC₀) (Real.exp_pos _))
  obtain ⟨E₀, hE₀, hEbase⟩ := exists_compact_factors_height_bound rho hN Ω K hΩ hK
  let D₀ := E₀ * (C₀ * Real.exp (r * B₁))
  have hD₀ : 0 < D₀ :=
    mul_pos (zero_lt_one.trans_le hE₀) (mul_pos (zero_lt_one.trans_le hC₀) (Real.exp_pos _))
  obtain ⟨Cbase, hCbase, hbase⟩ := hGrowth []
  let Base := Cbase * D₀ ^ e
  let Tail (α : P.val) := Cα α * Wn * Dα α ^ e
  have hBase : 0 ≤ Base := mul_nonneg hCbase (Real.rpow_nonneg hD₀.le _)
  have hTail (α : P.val) : 0 ≤ Tail α :=
    mul_nonneg (mul_nonneg (hCα α) hWn) (Real.rpow_nonneg (hDα α).le _)
  refine ⟨Base + ∑ α, Tail α, add_nonneg hBase (Finset.sum_nonneg fun α _ => hTail α), ?_⟩
  intro q p hp a ha hza hOutside k hk hx
  let lb : Option P.val → ℝ := fun α => α.elim 0 (fun x => logRoot a x.val)
  obtain ⟨s, _, hs⟩ := Finset.exists_max_image Finset.univ lb ⟨none, Finset.mem_univ _⟩
  have hmax₀ : 0 ≤ lb s := hs none (Finset.mem_univ _)
  have hmaxP : ∀ α ∈ P.val, logRoot a α ≤ lb s := fun α hα =>
    hs (some ⟨α, hα⟩) (Finset.mem_univ _)
  have hha := hAheight a ha hza hOutside (lb s) hmax₀ hmaxP
  let x := p * aG a * k
  have hxH : 0 < height x := zero_lt_one.trans_le (one_le_adelicHeight F G rho hN x)
  cases s with
  | none =>
    have hha' : height (aG a) ≤ C₀ * Real.exp (r * B₁) := by simpa only [lb, Option.elim_none,
      mul_zero, Real.exp_zero, mul_one] using hha
    have hdx : height x ≤ D₀ := (hEbase p hp _ k hk).trans
      (mul_le_mul_of_nonneg_left hha' (zero_le_one.trans hE₀))
    calc
      ‖f q x‖ * height x ^ m ≤ Cbase * height x ^ R * size q * height x ^ m :=
        mul_le_mul_of_nonneg_right (hbase q x) (pow_nonneg hxH.le _)
      _ = Cbase * height x ^ e * size q := by rw [show e = R + (m : ℝ) by rfl,
        Real.rpow_add hxH, Real.rpow_natCast]; ring
      _ ≤ Base * size q := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hxH.le hdx he) hCbase) (hsize q)
      _ ≤ (Base + ∑ α, Tail α) * size q :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Finset.sum_nonneg fun α _ => hTail α)) (hsize q)
  | some α =>
    let t := logRoot a α.val
    have ht : 0 ≤ t := hmax₀
    let H := Dα α * Real.exp (r * t)
    have hH : 0 < H := mul_pos (hDα α) (Real.exp_pos _)
    have hHcap (k' : A) (hk' : k' ∈ K' α) : height (p * aG a * k') ≤ H := by
      exact ((hE α p hp _ k' hk').trans
        (mul_le_mul_of_nonneg_left hha (zero_le_one.trans (hEα α)))).trans_eq
          (mul_assoc (Eα α) (C₀ * Real.exp (r * B₁)) (Real.exp (r * t))).symm
    let M := 𝓕.omitSimpleRoot α.val
    let j := 𝓕.iU M ≫ 𝓕.p M
    have hRf (z : RationalGroupPoints F (𝓕.U M)) (y : A) :
        f q (map F (𝓕.U M) G j (rational F (𝓕.U M) z) * y) = f q y :=
      hfR q _ (𝓕.radical_rationalImage_le_minimalParabolic M ((mem_rationalImage_iff j _).mpr ⟨z, rfl⟩)) y
    have hCT : subgroupConstantTerm F j (f q) = 0 :=
      𝓕.maximal_constantTerm_eq_zero_of_isCuspidalAlong P α.2 (hf q) (hfR q) (hfU q) (hCusp q)
    let M₀ := Wn * H ^ R * size q
    have hM₀ : 0 ≤ M₀ := mul_nonneg (mul_nonneg hWn (Real.rpow_nonneg hH.le _)) (hsize q)
    have hfdec := hiter α p hp a ha k hk hx (f q) (hf q) (hfS q) hRf (hfL q) hCT M₀ hM₀
      (fun k' hk' _ s hs => (hWord s hs q _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
          (zero_le_one.trans (one_le_adelicHeight F G rho hN _)) (hHcap k' hk') hR) hWn) (hsize q)))
    have hExpo : relativeCharacterDecay rT α.val a ^ n * H ^ e ≤ Dα α ^ e := by
      rw [relativeCharacterDecay_pow 𝓕 rT, show H = Dα α * Real.exp (r * t) by rfl,
        Real.mul_rpow (hDα α).le (Real.exp_pos _).le, ← Real.exp_mul]
      change Real.exp (-(n : ℝ) / D * t) * (Dα α ^ e * Real.exp (r * t * e)) ≤ _
      rw [mul_left_comm, ← Real.exp_add]
      have h : -(n : ℝ) / D * t + r * t * e ≤ 0 := by
        calc
          _ = (r * e - (n : ℝ) / D) * t := by ring
          _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hn') ht
      exact (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr h)
        (Real.rpow_nonneg (hDα α).le _)).trans_eq (mul_one _)
    have hcoef : Tail α ≤ Base + ∑ β, Tail β :=
      (Finset.single_le_sum (f := Tail) (fun β _ => hTail β) (Finset.mem_univ α)).trans
        (le_add_of_nonneg_left hBase)
    calc
      ‖f q x‖ * height x ^ m ≤ (Cα α * relativeCharacterDecay rT α.val a ^ n * M₀) * H ^ m :=
        mul_le_mul hfdec (pow_le_pow_left₀ hxH.le (hHcap k (hKin α hk)) _) (pow_nonneg hxH.le _)
          (mul_nonneg (mul_nonneg (hCα α) (pow_nonneg (relativeCharacterDecay_pos rT α.val a).le _)) hM₀)
      _ = Cα α * Wn * size q * (relativeCharacterDecay rT α.val a ^ n * H ^ e) := by
        rw [show e = R + (m : ℝ) by rfl, Real.rpow_add hH, Real.rpow_natCast]
        dsimp only [M₀]
        ring
      _ ≤ Cα α * Wn * size q * Dα α ^ e :=
        mul_le_mul_of_nonneg_left hExpo (mul_nonneg (mul_nonneg (hCα α) hWn) (hsize q))
      _ = Tail α * size q := by dsimp only [Tail]; ring
      _ ≤ (Base + ∑ β, Tail β) * size q := mul_le_mul_of_nonneg_right hcoef (hsize q)

end Langlands.Global.StandardParabolicFamily

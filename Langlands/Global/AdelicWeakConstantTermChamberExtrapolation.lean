import Langlands.Global.AdelicWeakConstantTermComponentExtraction
import Langlands.Global.AdelicSiegelExponentSubunitarity
import Langlands.Global.AdelicExponentPolynomials
import Langlands.Analysis.ShiftRecurrenceBound
import Langlands.Global.AdelicCentralPositiveHeightProof
import Langlands.Global.AdelicLeviCuspFormMajorantProof
import Langlands.Global.AdelicUniformTemperednessTorusFrame
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Siegel bounds for unitary exponent sums on Levi chambers

A sum `ψ` of functions with unitary normalized exponents along a standard parabolic `P = P_J`
that satisfies the logarithmic Siegel chamber bound of `G` satisfies the same bound at the
Siegel torus points that lie only in the chamber of the simple roots of `J`
(`StandardParabolicFamily.exists_leviChamber_bound_of_unitaryExponents`). The proof shifts the
point along a split ray of `P` into the chamber of `G` and comes back with the growth estimate
for translation equations with roots of norm `δ(r)^{-1/2}`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Analysis

/-- **Polynomial growth along a monic translation equation.** Let `a` be an element of a monoid
and `φ` a complex function with `∑_k c_k φ(a^k g) = 0` for every `g`, where `D = ∑_k c_k X^k` is
monic and every complex root of `D` has norm at most `κ > 0`. If `M ≥ 0` and
`‖φ(a^j g)‖ ≤ κ^j M` for `j < deg D`, then `‖φ(a^q g)‖ ≤ 3^{deg D} (q + 1)^{deg D} κ^q M`. -/
theorem norm_le_of_monic_translationSolution {A : Type*} [Monoid A] (a : A) (D : ℂ[X])
    (hD : D.Monic) {κ : ℝ} (hκ : 0 < κ) (hroots : ∀ z ∈ D.roots, ‖z‖ ≤ κ) (φ : A → ℂ)
    (hφ : ∀ g, ∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k * φ (a ^ k * g) = 0)
    (g : A) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j < D.natDegree, ‖φ (a ^ j * g)‖ ≤ κ ^ j * M)
    (q : ℕ) :
    ‖φ (a ^ q * g)‖ ≤ 3 ^ D.natDegree * ((q : ℝ) + 1) ^ D.natDegree * κ ^ q * M := by
  set L := D.roots.toList with hL
  have hlen : L.length = D.natDegree := by
    rw [hL, Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree]
  have hprod : (∏ k : Fin L.length, (X - C L[k.1]) : ℂ[X]) = D := by
    rw [Fin.prod_univ_fun_getElem L (fun z => (X - C z : ℂ[X])), hL, Multiset.prod_map_toList]
    exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq hD
      IsAlgClosed.card_roots_eq_natDegree
  have hw : ∀ k : Fin L.length, ‖L[k.1]‖ ≤ κ := fun k =>
    hroots _ (Multiset.mem_toList.mp (List.getElem_mem _))
  have h := norm_le_of_translationSolution a (fun k : Fin L.length => L[k.1]) hκ hw φ
    (fun g => by rw [hprod]; exact hφ g) g hM0 (fun j hj => hM j (hlen ▸ hj)) q
  rwa [hlen] at h

end Langlands.Analysis

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors RepresentationGrowth

section Modulus

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ T)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The Siegel modulus is positive. -/
theorem siegelModulus_pos (a : PositiveRealTorus.intrinsicSubgroup F T₀) :
    0 < siegelModulus F G T i ν T₀ j a := by
  unfold siegelModulus
  refine finprod_mem_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos)
    fun β _ => pow_pos ?_ _
  exact_mod_cast pos_iff_ne_zero.mpr (PositiveRealTorus.normCharacter F T₀ (j ≫ β) a).ne_zero

omit [IsAffine G.X.left] in
/-- The Siegel modulus is multiplicative on the positive torus. -/
theorem siegelModulus_mul (hT : IsSplitTorus T.toGrp)
    (a b : PositiveRealTorus.intrinsicSubgroup F T₀) :
    siegelModulus F G T i ν T₀ j (a * b) =
      siegelModulus F G T i ν T₀ j a * siegelModulus F G T i ν T₀ j b := by
  unfold siegelModulus
  rw [← finprod_mem_mul_distrib (hT.finite_positiveRelativeRoots i ν)]
  refine finprod_mem_congr rfl fun β _ => ?_
  rw [Subgroup.coe_mul, map_mul, Units.val_mul, NNReal.coe_mul, mul_pow]

omit [IsAffine G.X.left] in
/-- `δ(r^n b)^{1/2} = δ(r)^{n/2} δ(b)^{1/2}`. -/
theorem sqrt_siegelModulus_pow_mul (hT : IsSplitTorus T.toGrp)
    (r b : PositiveRealTorus.intrinsicSubgroup F T₀) (n : ℕ) :
    Real.sqrt (siegelModulus F G T i ν T₀ j (r ^ n * b)) =
      Real.sqrt (siegelModulus F G T i ν T₀ j r) ^ n *
        Real.sqrt (siegelModulus F G T i ν T₀ j b) := by
  induction n with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ n ih =>
    rw [pow_succ', mul_assoc, siegelModulus_mul i ν j hT,
      Real.sqrt_mul (siegelModulus_pos i ν j r).le, ih, pow_succ']
    ring

end Modulus

section CharacterLog

variable {F : Type} [Field F] [NumberField F]

/-- A closed matrix embedding bounds the absolute logarithm of each character by an affine
function of the logarithmic height. -/
theorem exists_abs_characterLog_le {G : GroupScheme (Spec (CommRingCat.of F))} {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (χ : rationalCharacters G) :
    ∃ c₀ c₁ : ℝ, 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ ∀ g : AdelicGroupPoints F G,
      |characterLog F G g χ| ≤ c₀ + c₁ * Real.log (adelicHeight F G rho g) := by
  obtain ⟨C, hC, e, he⟩ := exists_characterNorm_le F rho hN hrho χ
  refine ⟨Real.log C, e, Real.log_nonneg hC, Nat.cast_nonneg _, fun g => ?_⟩
  obtain ⟨h₁, h₂⟩ := he g
  set h := adelicHeight F G rho g with hh
  have h1 : 1 ≤ h := one_le_adelicHeight F G rho hN g
  have hpos : (0 : ℝ) < ((characterNorm F G χ.toMul g : ℝ≥0) : ℝ) := by
    exact_mod_cast pos_iff_ne_zero.mpr (characterNorm F G χ.toMul g).ne_zero
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC
  have hhpos : 0 < h := lt_of_lt_of_le one_pos h1
  have hlogR : Real.log (C * h ^ e) = Real.log C + e * Real.log h := by
    rw [Real.log_mul hCpos.ne' (pow_pos hhpos _).ne', Real.log_pow]
  rw [characterLog_apply, abs_le]
  constructor
  · have hinv' : ((((characterNorm F G χ.toMul g)⁻¹ : ℝ≥0ˣ) : ℝ≥0) : ℝ) =
        ((characterNorm F G χ.toMul g : ℝ≥0) : ℝ)⁻¹ := by
      simp
    have hinv : Real.log (((characterNorm F G χ.toMul g : ℝ≥0) : ℝ)⁻¹) ≤
        Real.log (C * h ^ e) := by
      refine Real.log_le_log (inv_pos.mpr hpos) ?_
      rw [← hinv']
      exact h₂
    rw [Real.log_inv, hlogR] at hinv
    linarith
  · have hle : Real.log ((characterNorm F G χ.toMul g : ℝ≥0) : ℝ) ≤ Real.log (C * h ^ e) :=
      Real.log_le_log hpos h₁
    rw [hlogR] at hle
    exact hle

/-- The logarithm of a pulled-back character is the logarithm of the character at the image. -/
theorem characterLog_comp {T₀ T : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ T)
    (χ : characterLattice T) (x : AdelicGroupPoints F T₀.toGrp) :
    characterLog F T₀.toGrp x (j ≫ χ) =
      characterLog F T.toGrp (map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) x) χ := by
  have he : Lie.characterValue (j ≫ χ) x =
      Lie.characterValue χ (map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) x) :=
    Lie.characterValue_comp j χ x
  change Real.log ((IdeleAbsoluteValue.full F (Lie.characterValue (j ≫ χ) x) : ℝ≥0) : ℝ) =
    Real.log ((IdeleAbsoluteValue.full F (Lie.characterValue χ
      (map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) x)) : ℝ≥0) : ℝ)
  rw [he]

end CharacterLog

namespace StandardParabolicFamily

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ fam.T)
  {N : ℕ} (rho : MatrixRepresentation G (Fin N))
  (J : StandardIndex F G fam.i fam.ν)

local notation "A" => AdelicGroupPoints F G
local notation "P" => fam.P J
local notation "Δ" => simpleRelativeRoots fam.i fam.ν
local notation "Torus" => PositiveRealTorus.intrinsicSubgroup F T₀
local notation "aG" => positiveMap F G fam.T fam.i T₀ j
local notation "pG" => map F P G (fam.p J)
local notation "δ" => siegelModulus F G fam.T fam.i fam.ν T₀ j
local notation "H" => adelicHeight F G rho

/-- **A split ray of `P_J` in the Siegel torus.** There is a positive torus point `r` with
`|β(r)| = 1` for the simple roots `β` in `J`, `|α(r)| > 1` for the other simple roots, whose image
in `G(𝔸)` lies in the positive split component `𝔄_P` of `P = P_J`. It is the product of the
fundamental rays of the simple roots outside `J`. -/
theorem exists_splitComponent_siegelRay
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j) :
    ∃ r : Torus, (∀ β ∈ J.val, characterLog F T₀.toGrp r.val (j ≫ β) = 0) ∧
      (∀ α ∈ Δ, α ∉ J.val → 0 < characterLog F T₀.toGrp r.val (j ≫ α)) ∧
      ∃ a : fam.positiveSplitComponent J, pG a.val = aG r := by
  classical
  obtain ⟨r, hOff, hPos, -, hSplit⟩ := fam.exists_siegelFundamentalRays j hsetup
  have hrr (g₀ α : Δ) : 0 ≤ characterLog F T₀.toGrp (r g₀).val (j ≫ α.val) := by
    by_cases h : α = g₀
    · rw [h]
      exact (hPos g₀).le
    · rw [hOff g₀ α h]
  have key : ∀ S : Finset Δ, (∀ α ∈ S, α.val ∉ J.val) → ∃ r' : Torus,
      (∀ β ∈ J.val, characterLog F T₀.toGrp r'.val (j ≫ β) = 0) ∧
      (∀ α ∈ S, 0 < characterLog F T₀.toGrp r'.val (j ≫ α.val)) ∧
      (∀ α : Δ, 0 ≤ characterLog F T₀.toGrp r'.val (j ≫ α.val)) ∧
      ∃ a : fam.positiveSplitComponent J, pG a.val = aG r' := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨1, fun β _ => ?_, fun α hα => absurd hα (Finset.notMem_empty α), fun α => ?_, 1, ?_⟩
      · rw [OneMemClass.coe_one, characterLog_one]
        rfl
      · rw [OneMemClass.coe_one, characterLog_one]
        exact le_rfl
      · rw [OneMemClass.coe_one, map_one, map_one]
    | insert g₀ S hg₀ ih =>
      intro hS
      obtain ⟨r', h0, hpos, hnn, a, ha⟩ := ih fun α hα => hS α (Finset.mem_insert_of_mem hα)
      have hg₀J : g₀.val ∉ J.val := hS g₀ (Finset.mem_insert_self g₀ S)
      obtain ⟨b, hb⟩ := hSplit J g₀ hg₀J
      refine ⟨r' * r g₀, fun β hβ => ?_, fun α hα => ?_, fun α => ?_, a * b, ?_⟩
      · have hne : (⟨β, J.property hβ⟩ : Δ) ≠ g₀ := fun he =>
          hg₀J (congrArg Subtype.val he ▸ hβ)
        have e1 := h0 β hβ
        have e2 := hOff g₀ ⟨β, J.property hβ⟩ hne
        rw [Subgroup.coe_mul, characterLog_mul]
        change characterLog F T₀.toGrp r'.val (j ≫ β) +
          characterLog F T₀.toGrp (r g₀).val (j ≫ β) = 0
        rw [e1, e2, add_zero]
      · rw [Subgroup.coe_mul, characterLog_mul]
        rcases Finset.mem_insert.mp hα with rfl | hα
        · exact add_pos_of_nonneg_of_pos (hnn α) (hPos α)
        · exact add_pos_of_pos_of_nonneg (hpos α hα) (hrr g₀ α)
      · rw [Subgroup.coe_mul, characterLog_mul]
        exact add_nonneg (hnn α) (hrr g₀ α)
      · rw [Subgroup.coe_mul, map_mul, ha, hb, map_mul]
  have : Fintype Δ := (fam.isSplitTorus_T.finite_simpleRelativeRoots fam.i fam.ν).fintype
  obtain ⟨r', h0, hpos, -, a, ha⟩ := key (Finset.univ.filter fun α : Δ => α.val ∉ J.val)
    fun α hα => (Finset.mem_filter.mp hα).2
  exact ⟨r', h0, fun α hα hαJ => hpos ⟨α, hα⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hαJ⟩),
    a, ha⟩

/-- The height of a torus point read through `fam.T`. -/
theorem adelicHeight_positiveMap (b : Torus) :
    adelicHeight F fam.T.toGrp (fam.i ≫ rho)
        (map F T₀.toGrp fam.T.toGrp (CommGroupScheme.groupHom j) b.val) = H (aG b) := by
  rw [adelicHeight_map_eq_adelicHeight_comp]
  change _ = adelicHeight F G rho (map F T₀.toGrp G (CommGroupScheme.groupHom j ≫ fam.i) b.val)
  rw [adelicHeight_map_eq_adelicHeight_comp, Category.assoc]

/-- **Shifting into the chamber along a split ray.** Let `r` be a split ray for `J` as in
`exists_splitComponent_siegelRay`. There are `X₀, X₁ ≥ 0` such that for every `b` in the
`J`-part `|β(b)| ≥ t` (`β ∈ J`) of the chamber there is `n₀ ≤ X₀ + X₁ log H(b)` with `r^n b` in
the full chamber of `G` for every `n ≥ n₀`. -/
theorem exists_ray_shift_mem_chamber (hN : 0 < N) (hrho : IsClosedSubgroup rho) (r : Torus)
    (hrJ : ∀ β ∈ J.val, characterLog F T₀.toGrp r.val (j ≫ β) = 0)
    (hrPos : ∀ α ∈ Δ, α ∉ J.val → 0 < characterLog F T₀.toGrp r.val (j ≫ α)) (t : ℝ≥0ˣ) :
    ∃ X₀ X₁ : ℝ, 0 ≤ X₀ ∧ 0 ≤ X₁ ∧ ∀ b : Torus,
      (∀ β ∈ J.val, Real.log ((t : ℝ≥0) : ℝ) ≤ characterLog F T₀.toGrp b.val (j ≫ β)) →
      ∃ n₀ : ℕ, (n₀ : ℝ) ≤ X₀ + X₁ * Real.log (H (aG b)) ∧
        ∀ n : ℕ, n₀ ≤ n →
          r ^ n * b ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ fam.T j G fam.i fam.ν t := by
  classical
  have : Fintype Δ := (fam.isSplitTorus_T.finite_simpleRelativeRoots fam.i fam.ν).fintype
  have hiC : IsClosedSubgroup fam.i := fam.maximalSplit.1.2
  have hc := fun α : Δ => exists_abs_characterLog_le (fam.i ≫ rho) hN (hiC.comp hrho) α.val
  choose c₀ c₁ hc₀ hc₁ hc using hc
  let u : Δ → ℝ := fun α =>
    if α.val ∈ J.val then 1 else characterLog F T₀.toGrp r.val (j ≫ α.val)
  have hu (α : Δ) : 0 < u α := by
    dsimp only [u]
    split_ifs with h
    · exact one_pos
    · exact hrPos α.val α.property h
  set lt := |Real.log ((t : ℝ≥0) : ℝ)| with hlt
  have hlt0 : 0 ≤ lt := abs_nonneg _
  refine ⟨∑ α : Δ, (lt + c₀ α) / u α + 1, ∑ α : Δ, c₁ α / u α,
    add_nonneg (Finset.sum_nonneg fun α _ => div_nonneg (add_nonneg hlt0 (hc₀ α)) (hu α).le)
      zero_le_one,
    Finset.sum_nonneg fun α _ => div_nonneg (hc₁ α) (hu α).le, fun b hb => ?_⟩
  have hlogb (α : Δ) : |characterLog F T₀.toGrp b.val (j ≫ α.val)| ≤
      c₀ α + c₁ α * Real.log (H (aG b)) := by
    rw [characterLog_comp, ← fam.adelicHeight_positiveMap j rho b]
    exact hc α _
  set X := ∑ α : Δ, (lt + |characterLog F T₀.toGrp b.val (j ≫ α.val)|) / u α with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun α _ =>
    div_nonneg (add_nonneg hlt0 (abs_nonneg _)) (hu α).le
  refine ⟨⌈X⌉₊, ?_, fun n hn => ?_⟩
  · have hXle : X ≤ ∑ α : Δ, (lt + c₀ α) / u α + (∑ α : Δ, c₁ α / u α) * Real.log (H (aG b)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun α _ => ?_
      rw [div_mul_eq_mul_div, ← add_div]
      exact div_le_div_of_nonneg_right (by linarith [hlogb α]) (hu α).le
    have := Nat.ceil_lt_add_one hX0
    linarith
  · refine (PositiveRealTorus.mem_weakSimpleRootChamber_iff_log F T₀ fam.T j G fam.i fam.ν t _).mpr fun χ hχ => ?_
    rw [Subgroup.coe_mul, SubmonoidClass.coe_pow, characterLog_mul, AdelicGroupPoints.characterLog_pow]
    change Real.log ((t : ℝ≥0) : ℝ) ≤ n • characterLog F T₀.toGrp r.val (j ≫ χ) +
      characterLog F T₀.toGrp b.val (j ≫ χ)
    rw [nsmul_eq_mul]
    by_cases hχJ : χ ∈ J.val
    · rw [hrJ χ hχJ, mul_zero, zero_add]
      exact hb χ hχJ
    · have hℓ := hrPos χ hχ hχJ
      have huχ : u ⟨χ, hχ⟩ = characterLog F T₀.toGrp r.val (j ≫ χ) := by simp [u, hχJ]
      have hXge : (lt + |characterLog F T₀.toGrp b.val (j ≫ χ)|) /
          characterLog F T₀.toGrp r.val (j ≫ χ) ≤ X := by
        have h := Finset.single_le_sum
          (f := fun α : Δ => (lt + |characterLog F T₀.toGrp b.val (j ≫ α.val)|) / u α)
          (fun α _ => div_nonneg (add_nonneg hlt0 (abs_nonneg _)) (hu α).le)
          (Finset.mem_univ ⟨χ, hχ⟩)
        rw [huχ] at h
        exact h
      have hnX : X ≤ n := (Nat.le_ceil X).trans (Nat.cast_le.mpr hn)
      have h1 : lt + |characterLog F T₀.toGrp b.val (j ≫ χ)| ≤
          n * characterLog F T₀.toGrp r.val (j ≫ χ) :=
        (div_le_iff₀ hℓ).mp (hXge.trans hnX)
      have h2 := le_abs_self (Real.log ((t : ℝ≥0) : ℝ))
      have h3 := neg_abs_le (characterLog F T₀.toGrp b.val (j ≫ χ))
      linarith

/-- Heights along a split ray grow at most linearly in logarithm. -/
theorem log_adelicHeight_ray_shift_le (hN : 0 < N) (r b : Torus) (n : ℕ) :
    Real.log (H (aG (r ^ n * b))) ≤
      Real.log (H 1) + n * Real.log (H (aG r)) + Real.log (H (aG b)) := by
  have hH (y : A) : 1 ≤ H y := one_le_adelicHeight F G rho hN y
  have hHp (y : A) : 0 < H y := zero_lt_one.trans_le (hH y)
  have hPow : H ((aG r) ^ n) ≤ H 1 * H (aG r) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ (aG r), pow_succ (H (aG r)), ← mul_assoc]
      exact (adelicHeight_mul_le F G rho hN _ _).trans
        (mul_le_mul_of_nonneg_right ih (hHp _).le)
  have hle : H (aG (r ^ n * b)) ≤ H 1 * H (aG r) ^ n * H (aG b) := by
    rw [map_mul, map_pow]
    exact (adelicHeight_mul_le F G rho hN _ _).trans
      (mul_le_mul_of_nonneg_right hPow (hHp _).le)
  calc Real.log (H (aG (r ^ n * b))) ≤ Real.log (H 1 * H (aG r) ^ n * H (aG b)) :=
        Real.log_le_log (hHp _) hle
    _ = _ := by
      rw [Real.log_mul (mul_pos (hHp _) (pow_pos (hHp _) _)).ne' (hHp _).ne',
        Real.log_mul (hHp _).ne' (pow_pos (hHp _) _).ne', Real.log_pow]

/-- **Siegel bound on Levi chambers for unitary exponent sums** (the estimate behind
Delorme 2023, Lemma 3.8 (ii), obtained here by extrapolation along a split ray).
Let `ψ = ∑_{λ ∈ s} c_λ` where each `c_λ` has the normalized exponent `λ` along `P = P_J` with
`Re λ = 0`, and suppose `ψ` satisfies the logarithmic Siegel chamber bound of `G`. Then for every
threshold `t` and compact `Ω` there are `e` and `B ≥ 0` with
`‖ψ(a_G(b) w)‖ ≤ B δ(b)^{1/2} (1 + log H(a_G(b)))^e` for every `w ∈ Ω` and every torus point `b`
with `|β(b)| ≥ t` only for the simple roots `β ∈ J`.

Proof: choose a split ray `r` of `P` (`exists_splitComponent_siegelRay`). Along `r⁻¹` the
function `ψ` satisfies a translation equation whose roots `(r⁻¹)^{λ + ρ_P}` all have norm
`δ(r)^{-1/2}`, since `Re λ = 0` and `|r^{ρ_P}| = δ(r)^{1/2}`. Shift `b` by `r^Q` into the
chamber of `G` (`exists_ray_shift_mem_chamber`), where the Siegel bound holds, and come back
along `r⁻¹` with `Langlands.Analysis.norm_le_of_monic_translationSolution`; the factor
`δ(r)^{Q/2}` cancels and `Q` is linear in `log H(a_G(b))`. -/
theorem exists_leviChamber_bound_of_unitaryExponents
    (hδ : StandardNestedHalfModulusCompatibilityStatement)
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j)
    (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (s : Finset (ComplexCharacterParameter F P)) (c : ComplexCharacterParameter F P → A → ℂ)
    (hexp : ∀ lam ∈ s, fam.HasExponent J lam (c lam))
    (hunit : ∀ lam ∈ s, parameterRealPart F P lam = 0)
    (hf : fam.HasSiegelChamberGrowth j rho (∑ lam ∈ s, c lam))
    (t : ℝ≥0ˣ) {Ω : Set A} (hΩ : IsCompact Ω) :
    ∃ (e : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ b : Torus,
      (∀ β ∈ J.val, Real.log ((t : ℝ≥0) : ℝ) ≤ characterLog F T₀.toGrp b.val (j ≫ β)) →
      ∀ w ∈ Ω, ‖(∑ lam ∈ s, c lam) (aG b * w)‖ ≤
        B * Real.sqrt (δ b) * (1 + Real.log (H (aG b))) ^ e := by
  classical
  set ψ := ∑ lam ∈ s, c lam with hψ
  obtain ⟨r, hrJ, hrPos, aD, haD⟩ := fam.exists_splitComponent_siegelRay j J hsetup
  obtain ⟨X₀, X₁, hX₀, hX₁, hX⟩ := fam.exists_ray_shift_mem_chamber j rho J hN hrho r hrJ hrPos t
  obtain ⟨e₀, C₀, hC₀, hB⟩ := hf t Ω hΩ
  -- translation equations along the inverse ray
  have hk : ∀ lam, ∃ k : ℕ, lam ∈ s → ∀ a : fam.positiveSplitComponent J,
      IsTranslationPolynomialSolution (pG a.val)
        ((X - C (parameterPower F P (lam + halfModulusParameter F P) a.val)) ^ (k + 1))
        (c lam) := by
    intro lam
    by_cases h : lam ∈ s
    · obtain ⟨k, hk⟩ := HasExponent.exists_isTranslationPolynomialSolution_pow fam J (hexp lam h)
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose k hk using hk
  let aI : fam.positiveSplitComponent J := aD⁻¹
  let root : ComplexCharacterParameter F P → ℂ := fun lam =>
    parameterPower F P (lam + halfModulusParameter F P) aI.val
  let D : ℂ[X] := ∏ lam ∈ s, (X - C (root lam)) ^ (k lam + 1)
  have hD : D.Monic := monic_prod_of_monic _ _ fun lam _ => (monic_X_sub_C _).pow _
  have hsol : IsTranslationPolynomialSolution (pG aI.val) D ψ :=
    isTranslationPolynomialSolution_sum_prod s _ _ _ fun lam hlam => hk lam hlam aI
  have hT := fam.isSplitTorus_T
  have hδr : 0 < δ r := siegelModulus_pos fam.i fam.ν j r
  have hsr : 0 < Real.sqrt (δ r) := Real.sqrt_pos.mpr hδr
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = (Real.sqrt (δ r))⁻¹ := ⟨_, rfl⟩
  have hκ : 0 < κ := hκdef ▸ inv_pos.mpr hsr
  have hhalf := fam.halfModulus_eq_siegelSqrt_of_positiveSplitComponent hδ hsetup J r aD haD
  have hroot : ∀ lam ∈ s, ‖root lam‖ = κ := by
    intro lam hlam
    have h1 : ‖parameterPower F P lam aI.val‖ = 1 := by
      rw [parameterPower, Complex.norm_exp, complexParameterPairing_re, hunit lam hlam, map_zero,
        LinearMap.zero_apply, Real.exp_zero]
    have h2 : parameterPower F P (halfModulusParameter F P) aI.val =
        (fam.halfModulus J aD.val)⁻¹ := by
      show parameterPower F P (halfModulusParameter F P) (aD⁻¹ : fam.positiveSplitComponent J).val =
        (parameterPower F P (halfModulusParameter F P) aD.val)⁻¹
      rw [InvMemClass.coe_inv, ← parameterCharacter_apply, map_inv, Units.val_inv_eq_inv_val,
        parameterCharacter_apply]
    show ‖parameterPower F P (lam + halfModulusParameter F P) aI.val‖ = κ
    rw [parameterPower_add, norm_mul, h1, one_mul, h2, hhalf, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), hκdef]
  have hroots : ∀ z ∈ D.roots, ‖z‖ ≤ κ := by
    intro z hz
    have h0 : D.IsRoot z := (mem_roots hD.ne_zero).mp hz
    rw [IsRoot, eval_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨lam, hlam, h⟩ := h0
    rw [eval_pow, eval_sub, eval_X, eval_C] at h
    rw [sub_eq_zero.mp ((pow_eq_zero_iff (Nat.succ_ne_zero _)).mp h), hroot lam hlam]
  -- constants
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = D.natDegree := ⟨_, rfl⟩
  have hH (y : A) : 1 ≤ H y := one_le_adelicHeight F G rho hN y
  have hlogH (y : A) : 0 ≤ Real.log (H y) := Real.log_nonneg (hH y)
  obtain ⟨c₃, hc₃def⟩ : ∃ c₃ : ℝ, c₃ = m + 1 + X₀ + X₁ := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂def⟩ : ∃ c₂ : ℝ, c₂ = Real.log (H 1) + c₃ * Real.log (H (aG r)) + 1 :=
    ⟨_, rfl⟩
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hc₃ : 0 ≤ c₃ := by rw [hc₃def]; linarith
  have hc₂ : 0 ≤ c₂ := by
    rw [hc₂def]
    exact add_nonneg (add_nonneg (hlogH 1) (mul_nonneg hc₃ (hlogH _))) zero_le_one
  refine ⟨m + e₀, 3 ^ m * (c₃ + 1) ^ m * C₀ * c₂ ^ e₀,
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith) _)) hC₀)
      (pow_nonneg hc₂ _), fun b hb w hw => ?_⟩
  obtain ⟨n₀, hn₀, hchamber⟩ := hX b hb
  obtain ⟨Lb, hLbdef⟩ : ∃ Lb : ℝ, Lb = 1 + Real.log (H (aG b)) := ⟨_, rfl⟩
  have hLb1 : 1 ≤ Lb := by rw [hLbdef]; linarith [hlogH (aG b)]
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, Q = m + n₀ := ⟨_, rfl⟩
  have hQ : (Q : ℝ) ≤ c₃ * Lb := by
    have hℓ := hlogH (aG b)
    have hexpand : c₃ * Lb = (m + X₀ + X₁ * Real.log (H (aG b))) +
        (1 + X₁ + (m + 1 + X₀) * Real.log (H (aG b))) := by
      rw [hc₃def, hLbdef]
      ring
    have h1 : 0 ≤ (m + 1 + X₀) * Real.log (H (aG b)) := mul_nonneg (by linarith) hℓ
    rw [hQdef, Nat.cast_add, hexpand]
    linarith
  have hshift : ∀ n ≤ Q, 1 + Real.log (H (aG (r ^ n * b))) ≤ c₂ * Lb := by
    intro n hn
    have h1 := fam.log_adelicHeight_ray_shift_le j rho hN r b n
    have hnQ : (n : ℝ) ≤ c₃ * Lb := (Nat.cast_le.mpr hn).trans hQ
    have h2 := mul_le_mul_of_nonneg_right hnQ (hlogH (aG r))
    have h3 := mul_le_mul_of_nonneg_left hLb1 (hlogH 1)
    have h4 : c₂ * Lb = Real.log (H 1) * Lb + c₃ * Lb * Real.log (H (aG r)) + Lb := by
      rw [hc₂def]
      ring
    rw [h4]
    linarith
  have hpt : ∀ n : ℕ, (pG aD.val) ^ n * (aG b * w) = aG (r ^ n * b) * w := by
    intro n
    rw [haD, map_mul, map_pow, mul_assoc]
  have hinvpow : ∀ i ≤ Q, (pG aI.val) ^ i * ((pG aD.val) ^ Q * (aG b * w)) =
      (pG aD.val) ^ (Q - i) * (aG b * w) := by
    intro i hi
    have hsplit : (pG aD.val) ^ Q = (pG aD.val) ^ i * (pG aD.val) ^ (Q - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hi]
    show (pG (aD⁻¹ : fam.positiveSplitComponent J).val) ^ i * ((pG aD.val) ^ Q * (aG b * w)) = _
    rw [hsplit, InvMemClass.coe_inv, map_inv, inv_pow, mul_assoc, inv_mul_cancel_left]
  have hbound : ∀ n, n₀ ≤ n → n ≤ Q → ‖ψ (aG (r ^ n * b) * w)‖ ≤
      C₀ * Real.sqrt (δ r) ^ n * Real.sqrt (δ b) * (c₂ * Lb) ^ e₀ := by
    intro n hn hnQ
    have hpos : 0 ≤ 1 + Real.log (H (aG (r ^ n * b))) := by linarith [hlogH (aG (r ^ n * b))]
    calc ‖ψ (aG (r ^ n * b) * w)‖
        ≤ C₀ * Real.sqrt (δ (r ^ n * b)) * (1 + Real.log (H (aG (r ^ n * b)))) ^ e₀ :=
          hB _ (hchamber n hn) w hw
      _ ≤ C₀ * Real.sqrt (δ (r ^ n * b)) * (c₂ * Lb) ^ e₀ :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos (hshift n hnQ) e₀)
            (mul_nonneg hC₀ (Real.sqrt_nonneg _))
      _ = _ := by
          rw [sqrt_siegelModulus_pow_mul fam.i fam.ν j hT]
          ring
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ,
      M = C₀ * Real.sqrt (δ r) ^ Q * Real.sqrt (δ b) * (c₂ * Lb) ^ e₀ := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC₀ (pow_nonneg (Real.sqrt_nonneg _) _))
      (Real.sqrt_nonneg _)) (pow_nonneg (mul_nonneg hc₂ (by linarith)) _)
  have hκs (i : ℕ) : κ ^ i * Real.sqrt (δ r) ^ i = 1 := by
    rw [← mul_pow, hκdef, inv_mul_cancel₀ hsr.ne', one_pow]
  have hM : ∀ i < D.natDegree, ‖ψ ((pG aI.val) ^ i * ((pG aD.val) ^ Q * (aG b * w)))‖ ≤
      κ ^ i * M := by
    intro i hi
    have hiQ : i ≤ Q := by omega
    rw [hinvpow i hiQ, hpt]
    refine (hbound (Q - i) (by omega) (Nat.sub_le _ _)).trans (le_of_eq ?_)
    have hsplit : Real.sqrt (δ r) ^ Q = Real.sqrt (δ r) ^ i * Real.sqrt (δ r) ^ (Q - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hiQ]
    rw [hMdef, hsplit]
    linear_combination (-(C₀ * Real.sqrt (δ r) ^ (Q - i) * Real.sqrt (δ b) * (c₂ * Lb) ^ e₀)) *
      hκs i
  have hfinal := Langlands.Analysis.norm_le_of_monic_translationSolution (pG aI.val) D hD hκ
    hroots ψ hsol ((pG aD.val) ^ Q * (aG b * w)) hM0 hM Q
  rw [hinvpow Q le_rfl, Nat.sub_self, pow_zero, one_mul, ← hm] at hfinal
  have hκQ : κ ^ Q * M = C₀ * Real.sqrt (δ b) * (c₂ * Lb) ^ e₀ := by
    rw [hMdef]
    linear_combination (C₀ * Real.sqrt (δ b) * (c₂ * Lb) ^ e₀) * hκs Q
  have hQ1 : (Q : ℝ) + 1 ≤ (c₃ + 1) * Lb := by nlinarith
  have hrest : 0 ≤ C₀ * Real.sqrt (δ b) * (c₂ * Lb) ^ e₀ :=
    mul_nonneg (mul_nonneg hC₀ (Real.sqrt_nonneg _)) (pow_nonneg (mul_nonneg hc₂ (by linarith)) _)
  calc ‖ψ (aG b * w)‖ ≤ 3 ^ m * ((Q : ℝ) + 1) ^ m * κ ^ Q * M := hfinal
    _ = 3 ^ m * ((Q : ℝ) + 1) ^ m * (C₀ * Real.sqrt (δ b) * (c₂ * Lb) ^ e₀) := by
        rw [mul_assoc _ (κ ^ Q), hκQ]
    _ ≤ 3 ^ m * ((c₃ + 1) * Lb) ^ m * (C₀ * Real.sqrt (δ b) * (c₂ * Lb) ^ e₀) := by
        refine mul_le_mul_of_nonneg_right ?_ hrest
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hQ1 m) (by positivity)
    _ = 3 ^ m * (c₃ + 1) ^ m * C₀ * c₂ ^ e₀ * Real.sqrt (δ b) *
        (1 + Real.log (H (aG b))) ^ (m + e₀) := by
        rw [← hLbdef, mul_pow (c₃ + 1) Lb m, mul_pow c₂ Lb e₀, pow_add]
        ring

end StandardParabolicFamily

end Langlands.Global

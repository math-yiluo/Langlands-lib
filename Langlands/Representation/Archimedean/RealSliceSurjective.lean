import Langlands.Representation.Archimedean.RealInductionStagesDerivative
import Langlands.Representation.Archimedean.RealBlockTestVector

/-!
# The slice at the identity is surjective

For lists `pre`, `core`, `post` of real blocks with `a = rank pre`, `r = rank core` and
`n = rank (pre ++ core ++ post)`, the slice at the identity,
`σ₁ F (g) = |det g|^(-c) F(diag(1_a, g, 1))`, maps the `O(n)`-finite functions of the standard
module of `pre ++ core ++ post` onto the `O(r)`-finite functions of the standard module of
`core` (`sliceK_one_surjective`).

Proof. Let `coreC = charList core` be `core` with every induction block replaced by the two
character blocks of its position characters; the standard module of `core` lies in that of
`coreC`. Averaging a linear left inverse of this inclusion over `O(r)` gives an exactly
`O(r)`-equivariant retraction `T`. For `ψ` in the standard module of `core`, an explicit
continuous `O(n)`-finite function on `O(n)` — a product of polynomial factors for the rows outside
the middle block times a sign-averaged polynomial extension of `ψ` in the entries of the middle
block — is the restriction of some `G'` in the standard module of `pre ++ coreC ++ post` with
`σ₁ G' = c ψ`, `c ≠ 0` (`sliceK_one_surjective_of_none`). The induced map `Ind T`
then gives `σ₁ (Ind T G') = T (σ₁ G') = c ψ`.
-/

noncomputable section

open scoped Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealSliceSurjective

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open InductionStages RealBlockRotation RealBlockFourierFinite RealBlockTestVector
open TranslateFinite GramFormula

/-! ## Expanding induction blocks into characters -/

section CharList

/-- Replace every induction block by the two character blocks carrying its position
characters `sgn^{|m|+1} |·|^{t+|m|/2}` and `|·|^{t-|m|/2}`. -/
def charList : List RealBlock → List RealBlock
  | [] => []
  | .character c :: ds => .character c :: charList ds
  | .induced d :: ds =>
      .character (RealJacquetFrobenius.charData
          ⟨(d.weight.natAbs + 1) % 2, Nat.mod_lt _ (by norm_num)⟩
          (d.exponent + (d.weight.natAbs : ℂ) / 2)) ::
        .character (RealJacquetFrobenius.charData 0 (d.exponent - (d.weight.natAbs : ℂ) / 2)) ::
          charList ds

theorem realRank_charList : ∀ ds : List RealBlock, realRank (charList ds) = realRank ds
  | [] => rfl
  | .character _ :: ds => by
      simp only [charList, realRank_cons, rank_character, realRank_charList ds]
  | .induced _ :: ds => by
      simp only [charList, realRank_cons, rank_character, rank_induced, realRank_charList ds]
      omega

theorem realInducedBlockAt_charList : ∀ (ds : List RealBlock) (p : ℕ),
    realInducedBlockAt (charList ds) p = none
  | [], _ => rfl
  | .character _ :: _, 0 => rfl
  | .character _ :: ds, p + 1 => realInducedBlockAt_charList ds p
  | .induced _ :: _, 0 => rfl
  | .induced _ :: _, 1 => rfl
  | .induced _ :: ds, p + 2 => realInducedBlockAt_charList ds p

theorem pow_mod_two_eq {M : Type*} [Monoid M] {y : M} (hy : y ^ 2 = 1) (m : ℕ) :
    y ^ (m % 2) = y ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m 2, pow_add, pow_mul, hy, one_pow, mul_one]

theorem sign_sq (x : ℝˣ) : ((((x : ℝ) / |(x : ℝ)| : ℝ) : ℂ)) ^ 2 = 1 := by
  rw [← Complex.ofReal_pow, div_pow, sq_abs, div_self (pow_ne_zero 2 x.ne_zero),
    Complex.ofReal_one]

theorem realPositionCharacter_charList : ∀ (ds : List RealBlock) (p : ℕ),
    realPositionCharacter (charList ds) p = realPositionCharacter ds p
  | [], _ => rfl
  | .character _ :: _, 0 => rfl
  | .character _ :: ds, p + 1 => realPositionCharacter_charList ds p
  | .induced d :: _, 0 => by
      funext x
      simp only [charList, realPositionCharacter, realInducedFirstCharacter,
        RealJacquetFrobenius.charData_character_apply, RealJacquetFrobenius.charFun]
      rw [pow_mod_two_eq (sign_sq x)]
  | .induced d :: _, 1 => by
      funext x
      simp only [charList, realPositionCharacter, realInducedSecondCharacter,
        RealJacquetFrobenius.charData_character_apply, RealJacquetFrobenius.charFun,
        Fin.val_zero, pow_zero, one_mul]
  | .induced _ :: ds, p + 2 => realPositionCharacter_charList ds p

/-- The standard module of `ds` lies in that of `charList ds`. -/
theorem realStandardModule_le_charList (r : ℕ) (ds : List RealBlock) :
    realStandardModule r ds ≤ realStandardModule r (charList ds) := by
  intro f hf
  have hχ : realPositionCharacter (charList ds) = realPositionCharacter ds :=
    funext (realPositionCharacter_charList ds)
  refine ⟨by rw [hχ]; exact hf.1, fun p d hd => ?_⟩
  rw [realInducedBlockAt_charList] at hd
  cases hd

theorem kFin_le_charList (r : ℕ) (ds : List RealBlock) : KFin r ds ≤ KFin r (charList ds) :=
  fun _ hf => ⟨realStandardModule_le_charList r ds hf.1, hf.2⟩

end CharList

/-! ## An equivariant retraction -/

section Retraction

variable {r : ℕ} (ds : List RealBlock)

/-- The inclusion `KFin r ds → KFin r (charList ds)`. -/
abbrev incl : KFin r ds →ₗ[ℂ] KFin r (charList ds) := Submodule.inclusion (kFin_le_charList r ds)

theorem incl_kRep (k : unitaryCompact ℝ r) (f : KFin r ds) :
    incl ds (kRep r ds k f) = kRep r (charList ds) k (incl ds f) :=
  rfl

theorem exists_retraction : ∃ T : KFin r (charList ds) →ₗ[ℂ] KFin r ds,
    (∀ k f, T (kRep r (charList ds) k f) = kRep r ds k (T f)) ∧ ∀ f, T (incl ds f) = f := by
  obtain ⟨T0, hT0⟩ := LinearMap.exists_leftInverse_of_injective (incl ds)
    (LinearMap.ker_eq_bot.mpr (Submodule.inclusion_injective _))
  refine ⟨avg T0, avg_kRep T0, fun f => ?_⟩
  have h := avg_sub_mem T0 ⊥ (incl ds f) f fun k => by
    rw [Submodule.mem_bot, conj_apply, ← incl_kRep,
      show T0 (incl ds (kRep r ds k f)) = kRep r ds k f from LinearMap.congr_fun hT0 _,
      kRep_inv_kRep, sub_self]
  rwa [Submodule.mem_bot, sub_eq_zero] at h

end Retraction

/-! ## Sign averages of polynomials -/

section SignAverage

variable {r : ℕ}

/-- The real sign vector of `u : Fin r → ℤˣ`. -/
def sv (u : Fin r → ℤˣ) : Fin r → ℝ := fun j => ((u j : ℤ) : ℝ)

/-- The weight `∏ⱼ uⱼ^{qⱼ}`. -/
def wt (q : Fin r → ℕ) (u : Fin r → ℤˣ) : ℂ := ∏ j, ((u j : ℤ) : ℂ) ^ q j

theorem sv_mul (u v : Fin r → ℤˣ) (j : Fin r) : sv (u * v) j = sv u j * sv v j := by
  simp [sv]

theorem wt_mul (q : Fin r → ℕ) (u v : Fin r → ℤˣ) : wt q (u * v) = wt q u * wt q v := by
  unfold wt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [mul_pow]

theorem wt_one (q : Fin r → ℕ) : wt q 1 = 1 := by
  simp [wt]

theorem wt_mul_self (q : Fin r → ℕ) (u : Fin r → ℤˣ) : wt q u * wt q u = 1 := by
  rw [← wt_mul, show u * u = 1 from funext fun j => Int.units_mul_self (u j), wt_one]

/-- Evaluation of a polynomial in the entries of a matrix. -/
def pev (P : MvPolynomial (Fin r × Fin r) ℂ) (Y : Matrix (Fin r) (Fin r) ℝ) : ℂ :=
  MvPolynomial.eval (fun kl => ((Y kl.1 kl.2 : ℝ) : ℂ)) P

/-- The sign average `Y ↦ ∑ᵤ wt(u) P(diag(u) Y)`. -/
def pt (q : Fin r → ℕ) (P : MvPolynomial (Fin r × Fin r) ℂ) (Y : Matrix (Fin r) (Fin r) ℝ) :
    ℂ :=
  ∑ u : Fin r → ℤˣ, wt q u * pev P (Matrix.diagonal (sv u) * Y)

theorem pt_diagonal (q : Fin r → ℕ) (P : MvPolynomial (Fin r × Fin r) ℂ)
    (v : Fin r → ℤˣ) (Y : Matrix (Fin r) (Fin r) ℝ) :
    pt q P (Matrix.diagonal (sv v) * Y) = wt q v * pt q P Y := by
  unfold pt
  have h : ∀ u : Fin r → ℤˣ, wt q u * pev P (Matrix.diagonal (sv u) *
      (Matrix.diagonal (sv v) * Y)) =
      wt q v * (wt q (u * v) * pev P (Matrix.diagonal (sv (u * v)) * Y)) := by
    intro u
    have hd : Matrix.diagonal (sv u) * (Matrix.diagonal (sv v) * Y) =
        Matrix.diagonal (sv (u * v)) * Y := by
      rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
      congr 2
      funext j
      rw [sv_mul]
    rw [hd, wt_mul, ← mul_assoc, ← mul_assoc, mul_comm (wt q v) (wt q u), mul_assoc (wt q u),
      wt_mul_self, mul_one]
  simp_rw [h]
  rw [← Finset.mul_sum]
  congr 1
  exact _root_.Equiv.sum_comp (Equiv.mulRight v)
    (fun w => wt q w * pev P (Matrix.diagonal (sv w) * Y))

/-- The sign vector of a real `±1` vector. -/
def unitsOf (s : Fin r → ℝ) : Fin r → ℤˣ := fun j => if s j = 1 then 1 else -1

theorem sv_unitsOf {s : Fin r → ℝ} (hs : ∀ j, s j = 1 ∨ s j = -1) : sv (unitsOf s) = s := by
  funext j
  unfold sv unitsOf
  rcases hs j with h | h
  · rw [ite_eq_left h, h]
    simp
  · rw [ite_eq_right (by rw [h]; norm_num), h]
    simp

theorem wt_unitsOf (q : Fin r → ℕ) {s : Fin r → ℝ} (hs : ∀ j, s j = 1 ∨ s j = -1) :
    wt q (unitsOf s) = ∏ j, ((s j : ℝ) : ℂ) ^ q j := by
  unfold wt
  refine Finset.prod_congr rfl fun j _ => ?_
  have := congrFun (sv_unitsOf hs) j
  unfold sv at this
  rw [← this]
  push_cast
  rfl

theorem pt_diagonal' (q : Fin r → ℕ) (P : MvPolynomial (Fin r × Fin r) ℂ) {s : Fin r → ℝ}
    (hs : ∀ j, s j = 1 ∨ s j = -1) (Y : Matrix (Fin r) (Fin r) ℝ) :
    pt q P (Matrix.diagonal s * Y) = (∏ j, ((s j : ℝ) : ℂ) ^ q j) * pt q P Y := by
  rw [← wt_unitsOf q hs, ← pt_diagonal, sv_unitsOf hs]

/-- The integer units as real units. -/
def realUnits (u : Fin r → ℤˣ) : Fin r → ℝˣ := fun j => Units.map (Int.castRingHom ℝ).toMonoidHom (u j)

theorem coe_realUnits (u : Fin r → ℤˣ) (j : Fin r) : ((realUnits u j : ℝˣ) : ℝ) = sv u j :=
  rfl

theorem sv_mul_self (u : Fin r → ℤˣ) (j : Fin r) : sv u j * sv u j = 1 := by
  rw [← sv_mul, show u * u = 1 from funext fun j => Int.units_mul_self (u j)]
  simp [sv]

theorem diagonal_sv_mem (u : Fin r → ℤˣ) :
    Matrix.diagonal (sv u) ∈ Matrix.unitaryGroup (Fin r) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  rw [Pi.star_apply, star_trivial, sv_mul_self]

theorem principalSeriesCharacter_realUnits {χ : ℕ → ℝˣ → ℂ} (u : Fin r → ℤˣ) :
    principalSeriesCharacter ℝ r χ (realUnits u) = ∏ j : Fin r, χ j (realUnits u j) := by
  unfold principalSeriesCharacter
  refine Finset.prod_congr rfl fun j _ => ?_
  have h : ‖((realUnits u j : ℝˣ) : ℝ)‖ = 1 := by
    rw [coe_realUnits]
    rcases Int.units_eq_one_or (u j) with h | h <;> simp [sv, h]
  rw [h, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one]

/-- **The sign average on `O(r)`.** If `ψ` lies in a principal series whose characters
satisfy `χⱼ(±1) = (±1)^{qⱼ}` and `P` agrees with `ψ` on `O(r)`, then the sign average of `P` is
`2^r ψ` on `O(r)`. -/
theorem pt_eq {χ : ℕ → ℝˣ → ℂ} {q : Fin r → ℕ}
    (hχ1 : ∀ j : Fin r, χ j 1 = 1) (hχ : ∀ j : Fin r, χ j (-1) = (-1 : ℂ) ^ q j)
    {ψ : Langlands.GeneralLinear r ℝ → ℂ} (hψ : ψ ∈ principalSeries ℝ r χ)
    {P : MvPolynomial (Fin r × Fin r) ℂ}
    (hP : ∀ k : Matrix.unitaryGroup (Fin r) ℝ, ψ (1 * Unitary.toUnits k) =
      MvPolynomial.eval (fun ij => ((k : Matrix (Fin r) (Fin r) ℝ) ij.1 ij.2 : ℂ)) P)
    {k : Langlands.GeneralLinear r ℝ} (hk : k ∈ unitaryCompact ℝ r) :
    pt q P (k : Matrix (Fin r) (Fin r) ℝ) =
      (Fintype.card (Fin r → ℤˣ) : ℂ) * ψ k := by
  have hterm : ∀ u : Fin r → ℤˣ,
      wt q u * pev P (Matrix.diagonal (sv u) * (k : Matrix (Fin r) (Fin r) ℝ)) = ψ k := by
    intro u
    have hmem : Matrix.diagonal (sv u) * (k : Matrix (Fin r) (Fin r) ℝ) ∈
        Matrix.unitaryGroup (Fin r) ℝ :=
      Submonoid.mul_mem _ (diagonal_sv_mem u) hk
    have h1 := hP ⟨_, hmem⟩
    have hU : (1 : Langlands.GeneralLinear r ℝ) * Unitary.toUnits
        (⟨_, hmem⟩ : Matrix.unitaryGroup (Fin r) ℝ) =
        (Iwasawa.diagonalUnits (realUnits u) : Langlands.GeneralLinear r ℝ) *
          ((1 : upperUnipotent r ℝ) : Langlands.GeneralLinear r ℝ) * k := by
      apply Units.ext
      simp only [one_mul, OneMemClass.coe_one, mul_one, Units.val_mul, Iwasawa.diagonalUnits_val]
      rfl
    rw [hU, hψ.2, principalSeriesCharacter_realUnits] at h1
    have hprod : ∏ j : Fin r, χ j (realUnits u j) = wt q u := by
      unfold wt
      refine Finset.prod_congr rfl fun j _ => ?_
      rcases Int.units_eq_one_or (u j) with h | h
      · have : realUnits u j = 1 := by rw [realUnits, h, map_one]
        rw [this, hχ1, h]
        simp
      · have : realUnits u j = -1 := by rw [realUnits, h]; ext; simp
        rw [this, hχ, h]
        simp
    rw [hprod] at h1
    unfold pev
    rw [← h1, ← mul_assoc, wt_mul_self, one_mul]
  unfold pt
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end SignAverage

/-! ## Translate-finiteness and continuity of sums, products and polynomials -/

section Finite

variable {G : Type*} [Group G] {ι : Type*} {s : ι → G}

theorem isTranslateFinite_finset_prod {β : Type*} (t : Finset β) {f : β → G → ℂ}
    (hf : ∀ b ∈ t, IsTranslateFinite s (f b)) :
    IsTranslateFinite s (fun x => ∏ b ∈ t, f b x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isTranslateFinite_const s 1
  | insert b t hb ih =>
      simp only [Finset.prod_insert hb]
      exact isTranslateFinite_mul (hf b (Finset.mem_insert_self b t))
        (ih fun b' hb' => hf b' (Finset.mem_insert_of_mem hb'))

theorem isTranslateFinite_finset_sum {β : Type*} (t : Finset β) {f : β → G → ℂ}
    (hf : ∀ b ∈ t, IsTranslateFinite s (f b)) :
    IsTranslateFinite s (fun x => ∑ b ∈ t, f b x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isTranslateFinite_const s 0
  | insert b t hb ih =>
      simp only [Finset.sum_insert hb]
      exact isTranslateFinite_add (hf b (Finset.mem_insert_self b t))
        (ih fun b' hb' => hf b' (Finset.mem_insert_of_mem hb'))

theorem isTranslateFinite_eval {σ : Type*} (P : MvPolynomial σ ℂ) {x : σ → G → ℂ}
    (hx : ∀ v, IsTranslateFinite s (x v)) :
    IsTranslateFinite s (fun g => MvPolynomial.eval (fun v => x v g) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa using isTranslateFinite_const s c
  | add p q hp hq => simpa using isTranslateFinite_add hp hq
  | mul_X p v hp => simpa using isTranslateFinite_mul hp (hx v)

theorem continuous_eval_comp {X σ : Type*} [TopologicalSpace X] (P : MvPolynomial σ ℂ)
    {x : σ → X → ℂ} (hx : ∀ v, Continuous (x v)) :
    Continuous (fun y => MvPolynomial.eval (fun v => x v y) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa using continuous_const
  | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq
  | mul_X p v hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      exact hp.mul (hx v)

end Finite

/-! ## Positions of induction blocks -/

section Positions

variable (L : List RealBlock)

/-- The exponent `0` or `1` of the sign of the position character of `L` at `i`. -/
def sgnExp (i : ℕ) : ℕ := if realPositionCharacter L i (-1) = 1 then 0 else 1

theorem neg_one_pow_sgnExp (i : ℕ) :
    (-1 : ℂ) ^ sgnExp L i = realPositionCharacter L i (-1) := by
  unfold sgnExp
  split_ifs with h1
  · rw [pow_zero, h1]
  · rcases RealStrictCharacterLanglandsQuotient.realPositionCharacter_neg_one L i with h | h
    · exact absurd h h1
    · rw [pow_one, h]

/-- At an induction block the next position starts no induction block, and the two position
characters are those of the block. -/
theorem induced_succ : ∀ (ds : List RealBlock) (p : ℕ) (d : ComplexCharacterData),
    realInducedBlockAt ds p = some d →
      realInducedBlockAt ds (p + 1) = none ∧
        realPositionCharacter ds p = realInducedFirstCharacter d ∧
          realPositionCharacter ds (p + 1) = realInducedSecondCharacter d
  | [], _, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: _, 0, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: ds, p + 1, d, h => induced_succ ds p d h
  | .induced e :: _, 0, d, h => by
      simp only [realInducedBlockAt, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩
  | .induced _ :: _, 1, _, h => by simp [realInducedBlockAt] at h
  | .induced _ :: ds, p + 2, d, h => induced_succ ds p d h

theorem sgnExp_succ_of_some {p : ℕ} {d : ComplexCharacterData}
    (hd : realInducedBlockAt L p = some d) : sgnExp L (p + 1) = 0 := by
  unfold sgnExp
  rw [(induced_succ L p d hd).2.2]
  simp [realInducedSecondCharacter]

theorem realInducedFirstCharacter_neg_one (d : ComplexCharacterData) :
    realInducedFirstCharacter d (-1) = (-1 : ℂ) ^ (d.weight.natAbs + 1) := by
  simp [realInducedFirstCharacter]

end Positions

/-! ## The test function -/

section Test

variable {n : ℕ} (L : List RealBlock) {a r : ℕ}

variable (a r) in
/-- The factor of the row `i`: the block factor `Z^{|m|+1} + Z̄^{|m|+1}` at the first row of an
induction block of weight `m`, the sign power `κᵢᵢ^{e}` of the position character at the other
rows outside the middle block, and `1` in the middle block. -/
def gFac (i : Fin n) (κ : Matrix (Fin n) (Fin n) ℝ) : ℂ :=
  (realInducedBlockAt L i).elim (if IsMid a r i then 1 else ((κ i i : ℝ) : ℂ) ^ sgnExp L i)
    fun d => if hb : (i : ℕ) + 1 < n then bf hb (ia hb) (ia hb) d.weight.natAbs κ else 1

variable (a r) in
/-- The sign exponent of the row factor `gFac`. -/
def gExp (i : Fin n) : ℕ :=
  (realInducedBlockAt L i).elim (if IsMid a r i then 0 else sgnExp L i)
    fun d => d.weight.natAbs + 1

variable (a r) in
/-- The sign exponent of the middle factor. -/
def mExp (i : Fin n) : ℕ := if IsMid a r i then sgnExp L i else 0

variable (a r) in
/-- The middle factor: the sign average of `P` at the middle block. -/
def ptMid (P : MvPolynomial (Fin r × Fin r) ℂ) (κ : Matrix (Fin n) (Fin n) ℝ) : ℂ :=
  pt (fun j => sgnExp L (a + j)) P (midBlock n a r κ)

variable (a r) in
/-- The test function: the product of the row factors times the middle factor. -/
def testFun (P : MvPolynomial (Fin r × Fin r) ℂ) (κ : Matrix (Fin n) (Fin n) ℝ) : ℂ :=
  (∏ i, gFac L a r i κ) * ptMid L a r P κ

theorem gFac_of_none {i : Fin n} (hi : realInducedBlockAt L i = none)
    (κ : Matrix (Fin n) (Fin n) ℝ) :
    gFac L a r i κ = if IsMid a r i then 1 else ((κ i i : ℝ) : ℂ) ^ sgnExp L i := by
  unfold gFac
  rw [hi]
  rfl

theorem gFac_of_some {i : Fin n} (hb : (i : ℕ) + 1 < n) {d : ComplexCharacterData}
    (hi : realInducedBlockAt L i = some d) (κ : Matrix (Fin n) (Fin n) ℝ) :
    gFac L a r i κ = bf hb (ia hb) (ia hb) d.weight.natAbs κ := by
  unfold gFac
  rw [hi]
  exact dite_eq_left hb

theorem gFac_ia {p : ℕ} (hp : p + 1 < n) {d : ComplexCharacterData}
    (hd : realInducedBlockAt L p = some d) (κ : Matrix (Fin n) (Fin n) ℝ) :
    gFac L a r (ia hp) κ = bf hp (ia hp) (ia hp) d.weight.natAbs κ :=
  gFac_of_some L (i := ia hp) hp hd κ

theorem gExp_of_none {i : Fin n} (hi : realInducedBlockAt L i = none) :
    gExp L a r i = if IsMid a r i then 0 else sgnExp L i := by
  unfold gExp
  rw [hi]
  rfl

theorem gExp_of_some {i : Fin n} {d : ComplexCharacterData}
    (hi : realInducedBlockAt L i = some d) : gExp L a r i = d.weight.natAbs + 1 := by
  unfold gExp
  rw [hi]
  rfl

theorem lt_of_some (hn : realRank L = n) {i : ℕ} {d : ComplexCharacterData}
    (hi : realInducedBlockAt L i = some d) : i + 1 < n := by
  rw [← hn]
  exact realInducedBlockAt_lt hi

/-! ### Signs -/

theorem gFac_diag (hn : realRank L = n) (i : Fin n) {s : Fin n → ℝ}
    (hs : ∀ i, s i = 1 ∨ s i = -1) (κ : Matrix (Fin n) (Fin n) ℝ) :
    gFac L a r i (Matrix.diagonal s * κ) = ((s i : ℝ) : ℂ) ^ gExp L a r i * gFac L a r i κ := by
  cases hi : realInducedBlockAt L i with
  | none =>
      rw [gFac_of_none L hi, gFac_of_none L hi, gExp_of_none L hi]
      split_ifs
      · simp
      · rw [Matrix.diagonal_mul, Complex.ofReal_mul, mul_pow]
  | some d =>
      have hb := lt_of_some L hn hi
      rw [gFac_of_some L hb hi, gFac_of_some L hb hi, gExp_of_some L hi,
        isSignEq_bf hb (ia hb) (ia hb) d.weight.natAbs s hs κ, prod_pow_single]
      rfl

theorem midBlock_diagonal_mul (h : a + r ≤ n) (s : Fin n → ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    midBlock n a r (Matrix.diagonal s * κ) =
      Matrix.diagonal (fun j => s (idx h j)) * midBlock n a r κ := by
  ext j l
  rw [midBlock_apply h, Matrix.diagonal_mul, Matrix.diagonal_mul, midBlock_apply h]

theorem isSignEq_ptMid (h : a + r ≤ n) (P : MvPolynomial (Fin r × Fin r) ℂ) :
    IsSignEq (n := n) (mExp L a r) (ptMid L a r P) := by
  intro s hs κ
  unfold ptMid
  rw [midBlock_diagonal_mul h, pt_diagonal' _ P (fun j => hs (idx h j))]
  congr 1
  refine Fintype.prod_of_injective (idx h) (idx_injective h) _ _ (fun i hi => ?_) (fun j => ?_)
  · rw [mExp, ite_eq_right ((not_isMid_iff_not_mem_range h i).mpr hi), pow_zero]
  · rw [mExp, ite_eq_left (isMid_idx h j)]
    rfl

theorem isSignEq_testFun (hn : realRank L = n) (h : a + r ≤ n)
    (P : MvPolynomial (Fin r × Fin r) ℂ) :
    IsSignEq (n := n) (gExp L a r + mExp L a r) (testFun L a r P) := by
  have hg : IsSignEq (n := n) (gExp L a r) (fun κ => ∏ i, gFac L a r i κ) := by
    intro s hs κ
    dsimp only
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => gFac_diag L hn i hs κ
  exact isSignEq_mul hg (isSignEq_ptMid L h P)

theorem neg_one_pow_exp
    (hout : ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt L p = some d →
      p + 1 < a ∨ a + r ≤ p) (i : Fin n) :
    (-1 : ℂ) ^ (gExp L a r i + mExp L a r i) = realPositionCharacter L i (-1) := by
  cases hi : realInducedBlockAt L i with
  | none =>
      rw [gExp_of_none L hi, mExp]
      split_ifs
      · rw [zero_add, neg_one_pow_sgnExp]
      · rw [add_zero, neg_one_pow_sgnExp]
  | some d =>
      have hmid : ¬IsMid a r i := by
        have := hout _ _ hi
        unfold IsMid
        omega
      rw [gExp_of_some L hi, mExp, ite_eq_right hmid, add_zero, (induced_succ L i d hi).2.1,
        realInducedFirstCharacter_neg_one]

/-! ### Rotations of an induction block -/

theorem not_isMid_ia (hout : ∀ (p : ℕ) (d : ComplexCharacterData),
      realInducedBlockAt L p = some d → p + 1 < a ∨ a + r ≤ p)
    {p : ℕ} (hp : p + 1 < n) {d : ComplexCharacterData} (hd : realInducedBlockAt L p = some d) :
    ¬IsMid a r (ia hp) ∧ ¬IsMid a r (ib hp) := by
  have := hout p d hd
  unfold IsMid
  simp only [ia, ib]
  omega

theorem midBlock_rot (h : a + r ≤ n) {p : ℕ} (hp : p + 1 < n) (h1 : ¬IsMid a r (ia hp))
    (h2 : ¬IsMid a r (ib hp)) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    midBlock n a r ((blockRotation n p φ : Matrix (Fin n) (Fin n) ℝ) * κ) = midBlock n a r κ := by
  ext j l
  rw [midBlock_apply h, midBlock_apply h,
    rot_mul_of_ne hp φ κ (fun e => h1 (e ▸ isMid_idx h j)) (fun e => h2 (e ▸ isMid_idx h j))]

theorem gFac_rot_of_ne (hn : realRank L = n) {p : ℕ} (hp : p + 1 < n)
    {d : ComplexCharacterData} (hd : realInducedBlockAt L p = some d) {i : Fin n}
    (hi : i ≠ ia hp) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    gFac L a r i ((blockRotation n p φ : Matrix (Fin n) (Fin n) ℝ) * κ) = gFac L a r i κ := by
  have hip : (i : ℕ) ≠ p := fun e => hi (Fin.ext e)
  obtain ⟨hnone, -, -⟩ := induced_succ L p d hd
  cases hj : realInducedBlockAt L i with
  | none =>
      rw [gFac_of_none L hj, gFac_of_none L hj]
      split_ifs
      · rfl
      · by_cases hi2 : i = ib hp
        · have h0 : sgnExp L (i : ℕ) = 0 := by
            rw [hi2]
            exact sgnExp_succ_of_some L hd
          rw [h0, pow_zero, pow_zero]
        · rw [rot_mul_of_ne hp φ κ hi hi2]
  | some e =>
      have hb := lt_of_some L hn hj
      obtain ⟨hnone', -, -⟩ := induced_succ L i e hj
      have h1 : (i : ℕ) ≠ p + 1 := fun e' => by
        rw [e', hnone] at hj
        cases hj
      have h2 : p ≠ (i : ℕ) + 1 := fun e' => by
        rw [e', hnone'] at hd
        cases hd
      rw [gFac_of_some L hb hj, gFac_of_some L hb hj]
      exact bf_rot_of_disjoint hb hp (by omega) _ _ _ φ κ

theorem testFun_rot (h : a + r ≤ n) (hn : realRank L = n)
    (hout : ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt L p = some d →
      p + 1 < a ∨ a + r ≤ p)
    {p : ℕ} (hp : p + 1 < n) {d : ComplexCharacterData} (hd : realInducedBlockAt L p = some d)
    (P : MvPolynomial (Fin r × Fin r) ℂ) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    testFun L a r P ((blockRotation n p φ : Matrix (Fin n) (Fin n) ℝ) * κ) =
      expMode ((d.weight.natAbs : ℤ) + 1) φ *
          (zp hp (ia hp) κ ^ d.weight.natAbs * zp hp (ia hp) κ *
            ((∏ i ∈ Finset.univ.erase (ia hp), gFac L a r i κ) * ptMid L a r P κ)) +
        expMode (-((d.weight.natAbs : ℤ) + 1)) φ *
          (zm hp (ia hp) κ ^ d.weight.natAbs * zm hp (ia hp) κ *
            ((∏ i ∈ Finset.univ.erase (ia hp), gFac L a r i κ) * ptMid L a r P κ)) := by
  obtain ⟨h1, h2⟩ := not_isMid_ia L hout hp hd
  have hrest : ∏ i ∈ Finset.univ.erase (ia hp),
      gFac L a r i ((blockRotation n p φ : Matrix (Fin n) (Fin n) ℝ) * κ) =
      ∏ i ∈ Finset.univ.erase (ia hp), gFac L a r i κ :=
    Finset.prod_congr rfl fun i hi => gFac_rot_of_ne L hn hp hd (Finset.ne_of_mem_erase hi) φ κ
  have hmid : ptMid L a r P ((blockRotation n p φ : Matrix (Fin n) (Fin n) ℝ) * κ) =
      ptMid L a r P κ := by
    unfold ptMid
    rw [midBlock_rot h hp h1 h2]
  unfold testFun
  rw [hmid, ← Finset.mul_prod_erase Finset.univ
      (fun i => gFac L a r i ((blockRotation n p φ : Matrix (Fin n) (Fin n) ℝ) * κ))
      (Finset.mem_univ (ia hp)), hrest, gFac_ia L hp hd, bf_rot]
  ring

theorem abs_lt_natAbs_succ {j m : ℤ} (h : |j| < |m|) : |j| < |((m.natAbs : ℕ) : ℤ) + 1| := by
  have h1 : |((m.natAbs : ℕ) : ℤ) + 1| = (m.natAbs : ℤ) + 1 := abs_of_nonneg (by positivity)
  rw [h1]
  rw [Int.abs_eq_natAbs m] at h
  omega

theorem coeff_testFun (h : a + r ≤ n) (hn : realRank L = n)
    (hout : ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt L p = some d →
      p + 1 < a ∨ a + r ≤ p)
    {p : ℕ} {d : ComplexCharacterData} (hd : realInducedBlockAt L p = some d)
    (P : MvPolynomial (Fin r × Fin r) ℂ) {k : ℤ} (hk : |k| < |d.weight|)
    (κ : Matrix (Fin n) (Fin n) ℝ) :
    coeff k (fun φ => testFun L a r P ((blockRotation n p φ : Matrix (Fin n) (Fin n) ℝ) * κ)) =
      0 :=
  coeff_eq_zero_of_two_mode (fun φ κ => testFun_rot L h hn hout (lt_of_some L hn hd) hd P φ κ)
    (abs_lt_natAbs_succ hk) κ

/-! ### Continuity and translate-finiteness -/

theorem continuous_gFac (hn : realRank L = n) (i : Fin n) : Continuous (gFac L a r i) := by
  cases hi : realInducedBlockAt L i with
  | none =>
      rw [funext (gFac_of_none L hi)]
      by_cases hm : IsMid a r i
      · simp only [hm, ↓reduceIte]
        exact continuous_const
      · simp only [hm, ↓reduceIte]
        exact (continuous_entry i i).pow _
  | some d =>
      have hb := lt_of_some L hn hi
      rw [funext (gFac_of_some L hb hi)]
      exact continuous_bf hb _ _ _

theorem isTranslateFinite_gFac (hn : realRank L = n) (i : Fin n) :
    IsTranslateFinite (id : Matrix.unitaryGroup (Fin n) ℝ → Matrix.unitaryGroup (Fin n) ℝ)
      (fun κ => gFac L a r i (κ : Matrix (Fin n) (Fin n) ℝ)) := by
  cases hi : realInducedBlockAt L i with
  | none =>
      simp only [gFac_of_none L hi]
      by_cases hm : IsMid a r i
      · simp only [hm, ↓reduceIte]
        exact isTranslateFinite_const _ 1
      · simp only [hm, ↓reduceIte]
        exact isTranslateFinite_pow (isTranslateFinite_entry (i, i)) _
  | some d =>
      have hb := lt_of_some L hn hi
      simp only [gFac_of_some L hb hi]
      exact isTranslateFinite_bf hb _ _ _

theorem ptMid_eq (h : a + r ≤ n) (P : MvPolynomial (Fin r × Fin r) ℂ)
    (κ : Matrix (Fin n) (Fin n) ℝ) :
    ptMid L a r P κ = ∑ u : Fin r → ℤˣ, wt (fun j => sgnExp L (a + j)) u *
      MvPolynomial.eval (fun kl => ((sv u kl.1 : ℝ) : ℂ) *
        ((κ (idx h kl.1) (idx h kl.2) : ℝ) : ℂ)) P := by
  unfold ptMid pt
  refine Finset.sum_congr rfl fun u _ => ?_
  unfold pev
  have he : (fun kl : Fin r × Fin r =>
      (((Matrix.diagonal (sv u) * midBlock n a r κ) kl.1 kl.2 : ℝ) : ℂ)) =
      fun kl => ((sv u kl.1 : ℝ) : ℂ) * ((κ (idx h kl.1) (idx h kl.2) : ℝ) : ℂ) := by
    funext kl
    rw [Matrix.diagonal_mul, midBlock_apply h, Complex.ofReal_mul]
  rw [he]

theorem continuous_testFun (hn : realRank L = n) (h : a + r ≤ n)
    (P : MvPolynomial (Fin r × Fin r) ℂ) : Continuous (testFun (n := n) L a r P) := by
  have h1 : Continuous fun κ : Matrix (Fin n) (Fin n) ℝ => ∏ i, gFac L a r i κ :=
    continuous_finsetProd _ fun i _ => continuous_gFac L hn i
  have h2 : Continuous (ptMid (n := n) L a r P) := by
    rw [funext (ptMid_eq L h P)]
    exact continuous_finsetSum _ fun u _ => continuous_const.mul
      (continuous_eval_comp P fun kl => continuous_const.mul (continuous_entry _ _))
  exact h1.mul h2

theorem isTranslateFinite_testFun (hn : realRank L = n) (h : a + r ≤ n)
    (P : MvPolynomial (Fin r × Fin r) ℂ) :
    IsTranslateFinite (id : Matrix.unitaryGroup (Fin n) ℝ → Matrix.unitaryGroup (Fin n) ℝ)
      (fun κ => testFun L a r P (κ : Matrix (Fin n) (Fin n) ℝ)) := by
  have h1 : IsTranslateFinite (id : Matrix.unitaryGroup (Fin n) ℝ → Matrix.unitaryGroup (Fin n) ℝ)
      (fun κ => ∏ i, gFac L a r i (κ : Matrix (Fin n) (Fin n) ℝ)) :=
    isTranslateFinite_finset_prod _ fun i _ => isTranslateFinite_gFac L hn i
  have h2 : IsTranslateFinite (id : Matrix.unitaryGroup (Fin n) ℝ → Matrix.unitaryGroup (Fin n) ℝ)
      (fun κ => ptMid L a r P (κ : Matrix (Fin n) (Fin n) ℝ)) := by
    simp only [ptMid_eq L h P]
    exact isTranslateFinite_finset_sum _ fun u _ => isTranslateFinite_smul
      (isTranslateFinite_eval P fun kl => isTranslateFinite_smul
        (isTranslateFinite_entry (idx h kl.1, idx h kl.2)) _) _
  exact isTranslateFinite_mul h1 h2

/-! ### Values on the middle block -/

theorem midBlock_blockMat (h : a + r ≤ n) (y : Matrix (Fin r) (Fin r) ℝ) :
    midBlock n a r (blockMat n a r y) = y := by
  ext j l
  rw [midBlock_apply h, blockMat_apply_idx h]

theorem gFac_blockMat (hn : realRank L = n)
    (hout : ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt L p = some d →
      p + 1 < a ∨ a + r ≤ p) (i : Fin n) (y : Matrix (Fin r) (Fin r) ℝ) :
    gFac L a r i (blockMat n a r y) = gFac L a r i 1 := by
  cases hi : realInducedBlockAt L i with
  | none =>
      rw [gFac_of_none L hi, gFac_of_none L hi]
      split_ifs with hm
      · rfl
      · rw [blockMat_apply_of_not_isMid_left y hm]
  | some d =>
      have hb := lt_of_some L hn hi
      obtain ⟨h1, h2⟩ := not_isMid_ia L hout hb hi
      rw [gFac_of_some L hb hi, gFac_of_some L hb hi]
      simp only [bf, zp, zm, blockMat_apply_of_not_isMid_left y h1,
        blockMat_apply_of_not_isMid_left y h2]

theorem gFac_one_ne_zero (hn : realRank L = n) (i : Fin n) :
    gFac L a r i (1 : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  cases hi : realInducedBlockAt L i with
  | none =>
      rw [gFac_of_none L hi]
      split_ifs
      · exact one_ne_zero
      · simp
  | some d =>
      have hb := lt_of_some L hn hi
      rw [gFac_of_some L hb hi]
      have h1 : zp hb (ia hb) (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
        simp [zp, Matrix.one_apply_ne (ia_ne_ib hb).symm]
      have h2 : zm hb (ia hb) (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
        simp [zm, Matrix.one_apply_ne (ia_ne_ib hb).symm]
      rw [bf, h1, h2]
      norm_num

theorem testFun_blockMat (h : a + r ≤ n) (hn : realRank L = n)
    (hout : ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt L p = some d →
      p + 1 < a ∨ a + r ≤ p) (P : MvPolynomial (Fin r × Fin r) ℂ)
    (y : Matrix (Fin r) (Fin r) ℝ) :
    testFun L a r P (blockMat n a r y) =
      (∏ i, gFac (n := n) L a r i 1) * pt (fun j => sgnExp L (a + j)) P y := by
  unfold testFun ptMid
  rw [midBlock_blockMat h]
  congr 1
  exact Finset.prod_congr rfl fun i _ => gFac_blockMat L hn hout i y

end Test

/-! ## Surjectivity of the slice at the identity -/

section Surjective

variable {n a r : ℕ}

/-- **The slice at the identity is onto, without induction blocks in the middle.** -/
theorem sliceK_one_surjective_of_none {pre M post : List RealBlock} (h : a + r ≤ n)
    (ha : realRank pre = a) (hr : realRank M = r) (hn : realRank (pre ++ M ++ post) = n)
    (hM : ∀ p, realInducedBlockAt M p = none) :
    Function.Surjective (sliceK (post := post) h ha hr 1) := by
  intro ψ
  have hout : ∀ (p : ℕ) (d : ComplexCharacterData),
      realInducedBlockAt (pre ++ M ++ post) p = some d → p + 1 < a ∨ a + r ≤ p := by
    intro p d hd
    rcases realInducedBlockAt_append_cases (pre ++ M) post p d hd with ⟨-, h2⟩ | ⟨h1, -⟩
    · rcases realInducedBlockAt_append_cases pre M p d h2 with ⟨h3, -⟩ | ⟨-, h4⟩
      · exact Or.inl (ha ▸ h3)
      · rw [hM] at h4
        cases h4
    · right
      rw [realRank_append', ha, hr] at h1
      exact h1
  obtain ⟨P, hP⟩ := OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors
    ψ.2.1.1.1.continuous ψ.2.2 1
  obtain ⟨v, hv⟩ := exists_KF (ds := pre ++ M ++ post) hn
    (continuous_testFun (pre ++ M ++ post) hn h P)
    (isTranslateFinite_testFun (pre ++ M ++ post) hn h P)
    (isSignEq_testFun (pre ++ M ++ post) hn h P)
    (fun i => neg_one_pow_exp (pre ++ M ++ post) hout i)
    (fun p d hd k hk κ _ => coeff_testFun (pre ++ M ++ post) h hn hout hd P hk κ)
  set c0 : ℂ := (∏ i, gFac (pre ++ M ++ post) a r i 1) * (Fintype.card (Fin r → ℤˣ) : ℂ)
    with hc0
  have hc0ne : c0 ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => gFac_one_ne_zero _ hn i)
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hχ : ∀ j : Fin r, realPositionCharacter M j (-1) =
      (-1 : ℂ) ^ sgnExp (pre ++ M ++ post) (a + j) := fun j => by
    rw [neg_one_pow_sgnExp, realPositionCharacter_mid ha hr j]
  have hslice : slice h ((1 : unitaryCompact ℝ n) : Langlands.GeneralLinear n ℝ)
      (v : Langlands.GeneralLinear n ℝ → ℂ) = c0 • (ψ : Langlands.GeneralLinear r ℝ → ℂ) := by
    refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries
      (slice_mem_realStandardModule h ha hr _ v.2.1).1
      (Submodule.smul_mem _ c0 ψ.2.1.1) fun k hk => ?_
    rw [slice_apply, sliceFactor_of_mem_unitaryCompact hk, one_mul, OneMemClass.coe_one, mul_one,
      hv _ (blockEmb_mem_unitaryCompact h hk), blockEmb_val,
      testFun_blockMat (pre ++ M ++ post) h hn hout P,
      pt_eq (fun j => RealStrictCharacterLanglandsQuotient.realPositionCharacter_one M j) hχ
        ψ.2.1.1 hP hk, Pi.smul_apply, smul_eq_mul, hc0]
    ring
  refine ⟨c0⁻¹ • v, Subtype.ext ?_⟩
  rw [map_smul, Submodule.coe_smul, sliceK_apply_coe, hslice, smul_smul, inv_mul_cancel₀ hc0ne,
    one_smul]

/-- **The slice at the identity is onto.** For `a = rank pre`, `r = rank ds` and
`n = rank (pre ++ ds ++ post)`, every `O(r)`-finite function of the standard module of `ds` is
`σ₁ F` for an `O(n)`-finite function `F` of the standard module of `pre ++ ds ++ post`. -/
theorem sliceK_one_surjective {pre ds post : List RealBlock} (h : a + r ≤ n)
    (ha : realRank pre = a) (hr : realRank ds = r) (hn : realRank (pre ++ ds ++ post) = n) :
    Function.Surjective (sliceK (post := post) h ha hr 1) := by
  intro ψ
  obtain ⟨T, hT, hTi⟩ := exists_retraction (r := r) ds
  have hr' : realRank (charList ds) = r := (realRank_charList ds).trans hr
  have hn' : realRank (pre ++ charList ds ++ post) = n := by
    have := hn
    rw [realRank_append', realRank_append'] at this ⊢
    rw [realRank_charList]
    exact this
  obtain ⟨G, hG⟩ := sliceK_one_surjective_of_none h ha hr' hn' (realInducedBlockAt_charList ds)
    (incl ds ψ)
  refine ⟨ind h ha hr hr' hn T hT G, ?_⟩
  rw [sliceK_ind, hG, hTi]

end Surjective

end RealSliceSurjective

end Langlands.Archimedean

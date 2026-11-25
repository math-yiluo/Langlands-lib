import Langlands.Theta.WeilIndex.OneDimensional

/-!
# The Weil index in the unramified case

GKT §3.2.4: Lemma 3.23, Propositions 3.24 and 3.25, Corollary 3.26 (pp. 86–87). Let `F` be a
nonarchimedean local field with `2 ≠ 0` and valuation `v`, and `ψ` a non-trivial unitary character
of `F` with conductor `c` (`UnitaryAdditiveCharacter.IsConductor ψ c`: `ψ` is trivial on the ball
`{v x ≤ v c}` and non-trivial on every larger ball; the book's `ϖ^r O`, `c = ϖ^r`).

* Lemma 3.23 (`annihilator_valuationBall`): for the character of second degree `x ↦ ψ(a x²)`, whose
  bicharacter is `ψ(2a x y)`, the annihilator of the ball `{v x ≤ v t}` is the ball
  `{v x ≤ v(c / (2 a t))}`. (The book's case `a = 1`, `t = ϖ^{⌈r/2⌉}`: `ϖ^{r/2 - e} O` or
  `ϖ^{(r-1)/2 - e} O`, `2 O = ϖ^e O`.)
* Proposition 3.24 (`weilIndexOne_scale_eq_one`): if `v(2) = 1` (odd residue characteristic) and
  `v(c) = v(a) v(t)²` for some `t` (`ord c - ord a` even; the book's "`r + s` even"), then
  `γ(ψ_a) = 1`: the ball `{v x ≤ v t}` is then a self-dual lattice on which `ψ(a x²) = 1`
  (Corollary 3.11).
* Proposition 3.25 (`weilIndex_diagonal_eq_one`, `weilIndex_eq_one_of_isometryEquiv`) and
  Corollary 3.26 (`weilIndex_eq_one_of_isConductor_one`): products.
-/

noncomputable section

open ValuativeRel

namespace Langlands

namespace HarmonicAnalysis.UnitaryAdditiveCharacter

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]

/-- **`ψ` has conductor `c`** (GKT §3.2.4: "`ϖ^r O` is the conductor of `ψ`, so that `ψ` is trivial
on `ϖ^r O` but not on `ϖ^{r-1} O`"): `ψ` is trivial on the ball `{v x ≤ v c}` and non-trivial on
every ball `{v x ≤ v s}` with `v s > v c`. -/
def IsConductor (ψ : UnitaryAdditiveCharacter F) (c : Fˣ) : Prop :=
  (∀ x : F, valuation F x ≤ valuation F (c : F) → ψ x = 1) ∧
    ∀ s : Fˣ, valuation F (c : F) < valuation F (s : F) →
      ∃ x : F, valuation F x ≤ valuation F (s : F) ∧ ψ x ≠ 1

end HarmonicAnalysis.UnitaryAdditiveCharacter

namespace Theta

open HarmonicAnalysis LocalClassField

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

attribute [local instance] WeilIndex.Internal.secondCountableTopology_self
  WeilIndex.Internal.locallyCompactSpace_self WeilIndex.Internal.compactOpenExhaustion_self

namespace WeilIndex.Internal

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_valuationBall_iff (t : Fˣ) (x : F) :
    x ∈ valuationBall t ↔ valuation F x ≤ valuation F (t : F) := by
  simp only [valuationBall, Set.mem_ofPred_eq]

/-- The ball `{v x ≤ v t}` as an additive subgroup. -/
def valuationBallSubgroup (t : Fˣ) : AddSubgroup F where
  carrier := valuationBall t
  zero_mem' := by rw [mem_valuationBall_iff]; simp
  add_mem' {x y} ha hb := by
    rw [mem_valuationBall_iff] at ha hb ⊢
    exact (valuation F).map_add_le ha hb
  neg_mem' {x} hx := by
    rw [mem_valuationBall_iff] at hx ⊢
    rwa [Valuation.map_neg]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coe_valuationBallSubgroup (t : Fˣ) :
    (valuationBallSubgroup t : Set F) = valuationBall t := rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `u x ∈ {v ≤ v c}` if and only if `x ∈ {v ≤ v(u⁻¹ c)}`. -/
theorem mul_mem_valuationBall_iff (u c : Fˣ) (x : F) :
    (u : F) * x ∈ valuationBall c ↔ x ∈ valuationBall (u⁻¹ * c) := by
  simp only [valuationBall, Set.mem_ofPred_eq, Units.val_mul, Units.val_inv_eq_inv_val, map_mul,
    map_inv₀]
  rw [le_inv_mul_iff₀ (by simp [zero_lt_iff])]

end WeilIndex.Internal

open WeilIndex.Internal

variable [NeZero (2 : F)] (ψ : UnitaryAdditiveCharacter F)

/-- The bicharacter of `x ↦ ψ(a x²)` is `ψ(2 a x y)`. -/
theorem secondDegreeBicharacter_mul_sq (a : Fˣ) :
    secondDegreeBicharacter (fun x : F => ψ.complex (a * x ^ 2)) =
      fun x y => ψ.complex (2 * a * (x * y)) := by
  refine secondDegreeBicharacter_eq (isCharacterOfSecondDegree_mul_sq ψ a).ne_zero fun x y => ?_
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- **GKT Lemma 3.23** (valuation form): if `ψ` has conductor `c`, the annihilator of the ball
`{v x ≤ v t}` for the bicharacter `ψ(2 a x y)` of `x ↦ ψ(a x²)` is the ball
`{v x ≤ v((2 a t)⁻¹ c)}`. -/
theorem annihilator_valuationBall {c : Fˣ} (hc : ψ.IsConductor c) (a t : Fˣ) :
    ((isCharacterOfSecondDegree_mul_sq ψ a).isSelfDualBicharacter.annihilator
        (valuationBall t) : Set F) =
      valuationBall ((Units.mk0 (2 : F) two_ne_zero * a * t)⁻¹ * c) := by
  ext z
  have hb := secondDegreeBicharacter_mul_sq ψ a
  change (∀ y ∈ valuationBall t, secondDegreeBicharacter _ y z = 1) ↔ _
  rw [hb]
  simp only [UnitaryAdditiveCharacter.complex_apply]
  have hcoe : ∀ w : F, ((ψ w : Circle) : ℂ) = 1 ↔ ψ w = 1 := fun w => by
    rw [← Circle.coe_one, Circle.coe_inj]
  simp_rw [hcoe]
  rw [← mul_mem_valuationBall_iff]
  constructor
  · intro h
    by_contra hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hz (by rw [mem_valuationBall_iff]; simp)
    set s : Fˣ := Units.mk0 (2 : F) two_ne_zero * a * t * Units.mk0 z hz0
    have hs : valuation F (c : F) < valuation F (s : F) := by
      rw [mem_valuationBall_iff, not_le] at hz
      simpa [s] using hz
    obtain ⟨w, hw, hψw⟩ := hc.2 s hs
    have h2az : (2 * a * z : F) ≠ 0 := by
      simp [two_ne_zero, a.ne_zero, hz0]
    refine hψw ?_
    have hy : w * (2 * a * z)⁻¹ ∈ valuationBall t := by
      rw [mem_valuationBall_iff]
      have hs' : valuation F (s : F) = valuation F (2 * a * z) * valuation F (t : F) := by
        simp only [s, Units.val_mul, Units.val_mk0, map_mul]
        exact mul_right_comm _ _ _
      rw [map_mul, map_inv₀]
      rw [hs'] at hw
      have hpos : 0 < valuation F (2 * a * z : F) := by
        rw [zero_lt_iff]; exact (map_ne_zero _).2 h2az
      rw [mul_inv_le_iff₀ hpos]
      calc valuation F w ≤ valuation F (2 * a * z) * valuation F (t : F) := hw
        _ = valuation F (t : F) * valuation F (2 * a * z) := mul_comm _ _
    have := h _ hy
    rwa [show 2 * (a : F) * (w * (2 * a * z)⁻¹ * z) = w by field_simp] at this
  · intro h y hy
    rw [mem_valuationBall_iff] at h hy
    refine hc.1 _ ?_
    have h1 : valuation F (y * (t : F)⁻¹) ≤ 1 := by
      rw [map_mul, map_inv₀]
      have hpos : 0 < valuation F (t : F) := by rw [zero_lt_iff]; simp
      rw [mul_inv_le_iff₀ hpos, one_mul]
      exact hy
    have e : 2 * (a : F) * (y * z) =
        ((Units.mk0 (2 : F) two_ne_zero * a * t : Fˣ) : F) * z * (y * (t : F)⁻¹) := by
      simp only [Units.val_mul, Units.val_mk0]
      field_simp
    rw [e, map_mul]
    calc valuation F (((Units.mk0 (2 : F) two_ne_zero * a * t : Fˣ) : F) * z) *
          valuation F (y * (t : F)⁻¹)
        ≤ valuation F (((Units.mk0 (2 : F) two_ne_zero * a * t : Fˣ) : F) * z) * 1 :=
          mul_le_mul_right h1 _
      _ = _ := mul_one _
      _ ≤ _ := h

/-- **GKT Proposition 3.24** (valuation form): if `v(2) = 1` (the residue characteristic is odd),
`ψ` has conductor `c` and `v(c) = v(a) v(t)²` for some `t` (`ord c - ord a` is even; the book's
"`r + s` even", the conductor of `ψ_a` being `ϖ^{r-s} O`), then `γ(ψ_a) = 1`. -/
theorem weilIndexOne_scale_eq_one (h2 : valuation F (2 : F) = 1) {c : Fˣ}
    (hc : ψ.IsConductor c) (a t : Fˣ)
    (ht : valuation F (c : F) = valuation F (a : F) * valuation F (t : F) ^ 2) :
    weilIndexOne (ψ.scale a) = 1 := by
  have hf := isCharacterOfSecondDegree_mul_sq ψ a
  let L := valuationBallSubgroup t
  have hLc : IsCompact (L : Set F) := by
    rw [coe_valuationBallSubgroup]; exact isCompact_valuationBall t
  have hLo : IsOpen (L : Set F) := by
    rw [coe_valuationBallSubgroup]; exact isOpen_valuationBall t
  have hL1 : ∀ x ∈ L, ψ.complex (a * x ^ 2) = 1 := by
    intro x hx
    have hx' : valuation F x ≤ valuation F (t : F) := (mem_valuationBall_iff t x).1 hx
    rw [UnitaryAdditiveCharacter.complex_apply, hc.1 _ ?_, Circle.coe_one]
    rw [map_mul, map_pow, ht]
    exact mul_le_mul_right (pow_le_pow_left₀ zero_le hx' 2) _
  have hLL : hf.isSelfDualBicharacter.annihilator (L : Set F) = L := by
    ext z
    have := congrArg (z ∈ ·) (annihilator_valuationBall ψ hc a t)
    simp only [eq_iff_iff] at this
    rw [← SetLike.mem_coe, coe_valuationBallSubgroup, this, ← SetLike.mem_coe,
      coe_valuationBallSubgroup, mem_valuationBall_iff, mem_valuationBall_iff]
    have hv : valuation F (((Units.mk0 (2 : F) two_ne_zero * a * t)⁻¹ * c : Fˣ) : F) =
        valuation F (t : F) := by
      have hat : valuation F ((a : F) * t) ≠ 0 := by simp
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, map_mul, map_inv₀,
        h2, ht]
      field_simp
    rw [hv]
  rw [weilIndexOne_scale]
  exact weilIndex_eq_one hf hLc hLo hL1 hLL

/-- **GKT Proposition 3.24**, second part: an unramified `ψ` (conductor `O`, `c = 1`) has `γ(ψ) = 1`
when the residue characteristic is odd. -/
theorem weilIndexOne_eq_one_of_isConductor_one (h2 : valuation F (2 : F) = 1)
    (hc : ψ.IsConductor 1) : weilIndexOne ψ = 1 := by
  have h := weilIndexOne_scale_eq_one ψ h2 hc 1 1 (by simp)
  rwa [UnitaryAdditiveCharacter.scale_one] at h

/-- **GKT Proposition 3.25** for a diagonal form `∑ aᵢ xᵢ²`: if `v(2) = 1`, `ψ` has conductor `c`
and `v(c) / v(aᵢ)` is a square of the value group for every `i`, then `γ(ψ ∘ q) = 1`. -/
theorem weilIndex_diagonal_eq_one (h2 : valuation F (2 : F) = 1) {c : Fˣ}
    (hc : ψ.IsConductor c) {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → Fˣ)
    (ht : ∀ i, ∃ t : Fˣ, valuation F (c : F) = valuation F (a i : F) * valuation F (t : F) ^ 2) :
    weilIndex (fun x : ι → F => ψ.complex (∑ i, (a i : F) * x i ^ 2)) = 1 := by
  rw [weilIndex_diagonal]
  refine Finset.prod_eq_one fun i _ => ?_
  obtain ⟨t, hti⟩ := ht i
  exact weilIndexOne_scale_eq_one ψ h2 hc (a i) t hti

/-- **GKT Proposition 3.25**: a quadratic space isometric to `∑ aᵢ xᵢ²` with `v(c) / v(aᵢ)` squares
of the value group has Weil index one (`v(2) = 1`, `ψ` of conductor `c`). -/
theorem weilIndex_eq_one_of_isometryEquiv (h2 : valuation F (2 : F) = 1) {c : Fˣ}
    (hc : ψ.IsConductor c) {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [TopologicalSpace V] [IsModuleTopology F V] (q : QuadraticForm F V)
    (hq : (QuadraticMap.polarBilin q).SeparatingLeft) {n : Type} [Fintype n] [DecidableEq n]
    (a : n → Fˣ) (e : q.IsometryEquiv (QuadraticMap.weightedSumSquares F a))
    (ht : ∀ i, ∃ t : Fˣ, valuation F (c : F) = valuation F (a i : F) * valuation F (t : F) ^ 2) :
    weilIndex (fun x => ψ.complex (q x)) = 1 := by
  rw [← weilIndex_quadraticForm_isometryEquiv ψ e.symm hq, ← weilIndex_diagonal_eq_one ψ h2 hc a ht]
  congr 1
  funext x
  rw [QuadraticMap.weightedSumSquares_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Units.smul_def, smul_eq_mul, sq]

/-- **GKT Corollary 3.26**: if the residue characteristic is odd, `ψ` is unramified (conductor `O`)
and the `aᵢ` are units of `O`, then `γ(ψ ∘ ∑ aᵢ xᵢ²) = 1`. -/
theorem weilIndex_eq_one_of_isConductor_one (h2 : valuation F (2 : F) = 1)
    (hc : ψ.IsConductor 1) {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → Fˣ)
    (ha : ∀ i, valuation F (a i : F) = 1) :
    weilIndex (fun x : ι → F => ψ.complex (∑ i, (a i : F) * x i ^ 2)) = 1 :=
  weilIndex_diagonal_eq_one ψ h2 hc a fun i => ⟨1, by simp [ha i]⟩

end Theta

end Langlands

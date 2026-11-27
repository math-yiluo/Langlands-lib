import Langlands.Correspondence.Laumon.EndRingSimplePoints

/-!
# Stage rings of the end ring

For `b ∈ endRing k`, the *stage ring* `stage k b` is the subring of the fractions `p(b) / q(b)`
with `p, q ∈ k[x][Y]` and `q(b)` a unit: the image of the localization of `k[x][Y]` at the kernel
of `p ↦ p(b) mod t`. For a simple point `b` this ring contains every element of `endRing k` lying
in `k(t)(b)` (`mem_stage_of_mem_adjoin`), and any two elements of `endRing k` lie in a common
stage ring of a simple point (`exists_isSimplePoint_mem_stage`).
-/

noncomputable section

universe u

open Polynomial IsLocalRing

namespace Langlands.Henniart.Laumon

variable (k : Type u) [Field k]

local notation "ι" => endChartCoordinate k FourierEnd.zero
local notation "τ" => endUniformizer k FourierEnd.zero

/-- The residue of `p(b)`, for `p ∈ k[x][Y]`. -/
def stageResidue (b : endRing k) : k[X][X] →+* k :=
  (endResidue k).comp (eval₂RingHom ι b)

/-- The prime ideal of the polynomials `p ∈ k[x][Y]` with `p(b) ≡ 0 (mod t)`. -/
def stagePrime (b : endRing k) : Ideal k[X][X] :=
  RingHom.ker (stageResidue k b)

instance stagePrime_isPrime (b : endRing k) : (stagePrime k b).IsPrime :=
  RingHom.ker_isPrime _

/-- The localization of `k[x][Y]` at `stagePrime k b`. -/
abbrev StageLocalization (b : endRing k) := Localization.AtPrime (stagePrime k b)

theorem isUnit_eval₂_of_mem_primeCompl (b : endRing k) (q : (stagePrime k b).primeCompl) :
    IsUnit (eval₂RingHom ι b (q : k[X][X])) := by
  rw [isUnit_iff_endResidue_ne_zero]
  exact q.2

/-- The evaluation `p / q ↦ p(b) / q(b)` of the localization in the end ring. -/
def stageMap (b : endRing k) : StageLocalization k b →+* endRing k :=
  IsLocalization.lift (isUnit_eval₂_of_mem_primeCompl k b)

/-- The stage ring of `b`: the fractions `p(b) / q(b)` with `q(b)` a unit. -/
def stage (b : endRing k) : Subring (endRing k) :=
  @RingHom.range (StageLocalization k b) (endRing k) _ _ (stageMap k b)

theorem mem_stage_iff (b x : endRing k) : x ∈ stage k b ↔ ∃ z, stageMap k b z = x :=
  Iff.rfl

theorem stageMap_algebraMap (b : endRing k) (p : k[X][X]) :
    stageMap k b (algebraMap k[X][X] (StageLocalization k b) p) = eval₂ ι b p :=
  IsLocalization.lift_eq _ _

theorem eval₂_mem_stage (b : endRing k) (p : k[X][X]) : eval₂ ι b p ∈ stage k b :=
  (mem_stage_iff k b _).2 ⟨_, stageMap_algebraMap k b p⟩

theorem endChartCoordinate_mem_stage (b : endRing k) (a : k[X]) : ι a ∈ stage k b := by
  simpa using eval₂_mem_stage k b (C a)

theorem self_mem_stage (b : endRing k) : b ∈ stage k b := by
  simpa using eval₂_mem_stage k b X

/-- The localization onto the stage ring. -/
def stageProj (b : endRing k) : StageLocalization k b →+* stage k b :=
  (stageMap k b).codRestrict (stage k b) fun z => (mem_stage_iff k b _).2 ⟨z, rfl⟩

theorem coe_stageProj (b : endRing k) (z : StageLocalization k b) :
    ((stageProj k b z : stage k b) : endRing k) = stageMap k b z := rfl

theorem stageProj_surjective (b : endRing k) : Function.Surjective (stageProj k b) := by
  rintro ⟨s, hs⟩
  obtain ⟨z, rfl⟩ := (mem_stage_iff k b _).1 hs
  exact ⟨z, rfl⟩

theorem stageProj_algebraMap (b : endRing k) (p : k[X][X]) :
    stageProj k b (algebraMap k[X][X] (StageLocalization k b) p) =
      ⟨eval₂ ι b p, eval₂_mem_stage k b p⟩ :=
  Subtype.ext (stageMap_algebraMap k b p)

/-- Elements of the localization whose image is a unit of the end ring are units. -/
theorem isUnit_of_isUnit_stageMap (b : endRing k) (z : StageLocalization k b)
    (hz : IsUnit (stageMap k b z)) : IsUnit z := by
  obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective (stagePrime k b).primeCompl z
  have hspec := (IsLocalization.lift_mk'_spec (isUnit_eval₂_of_mem_primeCompl k b) p
    (stageMap k b (IsLocalization.mk' _ p q)) q).1 rfl
  have hp : IsUnit (eval₂RingHom ι b p) := by
    rw [hspec]
    exact (isUnit_eval₂_of_mem_primeCompl k b q).mul hz
  have hp' : p ∈ (stagePrime k b).primeCompl := by
    change stageResidue k b p ≠ 0
    rw [stageResidue, RingHom.comp_apply, ← isUnit_iff_endResidue_ne_zero]
    exact hp
  exact isUnit_iff_exists_inv.2 ⟨_, IsLocalization.mk'_mul_mk'_eq_one (M :=
    (stagePrime k b).primeCompl) ⟨p, hp'⟩ q⟩

/-- **Division in a stage ring.** If `s` is an element of the stage ring which is a unit of the
end ring and `x s` lies in the stage ring, then so does `x`. -/
theorem mem_stage_of_mul_mem (b x s : endRing k) (hs : s ∈ stage k b) (hsu : IsUnit s)
    (hxs : x * s ∈ stage k b) : x ∈ stage k b := by
  obtain ⟨z, rfl⟩ := (mem_stage_iff k b _).1 hs
  obtain ⟨w, hw⟩ := (mem_stage_iff k b _).1 hxs
  obtain ⟨u, hu⟩ := isUnit_of_isUnit_stageMap k b z hsu
  refine (mem_stage_iff k b _).2 ⟨w * ↑u⁻¹, ?_⟩
  rw [map_mul, hw, mul_assoc, ← map_mul, ← hu, Units.mul_inv, map_one, mul_one]

/-- A subring containing the coordinate and an element `c` contains every polynomial expression
in `c` over `k[x]`. -/
theorem eval₂_mem_of_mem (S : Subring (endRing k)) (hS : ∀ a : k[X], ι a ∈ S) {c : endRing k}
    (hc : c ∈ S) (p : k[X][X]) : eval₂ ι c p ∈ S := by
  induction p using Polynomial.induction_on with
  | C a => rw [eval₂_C]; exact hS a
  | add p q hp hq => rw [eval₂_add]; exact add_mem hp hq
  | monomial n a _ =>
    rw [eval₂_mul, eval₂_C, eval₂_X_pow]
    exact mul_mem (hS a) (pow_mem hc _)

/-- Stage rings increase: if `b ∈ stage k b'`, then `stage k b ≤ stage k b'`. -/
theorem stage_le_stage {b b' : endRing k} (h : b ∈ stage k b') : stage k b ≤ stage k b' := by
  intro x hx
  obtain ⟨z, rfl⟩ := (mem_stage_iff k b _).1 hx
  obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective (stagePrime k b).primeCompl z
  have hspec := (IsLocalization.lift_mk'_spec (isUnit_eval₂_of_mem_primeCompl k b) p
    (stageMap k b (IsLocalization.mk' _ p q)) q).1 rfl
  refine mem_stage_of_mul_mem k b' _ (eval₂RingHom ι b (q : k[X][X]))
    (eval₂_mem_of_mem k _ (endChartCoordinate_mem_stage k b') h _)
    (isUnit_eval₂_of_mem_primeCompl k b q) ?_
  rw [mul_comm, ← hspec]
  exact eval₂_mem_of_mem k _ (endChartCoordinate_mem_stage k b') h _

theorem endResidue_sub_endChartCoordinate_C (b : endRing k) :
    endResidue k (b - ι (C (endResidue k b))) = 0 := by
  rw [RingHom.map_sub, endResidue_endChartCoordinate, coeff_C_zero, sub_self]

/-- Splitting off the value at the residue: `p(b) = (p(c))(t) + (b - c) q(b)` with `c` the residue
of `b`, and the residue of `p(c)` is that of `p(b)`. -/
theorem exists_eval₂_eq (b : endRing k) (p : k[X][X]) :
    ∃ (a : k[X]) (q : k[X][X]), eval₂ ι b p = ι a + (b - ι (C (endResidue k b))) * eval₂ ι b q ∧
      a.coeff 0 = endResidue k (eval₂ ι b p) ∧
      eval₂ ι b (derivative p) = eval₂ ι b q +
        (b - ι (C (endResidue k b))) * eval₂ ι b (derivative q) := by
  set c := C (endResidue k b) with hc
  refine ⟨p.eval c, p /ₘ (X - C c), ?_, ?_, ?_⟩
  · conv_lhs => rw [← modByMonic_add_div p (X - C c), modByMonic_X_sub_C_eq_C_eval]
    rw [eval₂_add, eval₂_mul, eval₂_C, eval₂_sub, eval₂_X, eval₂_C]
  · have h : eval₂ ι b p = ι (p.eval c) + (b - ι c) * eval₂ ι b (p /ₘ (X - C c)) := by
      conv_lhs => rw [← modByMonic_add_div p (X - C c), modByMonic_X_sub_C_eq_C_eval]
      rw [eval₂_add, eval₂_mul, eval₂_C, eval₂_sub, eval₂_X, eval₂_C]
    rw [h, RingHom.map_add, RingHom.map_mul, hc, endResidue_sub_endChartCoordinate_C, zero_mul,
      add_zero, endResidue_endChartCoordinate]
  · conv_lhs => rw [← modByMonic_add_div p (X - C c), modByMonic_X_sub_C_eq_C_eval]
    rw [derivative_add, derivative_C, zero_add, derivative_mul, derivative_sub, derivative_X,
      derivative_C, sub_zero, one_mul, eval₂_add, eval₂_mul, eval₂_sub, eval₂_X, eval₂_C]

/-- For a simple point `b` with residue `c`, the element `b - c` is `t` times an element of the
stage ring of `b`. -/
theorem exists_sub_eq_endUniformizer_mul {b : endRing k} (hb : IsSimplePoint k b) :
    ∃ u ∈ stage k b, b - ι (C (endResidue k b)) = τ * u := by
  obtain ⟨G, hG0, hG1⟩ := hb
  obtain ⟨a, q, hGa, ha, hGd⟩ := exists_eval₂_eq k b G
  have hqu : IsUnit (eval₂ ι b q) := by
    rw [isUnit_iff_endResidue_ne_zero] at hG1 ⊢
    rwa [hGd, RingHom.map_add, RingHom.map_mul, endResidue_sub_endChartCoordinate_C, zero_mul,
      add_zero] at hG1
  rw [hG0, RingHom.map_zero] at ha
  obtain ⟨a', rfl⟩ : X ∣ a := Polynomial.X_dvd_iff.2 ha
  have hιX : ι X = τ := eval₂_X _ _
  rw [map_mul, hιX] at hGa
  refine ⟨-ι a' * ↑hqu.unit⁻¹, ?_, ?_⟩
  · refine mem_stage_of_mul_mem k b _ _ (eval₂_mem_stage k b q) hqu ?_
    rw [mul_assoc, IsUnit.val_inv_mul, mul_one]
    exact neg_mem (endChartCoordinate_mem_stage k b a')
  · have h : (b - ι (C (endResidue k b))) * eval₂ ι b q =
        τ * (-ι a' * ↑hqu.unit⁻¹) * eval₂ ι b q := by
      rw [mul_assoc, mul_assoc, IsUnit.val_inv_mul, mul_one]
      linear_combination hG0 - hGa
    exact mul_right_cancel₀ hqu.ne_zero h

/-- **Division by `t` in a stage ring.** For a simple point `b`, if `t y` lies in the stage ring of
`b`, then so does `y`. -/
theorem mem_stage_of_endUniformizer_mul_mem {b : endRing k} (hb : IsSimplePoint k b)
    (y : endRing k) (h : τ * y ∈ stage k b) : y ∈ stage k b := by
  obtain ⟨u, hu, hbu⟩ := exists_sub_eq_endUniformizer_mul k hb
  obtain ⟨z, hz⟩ := (mem_stage_iff k b _).1 h
  obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective (stagePrime k b).primeCompl z
  have hspec := (IsLocalization.lift_mk'_spec (isUnit_eval₂_of_mem_primeCompl k b) p
    (τ * y) q).1 hz
  -- `hspec : p(b) = q(b) * (t y)`
  obtain ⟨a, p₂, hpa, ha, -⟩ := exists_eval₂_eq k b p
  have hres : endResidue k (eval₂ ι b p) = 0 := by
    change endResidue k (eval₂RingHom ι b p) = 0
    rw [hspec, RingHom.map_mul, RingHom.map_mul, endResidue_endUniformizer, zero_mul, mul_zero]
  rw [hres] at ha
  obtain ⟨a', rfl⟩ : X ∣ a := Polynomial.X_dvd_iff.2 ha
  have hιX : ι X = τ := eval₂_X _ _
  rw [map_mul, hιX, hbu] at hpa
  have hy : y * eval₂ ι b q = ι a' + u * eval₂ ι b p₂ := by
    apply mul_left_cancel₀ (endUniformizer_ne_zero k .zero)
    change τ * (y * eval₂RingHom ι b q) = _
    rw [← mul_assoc, mul_comm (τ * y), ← hspec]
    change eval₂ ι b p = _
    rw [hpa]
    ring
  refine mem_stage_of_mul_mem k b y _ (eval₂_mem_stage k b q)
    (isUnit_eval₂_of_mem_primeCompl k b q) ?_
  rw [hy]
  exact add_mem (endChartCoordinate_mem_stage k b a') (mul_mem hu (eval₂_mem_stage k b p₂))

theorem mem_stage_of_endUniformizer_pow_mul_mem {b : endRing k} (hb : IsSimplePoint k b)
    (n : ℕ) (y : endRing k) (h : τ ^ n * y ∈ stage k b) : y ∈ stage k b := by
  induction n generalizing y with
  | zero => simpa using h
  | succ n ih =>
    refine ih y (mem_stage_of_endUniformizer_mul_mem k hb _ ?_)
    rwa [← mul_assoc, ← pow_succ']

/-- **Elements of `k(t)(b)` lie in the stage ring of a simple point `b`.** -/
theorem mem_stage_of_mem_adjoin {b : endRing k} (hb : IsSimplePoint k b) (x : endRing k)
    (hx : (x : endField k) ∈ IntermediateField.adjoin (RatFunc k) {(b : endField k)}) :
    x ∈ stage k b := by
  classical
  obtain ⟨G, hG0, hG1⟩ := hb
  have hG : G ≠ 0 := by
    rintro rfl
    simp at hG1
  have halg : IsAlgebraic (RatFunc k) (b : endField k) := by
    refine ⟨G.map (algebraMap k[X] (RatFunc k)),
      (Polynomial.map_ne_zero_iff (IsFractionRing.injective k[X] (RatFunc k))).2 hG, ?_⟩
    rw [← coe_eval₂_endChartCoordinate, hG0]
    rfl
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg,
    Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨P, hP⟩ := hx
  obtain ⟨d, hd, hdP⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors k[X]) P
  set N := IsLocalization.integerNormalization (nonZeroDivisors k[X]) P
  have hN : eval₂ ι b N = ι d * x := by
    apply Subtype.ext
    rw [coe_eval₂_endChartCoordinate, hdP, Algebra.smul_def, map_mul, Polynomial.algebraMap_apply,
      aeval_C]
    change _ = ((ι d : endRing k) : endField k) * (x : endField k)
    rw [coe_endChartCoordinate]
    congr 1
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨d', hdd, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd d hd0 0
  rw [map_zero, sub_zero] at hdd hnd
  have hd'u : IsUnit (ι d') := by
    rw [isUnit_iff_endResidue_ne_zero, endResidue_endChartCoordinate]
    exact fun h => hnd (Polynomial.X_dvd_iff.2 h)
  have hιX : ι X = τ := eval₂_X _ _
  rw [hdd, map_mul, map_pow, hιX, mul_assoc] at hN
  have h1 : ι d' * x ∈ stage k b :=
    mem_stage_of_endUniformizer_pow_mul_mem k ⟨G, hG0, hG1⟩ _ _ (hN ▸ eval₂_mem_stage k b N)
  refine mem_stage_of_mul_mem k b x _ (endChartCoordinate_mem_stage k b d') hd'u ?_
  rwa [mul_comm]

theorem infinite_ratFunc : Infinite (RatFunc k) :=
  Infinite.of_injective _ (IsFractionRing.injective k[X] (RatFunc k))

theorem isSeparable_endField : Algebra.IsSeparable (RatFunc k) (endField k) :=
  separableClosure.isSeparable _ _

/-- **Common stage rings.** Any two elements of the end ring lie in the stage ring of a common
simple point. -/
theorem exists_isSimplePoint_mem_stage (x₁ x₂ : endRing k) :
    ∃ b : endRing k, IsSimplePoint k b ∧ x₁ ∈ stage k b ∧ x₂ ∈ stage k b := by
  have := infinite_ratFunc k
  have := isSeparable_endField k
  obtain ⟨γ, hγ⟩ := Field.primitive_element_inf_aux (RatFunc k) (x₁ : endField k)
    (x₂ : endField k)
  obtain ⟨M, hM⟩ := exists_pow_mul_mem_endRing k γ
  obtain ⟨b, hb, hγb⟩ := exists_isSimplePoint k ⟨_, hM⟩
    (Algebra.IsSeparable.isSeparable (RatFunc k) _)
  have hτ0 : ((τ : endRing k) : endField k) ≠ 0 := by
    exact_mod_cast endUniformizer_ne_zero k .zero
  have hle : IntermediateField.adjoin (RatFunc k) {(x₁ : endField k), (x₂ : endField k)} ≤
      IntermediateField.adjoin (RatFunc k) {(b : endField k)} := by
    rw [hγ, IntermediateField.adjoin_simple_le_iff]
    have hγ' : γ = (((τ : endRing k) : endField k) ^ M)⁻¹ *
        (((τ : endRing k) : endField k) ^ M * γ) := by
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hτ0), one_mul]
    rw [hγ']
    refine mul_mem (inv_mem (pow_mem ?_ _)) hγb
    rw [coe_endUniformizer]
    exact IntermediateField.algebraMap_mem _ _
  refine ⟨b, hb, mem_stage_of_mem_adjoin k hb _ (hle ?_),
    mem_stage_of_mem_adjoin k hb _ (hle ?_)⟩
  · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)

end Langlands.Henniart.Laumon

import Langlands.Global.PrimitiveAdelicBounded
import Langlands.Global.PrincipalAdelesDiscreteProof
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.Pi

/-! # Rational minima of primitive adelic heights -/

noncomputable section

universe u

open scoped NNReal Topology Matrix

namespace Langlands.Global.PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The actual height of a rational vector after applying an adelic matrix. -/
def rationalHeight (g : AdelicGL F n) (v : Fin n → F) : ℝ :=
  height F n (g.val *ᵥ rational F n v)

theorem rational_injective : Function.Injective (rational F n) := by
  intro v w h
  funext i
  exact NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers F) F
    (congrFun h i)

@[simp] theorem rational_zero : rational F n 0 = 0 := by
  ext i
  exact map_zero (diagonal F)

theorem finite_inter_rational_range (B : Set (Vector F n)) (hB : IsCompact B) :
    (B ∩ Set.range (rational F n)).Finite := by
  have := adeles_t2Space F
  have := principalAdeles_discreteTopology F
  have hD : IsDiscrete (principalAdeles F : Set (Adeles F)) := ⟨inferInstance⟩
  have hcoord (i : Fin n) :
      (((fun x : Vector F n => x i) '' B) ∩
        (principalAdeles F : Set (Adeles F))).Finite :=
    ((hB.image (continuous_apply i)).inter_right (principalAdeles_isClosed F)).finite
      (hD.mono Set.inter_subset_right)
  apply (Set.Finite.pi' hcoord).subset
  rintro x ⟨hx, v, rfl⟩ i
  exact ⟨⟨rational F n v, hx, rfl⟩, ⟨v i, rfl⟩⟩

theorem continuous_mulVec (g : AdelicGL F n) :
    Continuous (fun x : Vector F n => g.val *ᵥ x) := by
  apply continuous_pi
  intro i
  change Continuous (fun x : Vector F n => ∑ j : Fin n, g i j * x j)
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

theorem finite_matrix_preimage_rational (g : AdelicGL F n)
    (B : Set (Vector F n)) (hB : IsCompact B) :
    {v : Fin n → F | g.val *ᵥ rational F n v ∈ B}.Finite := by
  have hfin := finite_inter_rational_range F n
    ((fun x : Vector F n => (g⁻¹).val *ᵥ x) '' B)
    (hB.image (continuous_mulVec F n g⁻¹))
  apply (hfin.preimage (rational_injective F n).injOn).subset
  intro v hv
  refine ⟨⟨g.val *ᵥ rational F n v, hv, ?_⟩, ⟨v, rfl⟩⟩
  change (g⁻¹).val *ᵥ (g.val *ᵥ rational F n v) = rational F n v
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec]

theorem rational_smul (a : Fˣ) (v : Fin n → F) :
    rational F n ((a : F) • v) = (diagonalUnits F a).val • rational F n v := by
  ext i
  exact map_mul (diagonal F) (a : F) (v i)

theorem mulVec_rational_smul (g : AdelicGL F n) (a : Fˣ) (v : Fin n → F) :
    g.val *ᵥ rational F n ((a : F) • v) =
      (diagonalUnits F a).val • (g.val *ᵥ rational F n v) := by
  rw [rational_smul, Matrix.mulVec_smul]

theorem rationalHeight_smul (g : AdelicGL F n) (a : Fˣ) (v : Fin n → F)
    (hv : v ≠ 0) :
    rationalHeight F n g ((a : F) • v) = rationalHeight F n g v := by
  have hx : IsPrimitive F n (g.val *ᵥ rational F n v) := ⟨g, v, hv, rfl⟩
  exact (congrArg (height F n) (mulVec_rational_smul F n g a v)).trans
    (hx.height_diagonal_smul F n a)

/-- For a fixed adelic matrix there are only finitely many height values of
nonzero rational vectors below any prescribed real bound. -/
theorem finite_rationalHeight_le (g : AdelicGL F n) (R : ℝ) :
    (rationalHeight F n g ''
      {v : Fin n → F | v ≠ 0 ∧ rationalHeight F n g v ≤ R}).Finite := by
  obtain ⟨B, hB, hcover⟩ := exists_isCompact_bounded_representatives F n R
  have hfin := finite_matrix_preimage_rational F n g B hB
  apply (hfin.image (rationalHeight F n g)).subset
  rintro h ⟨v, ⟨hv, hR⟩, rfl⟩
  have hx : IsPrimitive F n (g.val *ᵥ rational F n v) := ⟨g, v, hv, rfl⟩
  obtain ⟨a, ha⟩ := hcover _ hx hR
  refine ⟨(a : F) • v, ?_, rationalHeight_smul F n g a v hv⟩
  change g.val *ᵥ rational F n ((a : F) • v) ∈ B
  rw [mulVec_rational_smul]
  exact ha

/-- Any nonempty set of nonzero rational vectors has a vector of least height
after a fixed invertible adelic matrix. -/
theorem exists_min_rationalHeight_on (g : AdelicGL F n) (S : Set (Fin n → F))
    (hS : S.Nonempty) (hzero : (0 : Fin n → F) ∉ S) :
    ∃ v ∈ S, ∀ w ∈ S, rationalHeight F n g v ≤ rationalHeight F n g w := by
  obtain ⟨v₀, hv₀⟩ := hS
  let T : Set ℝ := rationalHeight F n g ''
    {v : Fin n → F | v ∈ S ∧ rationalHeight F n g v ≤ rationalHeight F n g v₀}
  have hT : T.Finite := by
    apply (finite_rationalHeight_le F n g (rationalHeight F n g v₀)).subset
    rintro h ⟨v, ⟨hv, hvle⟩, rfl⟩
    exact ⟨v, ⟨fun hz => hzero (hz ▸ hv), hvle⟩, rfl⟩
  have hTne : T.Nonempty := ⟨_, v₀, ⟨hv₀, le_rfl⟩, rfl⟩
  obtain ⟨h, ⟨v, ⟨hv, hvle⟩, rfl⟩, hmin⟩ := Set.exists_min_image T id hT hTne
  refine ⟨v, hv, fun w hw => ?_⟩
  by_cases hle : rationalHeight F n g w ≤ rationalHeight F n g v₀
  · exact hmin _ ⟨w, ⟨hw, hle⟩, rfl⟩
  · exact hvle.trans (le_of_not_ge hle)

/-- A nonzero rational vector attaining the global rational height minimum. -/
theorem exists_min_rationalHeight (g : AdelicGL F n) (hn : 0 < n) :
    ∃ v : Fin n → F, v ≠ 0 ∧
      ∀ w : Fin n → F, w ≠ 0 → rationalHeight F n g v ≤ rationalHeight F n g w := by
  apply exists_min_rationalHeight_on F n g {v | v ≠ 0}
  · refine ⟨fun _ => 1, ?_⟩
    intro h
    exact one_ne_zero (congrFun h ⟨0, hn⟩)
  · exact fun h => h rfl

theorem rationalHeight_pos (g : AdelicGL F n) (v : Fin n → F) (hv : v ≠ 0) :
    0 < rationalHeight F n g v :=
  IsPrimitive.height_pos F n ⟨g, v, hv, rfl⟩

/-- A chosen nonzero rational vector attaining the least height for a fixed
adelic matrix in positive dimension. -/
def minimumRationalVector (g : AdelicGL F n) (hn : 0 < n) : Fin n → F :=
  (exists_min_rationalHeight F n g hn).choose

theorem minimumRationalVector_ne_zero (g : AdelicGL F n) (hn : 0 < n) :
    minimumRationalVector F n g hn ≠ 0 :=
  (exists_min_rationalHeight F n g hn).choose_spec.1

theorem minimumRationalVector_min (g : AdelicGL F n) (hn : 0 < n)
    (v : Fin n → F) (hv : v ≠ 0) :
    rationalHeight F n g (minimumRationalVector F n g hn) ≤ rationalHeight F n g v :=
  (exists_min_rationalHeight F n g hn).choose_spec.2 v hv

/-- The positive rational height minimum of a fixed adelic matrix. -/
def minimumRationalHeight (g : AdelicGL F n) (hn : 0 < n) : ℝ :=
  rationalHeight F n g (minimumRationalVector F n g hn)

theorem minimumRationalHeight_pos (g : AdelicGL F n) (hn : 0 < n) :
    0 < minimumRationalHeight F n g hn :=
  rationalHeight_pos F n g _ (minimumRationalVector_ne_zero F n g hn)

/-- The rational heights of a fixed adelic matrix are bounded below by a
strictly positive constant. -/
theorem exists_pos_le_rationalHeight (g : AdelicGL F n) :
    ∃ c : ℝ, 0 < c ∧
      ∀ v : Fin n → F, v ≠ 0 → c ≤ rationalHeight F n g v := by
  by_cases hn : 0 < n
  · obtain ⟨v, hv, hmin⟩ := exists_min_rationalHeight F n g hn
    exact ⟨rationalHeight F n g v, rationalHeight_pos F n g v hv, hmin⟩
  · refine ⟨1, zero_lt_one, fun v hv => ?_⟩
    exfalso
    apply hv
    funext i
    exact False.elim (hn ((Nat.zero_le i.val).trans_lt i.isLt))

end Langlands.Global.PrimitiveAdelicHeight

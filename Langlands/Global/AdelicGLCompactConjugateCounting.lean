import Langlands.Analysis.DiscreteProductSubgroupCounting
import Langlands.Global.ArchimedeanHilbertGrowthComparison
import Langlands.Global.PrincipalAdelesDiscreteProof

/-! # Counting rational matrices in adelic conjugates of a compact set -/

noncomputable section

universe u

open Set Topology NumberField
open scoped Classical Matrix.Norms.Operator RestrictedProduct

namespace Langlands.Global.AdelicGL

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

private abbrev FiniteMatrix := Matrix (Fin n) (Fin n) (FiniteAdeles F)

private def mixedDiagonal : F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    ((RingHom.fst (InfiniteAdeles F) (FiniteAdeles F)).comp (diagonal F))

private def finiteDiagonal : F →+* FiniteAdeles F :=
  (RingHom.snd (InfiniteAdeles F) (FiniteAdeles F)).comp (diagonal F)

/-- The rational matrix embedded in its mixed archimedean and finite coordinates. -/
private def matrixDiagonal : Matrix (Fin n) (Fin n) F →+
    ArchimedeanMatrix F n × FiniteMatrix F n where
  toFun m := (fun i j => mixedDiagonal F (m i j), fun i j => finiteDiagonal F (m i j))
  map_zero' := by
    apply Prod.ext <;> apply Matrix.ext <;> intro i j
    · exact map_zero (mixedDiagonal F)
    · exact map_zero (finiteDiagonal F)
  map_add' m m' := by
    apply Prod.ext <;> apply Matrix.ext <;> intro i j
    · exact map_add (mixedDiagonal F) (m i j) (m' i j)
    · exact map_add (finiteDiagonal F) (m i j) (m' i j)

private def entryAdele (i j : Fin n) (p : ArchimedeanMatrix F n × FiniteMatrix F n) : Adeles F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i j), p.2 i j)

private theorem continuous_entryAdele (i j : Fin n) : Continuous (entryAdele F n i j) :=
  ((continuous_infiniteAdeleCoordinates_symm F).comp (continuous_fst.matrix_elem i j)).prodMk
    (continuous_snd.matrix_elem i j)

@[simp] private theorem entryAdele_diagonal (i j : Fin n) (m : Matrix (Fin n) (Fin n) F) :
    entryAdele F n i j (matrixDiagonal F n m) = diagonal F (m i j) := by
  change ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
    (InfiniteAdeleRing.ringEquiv_mixedSpace F ((diagonal F (m i j)).1)),
    (diagonal F (m i j)).2) = diagonal F (m i j)
  rw [RingEquiv.symm_apply_apply]
  rfl

private theorem matrixDiagonal_injective : Function.Injective (matrixDiagonal F n) := by
  intro m m' h
  apply Matrix.ext
  intro i j
  apply NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers F) F
  simpa only [entryAdele_diagonal] using congrArg (entryAdele F n i j) h

private theorem discrete_range_matrixDiagonal : DiscreteTopology (matrixDiagonal F n).range := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  let U : Set (ArchimedeanMatrix F n × FiniteMatrix F n) :=
    ⋂ i, ⋂ j, entryAdele F n i j ⁻¹' principalAdelesIsolatingSet F
  have hU : IsOpen U := isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_principalAdelesIsolatingSet F).preimage (continuous_entryAdele F n i j)
  refine isOpen_induced_iff.mpr ⟨U, hU, ?_⟩
  ext ⟨p, hp⟩
  obtain ⟨m, rfl⟩ := AddMonoidHom.mem_range.mp hp
  simp only [mem_preimage, mem_singleton_iff]
  constructor
  · intro h
    apply Subtype.ext
    change matrixDiagonal F n m = _
    suffices m = 0 by simp [this]
    apply Matrix.ext
    intro i j
    have hij := mem_iInter.mp (mem_iInter.mp h i) j
    simp only [mem_preimage, entryAdele_diagonal] at hij
    have he : diagonal F (m i j) ∈ principalAdelesIsolatingSet F ∩ principalAdeles F :=
      ⟨hij, m i j, rfl⟩
    rw [principalAdelesIsolatingSet_inter_principalAdeles] at he
    exact (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers F) F)
      ((mem_singleton_iff.mp he).trans (map_zero _).symm)
  · intro h
    have he : matrixDiagonal F n m = 0 := congrArg Subtype.val h
    rw [he]
    apply mem_iInter.mpr
    intro i
    apply mem_iInter.mpr
    intro j
    have h0 : entryAdele F n i j 0 = 0 := by
      change ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0, 0) = 0
      rw [map_zero]
      rfl
    change entryAdele F n i j 0 ∈ principalAdelesIsolatingSet F
    rw [h0]
    exact zero_mem_principalAdelesIsolatingSet F

private def mixedVal (x : AdelicGL F n) : ArchimedeanMatrix F n :=
  (archimedeanGLCoordinates F n (infinite F n x)).val

private def finiteVal (x : AdelicGL F n) : FiniteMatrix F n := (finite F n x).val

private theorem continuous_mixedVal : Continuous (mixedVal F n) :=
  Units.continuous_val.comp ((archimedeanGLCoordinates F n).continuous.comp (infinite F n).continuous)

private theorem continuous_finiteVal : Continuous (finiteVal F n) :=
  Units.continuous_val.comp (finite F n).continuous

private theorem mixedVal_mul (x y : AdelicGL F n) :
    mixedVal F n (x * y) = mixedVal F n x * mixedVal F n y := by
  simp only [mixedVal, map_mul, Units.val_mul]

private theorem mixedVal_conjugate_norm_le (a : InfiniteAdelicGL F n) (b : FiniteAdelicGL F n)
    (s : AdelicGL F n) :
    ‖mixedVal F n (pair F n a b * s * (pair F n a b)⁻¹)‖ ≤
      ‖mixedVal F n s‖ * ArchimedeanGL.matrixHeight F n a ^ 2 := by
  let x := pair F n a b
  change ‖mixedVal F n (x * s * x⁻¹)‖ ≤ _
  rw [mixedVal_mul, mixedVal_mul]
  have hx : ‖mixedVal F n x‖ ≤ ArchimedeanGL.matrixHeight F n a := by
    simpa [mixedVal, x] using ArchimedeanGL.norm_val_le_matrixHeight F n a
  have hx' : ‖mixedVal F n x⁻¹‖ ≤ ArchimedeanGL.matrixHeight F n a := by
    simpa [mixedVal, x, map_inv] using ArchimedeanGL.norm_inv_le_matrixHeight F n a
  calc
    _ ≤ ‖mixedVal F n x * mixedVal F n s‖ * ‖mixedVal F n x⁻¹‖ := norm_mul_le _ _
    _ ≤ (ArchimedeanGL.matrixHeight F n a * ‖mixedVal F n s‖) *
        ArchimedeanGL.matrixHeight F n a :=
      mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))) hx'
        (norm_nonneg _) (mul_nonneg (ArchimedeanGL.matrixHeight_nonneg F n a) (norm_nonneg _))
    _ = _ := by ring

/-- After fixing the finite component of the conjugating element, the number of rational
points in a compact conjugate is bounded by a polynomial in the archimedean Hilbert norm. -/
def AdelicGLCompactConjugateCountingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ) (S : Set (AdelicGL F n)), IsCompact S →
    ∀ b : FiniteAdelicGL F n, ∃ B : ℝ, 0 ≤ B ∧ ∀ a : InfiniteAdelicGL F n,
      let x := pair F n a b
      let P := (rational F n) ⁻¹' ((fun s => x * s * x⁻¹) '' S)
      P.Finite ∧ (P.ncard : ℝ) ≤ B * infiniteAdelicHilbertNorm F n a ^
        (2 * Module.finrank ℝ (ArchimedeanMatrix F n))

/-- Apply compact-slice packing to the additive diagonal matrix subgroup. -/
theorem adelicGLCompactConjugateCounting : AdelicGLCompactConjugateCountingStatement.{u} := by
  intro F _ _ n S hS b
  let c (s : AdelicGL F n) := ((b * finite F n s * b⁻¹).val : FiniteMatrix F n)
  let C := c '' S
  have hC : IsCompact C := hS.image (Units.continuous_val.comp
    ((continuous_const.mul (finite F n).continuous).mul continuous_const))
  let Γ := (matrixDiagonal F n).range
  let : T2Space (FiniteAdeles F) := inferInstanceAs
    (T2Space (Πʳ v : FinitePlace F, [FiniteCompletion F v, v.adicCompletionIntegers F]))
  obtain ⟨B, hB, hcount⟩ := @Langlands.Analysis.discreteProductSubgroupCounting
    (ArchimedeanMatrix F n) _ _ _ (FiniteMatrix F n) _ _ _ _ Γ
    (discrete_range_matrixDiagonal F n) C hC
  obtain ⟨L, _, hL, _, hcompare⟩ := archimedeanMatrixHilbertComparison F n
  obtain ⟨M, hM⟩ := (hS.image ((continuous_mixedVal F n).norm)).bddAbove
  let D := max 0 M * L ^ 2
  have hD : 0 ≤ D := mul_nonneg (le_max_left _ _) (sq_nonneg _)
  let d := Module.finrank ℝ (ArchimedeanMatrix F n)
  refine ⟨B * (1 + D) ^ d, by positivity, ?_⟩
  intro a
  let x := pair F n a b
  let H := infiniteAdelicHilbertNorm F n a
  have hH : 1 ≤ H := one_le_infiniteAdelicHilbertNorm F n a
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  let R := D * H ^ 2
  have hR : 0 ≤ R := mul_nonneg hD (sq_nonneg _)
  let Q := (Γ : Set (ArchimedeanMatrix F n × FiniteMatrix F n)) ∩
    (Metric.closedBall 0 R ×ˢ C)
  obtain ⟨hQ, hQbound⟩ := hcount R hR
  let P := (rational F n) ⁻¹' ((fun s => x * s * x⁻¹) '' S)
  change P.Finite ∧ (P.ncard : ℝ) ≤ _
  let j (g : RationalGL F n) := matrixDiagonal F n g.val
  have hj : Function.Injective j := fun _ _ h => Units.ext (matrixDiagonal_injective F n h)
  have hPQ : MapsTo j P Q := by
    intro g hg
    obtain ⟨s, hs, h⟩ := hg
    have he : j g = (mixedVal F n (rational F n g), finiteVal F n (rational F n g)) := rfl
    refine ⟨⟨g.val, rfl⟩, ?_⟩
    rw [he, ← h]
    refine ⟨?_, ⟨s, hs, ?_⟩⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hMs : ‖mixedVal F n s‖ ≤ max 0 M :=
        (hM (mem_image_of_mem _ hs)).trans (le_max_right _ _)
      calc
        _ ≤ ‖mixedVal F n s‖ * ArchimedeanGL.matrixHeight F n a ^ 2 :=
          mixedVal_conjugate_norm_le F n a b s
        _ ≤ max 0 M * (L * H) ^ 2 :=
          mul_le_mul hMs (pow_le_pow_left₀ (ArchimedeanGL.matrixHeight_nonneg F n a)
            (hcompare a).1 2) (sq_nonneg _) (le_max_left _ _)
        _ = R := by dsimp [R, D]; ring
    · simp only [finiteVal, c, map_mul, map_inv, x, finite_pair]
  refine ⟨Set.Finite.of_injOn hPQ hj.injOn hQ, ?_⟩
  have hle : 1 + R ≤ (1 + D) * H ^ 2 := by
    have : 1 ≤ H ^ 2 := one_le_pow₀ hH
    dsimp [R]
    rw [add_mul, one_mul]
    exact add_le_add_left this _
  calc
    (P.ncard : ℝ) ≤ Q.ncard := by
      exact_mod_cast Set.ncard_le_ncard_of_injOn j hPQ hj.injOn hQ
    _ ≤ B * (1 + R) ^ d := hQbound
    _ ≤ B * ((1 + D) * H ^ 2) ^ d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hle _) hB
    _ = _ := by rw [mul_pow, ← pow_mul, ← mul_assoc]

end Langlands.Global.AdelicGL

import Langlands.Representation.Hecke.LevelHeckeCornerComparisonStatement

/-! # The normalized linear comparison between the two level Hecke spaces -/

noncomputable section

open MeasureTheory Langlands.Shimura.LevelHecke Classical

namespace Langlands.Hecke

universe u

namespace LevelCorner

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- Evaluation on the underlying actual Hecke test function. -/
def evaluation (x : G) : HeckeAlgebra μ →ₗ[ℂ] ℂ where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The normalized indicator of the coset represented by `q`. -/
def cosetTest (q : G ⧸ K.toSubgroup) : HeckeAlgebra μ :=
  (HeckeAlgebra.toTestFunction μ).symm
    (TestFunction.leftTranslate q.out
      (HeckeAlgebra.toTestFunction μ (HeckeAlgebra.normalizedIndicator μ K hK)))

omit [BorelSpace G] [μ.IsHaarMeasure] in
theorem cosetTest_apply (q : G ⧸ K.toSubgroup) (x : G) :
    cosetTest μ K hK q x =
      if (x : G ⧸ K.toSubgroup) = q then (μ.real (K : Set G) : ℂ)⁻¹ else 0 := by
  classical
  have he : (x : G ⧸ K.toSubgroup) = q ↔ q.out⁻¹ * x ∈ K := by
    constructor
    · intro hx
      exact QuotientGroup.eq.mp ((QuotientGroup.out_eq' q).trans hx.symm)
    · intro hx
      exact (QuotientGroup.eq.mpr hx).symm.trans (QuotientGroup.out_eq' q)
  change (μ.real (K : Set G) : ℂ)⁻¹ *
    (K : Set G).indicator (fun _ => (1 : ℂ)) (q.out⁻¹ * x) = _
  by_cases hx : q.out⁻¹ * x ∈ K <;> simp [he, hx]

/-- Extend a finitely supported coset function using normalized coset indicators. -/
def expansion : (G ⧸ K.toSubgroup →₀ ℂ) →ₗ[ℂ] HeckeAlgebra μ :=
  Finsupp.linearCombination ℂ (cosetTest μ K hK)

theorem expansion_apply (a : G ⧸ K.toSubgroup →₀ ℂ) (x : G) :
    expansion μ K hK a x =
      (μ.real (K : Set G) : ℂ)⁻¹ * a (x : G ⧸ K.toSubgroup) := by
  classical
  change evaluation μ x (expansion μ K hK a) = _
  rw [expansion, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  change (∑ q ∈ a.support, a q * cosetTest μ K hK q x) = _
  simp_rw [cosetTest_apply]
  rw [Finset.sum_eq_single (x : G ⧸ K.toSubgroup)]
  · simp [mul_comm]
  · intro q _ hq
    simp [Ne.symm hq]
  · intro hx
    simp [Finsupp.notMem_support_iff.mp hx]

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
/-- A fixed permutation vector is constant under left multiplication by the subgroup. -/
theorem level_invariant (a : HeckeSpace ℂ K.toSubgroup K.toSubgroup)
    (k : K) (q : G ⧸ K.toSubgroup) :
    a.1 ((k : G) • q) = a.1 q := by
  have h := congrArg (fun f : G ⧸ K.toSubgroup →₀ ℂ => f ((k : G) • q)) (a.property k)
  change Langlands.Induction.permutation ℂ G (G ⧸ K.toSubgroup) ℂ (k : G)
    a.1 ((k : G) • q) = a.1 ((k : G) • q) at h
  rw [Langlands.Induction.permutation_apply, inv_smul_smul] at h
  exact h.symm

theorem expansion_mem (a : LevelHeckeAlgebra ℂ K.toSubgroup) :
    expansion μ K hK a.1 ∈ HeckeAlgebra.biInvariantSubalgebra μ K.toSubgroup := by
  constructor
  · intro k x
    change expansion μ K hK a.1 ((k : G) * x) = expansion μ K hK a.1 x
    rw [expansion_apply, expansion_apply]
    congr 1
    simpa only [MulAction.Quotient.smul_mk, smul_eq_mul] using
      level_invariant K a k (x : G ⧸ K.toSubgroup)
  · intro k x
    change expansion μ K hK a.1 (x * (k : G)) = expansion μ K hK a.1 x
    rw [expansion_apply, expansion_apply]
    congr 1
    congr 1
    apply QuotientGroup.eq.mpr
    simp

/-- The normalized linear map on left-invariant coset functions. -/
def toCorner : LevelHeckeAlgebra ℂ K.toSubgroup →ₗ[ℂ] HeckeAlgebra.Corner μ K hK where
  toFun a := ⟨expansion μ K hK a.1, expansion_mem μ K hK a⟩
  map_add' a b := Subtype.ext (map_add (expansion μ K hK) a.1 b.1)
  map_smul' c a := Subtype.ext (map_smul (expansion μ K hK) c a.1)

theorem toCorner_apply (a : LevelHeckeAlgebra ℂ K.toSubgroup) (x : G) :
    toCorner μ K hK a x =
      (μ.real (K : Set G) : ℂ)⁻¹ * a.1 (x : G ⧸ K.toSubgroup) :=
  expansion_apply μ K hK a.1 x

theorem toCorner_injective : Function.Injective (toCorner μ K hK) := by
  intro a b hab
  apply Subtype.ext
  apply Finsupp.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    have h := congrArg (fun f : HeckeAlgebra.Corner μ K hK => f x) hab
    rw [toCorner_apply, toCorner_apply] at h
    exact mul_left_cancel₀
      (inv_ne_zero (HeckeAlgebra.compactOpen_complex_mass_ne_zero μ K hK)) h

omit [BorelSpace G] [μ.IsHaarMeasure] in
/-- Only finitely many quotient cosets meet the support of a compactly supported test. -/
theorem finite_coset_support (f : HeckeAlgebra μ) :
    Set.Finite {q : G ⧸ K.toSubgroup | f q.out ≠ 0} := by
  classical
  obtain ⟨t, ht⟩ := (TestFunction.isCompact_support (HeckeAlgebra.toTestFunction μ f)
    ).elim_finite_subcover
    (fun i : G => (fun k => i * k) '' (K : Set G))
    (fun i => isOpenMap_mul_left i _ K.isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, 1, K.one_mem, mul_one x⟩)
  apply (t.image (fun x : G => (x : G ⧸ K.toSubgroup))).finite_toSet.subset
  intro q hq
  have hcover := ht hq
  simp only [Set.mem_iUnion] at hcover
  obtain ⟨i, hi, k, hk, he⟩ := hcover
  apply Finset.mem_image.mpr
  refine ⟨i, hi, ?_⟩
  rw [← QuotientGroup.out_eq' q, ← he]
  apply QuotientGroup.eq.mpr
  simpa using K.inv_mem hk

/-- Right invariance recovers a corner function from any chosen coset representative. -/
theorem out_value (f : HeckeAlgebra.Corner μ K hK) (x : G) :
    f (Quotient.out (x : G ⧸ K.toSubgroup)) = f x := by
  let y := Quotient.out (x : G ⧸ K.toSubgroup)
  have hk : x⁻¹ * y ∈ K :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (x : G ⧸ K.toSubgroup)).symm
  simpa only [mul_inv_cancel_left] using
    HeckeAlgebra.Corner.rightInvariant μ K hK f ⟨x⁻¹ * y, hk⟩ x

/-- The finitely supported coefficients of a corner function. -/
def coefficients (f : HeckeAlgebra.Corner μ K hK) : G ⧸ K.toSubgroup →₀ ℂ :=
  Finsupp.ofSupportFinite (fun q => (μ.real (K : Set G) : ℂ) * f q.out)
    ((finite_coset_support μ K (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK f)).subset
      (fun _ h => right_ne_zero_of_mul h))

theorem coefficients_mk (f : HeckeAlgebra.Corner μ K hK) (x : G) :
    coefficients μ K hK f (x : G ⧸ K.toSubgroup) =
      (μ.real (K : Set G) : ℂ) * f x := by
  change (μ.real (K : Set G) : ℂ) * f (Quotient.out (x : G ⧸ K.toSubgroup)) = _
  rw [out_value]

theorem coefficients_fixed (f : HeckeAlgebra.Corner μ K hK) :
    coefficients μ K hK f ∈ fixedVectors (permRep ℂ K.toSubgroup) K.toSubgroup := by
  intro k
  apply Finsupp.ext
  intro q
  change Langlands.Induction.permutation ℂ G (G ⧸ K.toSubgroup) ℂ (k : G)
    (coefficients μ K hK f) q = coefficients μ K hK f q
  rw [Langlands.Induction.permutation_apply]
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, coefficients_mk, coefficients_mk]
    congr 1
    exact HeckeAlgebra.Corner.leftInvariant μ K hK f k⁻¹ x

theorem toCorner_surjective : Function.Surjective (toCorner μ K hK) := by
  intro f
  refine ⟨⟨coefficients μ K hK f, coefficients_fixed μ K hK f⟩, ?_⟩
  apply Subtype.ext
  apply HeckeAlgebra.ext
  intro x
  change expansion μ K hK (coefficients μ K hK f) x = f x
  rw [expansion_apply, coefficients_mk]
  rw [← mul_assoc,
    inv_mul_cancel₀ (HeckeAlgebra.compactOpen_complex_mass_ne_zero μ K hK), one_mul]

/-- The canonical normalized linear equivalence of the two level Hecke spaces. -/
def linearEquiv : LevelHeckeAlgebra ℂ K.toSubgroup ≃ₗ[ℂ] HeckeAlgebra.Corner μ K hK :=
  LinearEquiv.ofBijective (toCorner μ K hK)
    ⟨toCorner_injective μ K hK, toCorner_surjective μ K hK⟩

theorem linearEquiv_apply (a : LevelHeckeAlgebra ℂ K.toSubgroup) (x : G) :
    linearEquiv μ K hK a x =
      (μ.real (K : Set G) : ℂ)⁻¹ * a.1 (x : G ⧸ K.toSubgroup) :=
  toCorner_apply μ K hK a x

end LevelCorner

end Langlands.Hecke

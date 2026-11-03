import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Determinant

/-! # Recovering a split subspace from its exterior line -/

noncomputable section

open Module

namespace Langlands.GroupScheme.Chevalley

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {I : Type*} [Fintype I] [DecidableEq I]
  (b : Basis I R M) {d : ℕ} (s : Fin d ↪ I)

/-- The span of a chosen finite subfamily of a basis. -/
def coordinateSpan : Submodule R M :=
  Submodule.span R (Set.range fun i => b (s i))

/-- Its decomposable exterior vector. -/
def exteriorLineVector : ⋀[R]^d M :=
  exteriorPower.ιMulti R d (fun i => b (s i))

theorem mem_coordinateSpan_iff (x : M) :
    x ∈ coordinateSpan b s ↔ ∀ j : I, j ∉ Set.range s → b.coord j x = 0 := by
  constructor
  · intro hx j hj
    have hle : coordinateSpan b s ≤ LinearMap.ker (b.coord j) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hij : s i ≠ j := fun h => hj ⟨i, h⟩
      simp [Basis.coord_apply, Ne.symm hij]
    exact hle hx
  · intro hx
    rw [← b.sum_repr x]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i ∈ Set.range s
    · obtain ⟨j, rfl⟩ := hi
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · simp [← Basis.coord_apply, hx i hi]

omit [Fintype I] [DecidableEq I] in
/-- Every vector in the selected subspace annihilates its top exterior vector. -/
theorem ι_mul_exteriorLineVector_eq_zero {x : M} (hx : x ∈ coordinateSpan b s) :
    ExteriorAlgebra.ι R x * (exteriorLineVector b s : ExteriorAlgebra R M) = 0 := by
  have hle : coordinateSpan b s ≤ LinearMap.ker
      ((LinearMap.mulRight R (exteriorLineVector b s : ExteriorAlgebra R M)) ∘ₗ
        ExteriorAlgebra.ι R) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ExteriorAlgebra.ι_mul_prod_list (fun j => b (s j)) i
  exact hle hx

omit [Fintype I] in
private theorem paired_cons_det (x : M) (j : I) (hj : j ∉ Set.range s) :
    (Matrix.of fun i k : Fin (d + 1) =>
      ((Fin.cons (b.coord j) (fun l => b.coord (s l)) :
        Fin (d + 1) → Module.Dual R M) k)
        ((Fin.cons x (fun l => b (s l)) : Fin (d + 1) → M) i)).det = b.coord j x := by
  let A : Matrix (Fin (d + 1)) (Fin (d + 1)) R := Matrix.of fun i k =>
    ((Fin.cons (b.coord j) (fun l => b.coord (s l)) :
      Fin (d + 1) → Module.Dual R M) k)
      ((Fin.cons x (fun l => b (s l)) : Fin (d + 1) → M) i)
  have hcol (i : Fin d) : A i.succ 0 = 0 := by
    have hne : s i ≠ j := fun h => hj ⟨i, h⟩
    simp [A, Basis.coord_apply, Ne.symm hne]
  have hminor : A.submatrix Fin.succ Fin.succ = 1 := by
    ext i k
    simp [A, Basis.coord_apply, Finsupp.single_apply, Matrix.one_apply, s.injective.eq_iff]
  change A.det = _
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [hcol, hminor, A]

/-- The annihilator of the decomposable exterior vector is exactly the chosen subspace,
over an arbitrary commutative ring. -/
theorem ι_mul_exteriorLineVector_eq_zero_iff (x : M) :
    ExteriorAlgebra.ι R x * (exteriorLineVector b s : ExteriorAlgebra R M) = 0 ↔
      x ∈ coordinateSpan b s := by
  constructor
  · intro hx
    apply (mem_coordinateSpan_iff b s x).mpr
    intro j hj
    have hz : exteriorPower.ιMulti R (d + 1) (Fin.cons x (fun i => b (s i))) = 0 := by
      apply Subtype.ext
      simpa [exteriorLineVector, Matrix.vecTail] using hx
    have hp := congrArg
      (exteriorPower.alternatingMapToDual R M (d + 1)
        (Fin.cons (b.coord j) (fun i => b.coord (s i)))) hz
    rw [exteriorPower.alternatingMapToDual_apply_ιMulti, map_zero,
      paired_cons_det b s x j hj] at hp
    exact hp
  · exact ι_mul_exteriorLineVector_eq_zero b s

/-- A dual coordinate which takes the value one on the exterior vector. -/
def exteriorLineFunctional : (⋀[R]^d M) →ₗ[R] R :=
  exteriorPower.alternatingMapToDual R M d (fun i => b.coord (s i))

omit [Fintype I] in
@[simp] theorem exteriorLineFunctional_apply :
    exteriorLineFunctional b s (exteriorLineVector b s) = 1 := by
  rw [exteriorLineFunctional, exteriorLineVector,
    exteriorPower.alternatingMapToDual_apply_ιMulti]
  have hm : (Matrix.of fun i j : Fin d => b.coord (s j) (b (s i))) = 1 := by
    ext i j
    simp [Basis.coord_apply, Finsupp.single_apply, Matrix.one_apply, s.injective.eq_iff]
  rw [hm, Matrix.det_one]

private theorem alternatingMap_eq_det_smul
    {U P : Type*} [AddCommGroup U] [Module R U] [AddCommGroup P] [Module R P]
    (c : Basis (Fin d) R U) (f : U [⋀^Fin d]→ₗ[R] P) :
    f = c.det.smulRight (f c) := by
  refine c.ext_alternating fun i hi => ?_
  let σ : Equiv.Perm (Fin d) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
  change f (c ∘ σ) = (c.det.smulRight (f c)) (c ∘ σ)
  simp [AlternatingMap.map_perm, Basis.det_self, AlternatingMap.smulRight]

omit [Fintype I] [DecidableEq I] in
/-- Preserving the coordinate subspace makes its exterior vector an eigenvector. -/
theorem exists_scalar_exteriorLineVector (f : M →ₗ[R] M)
    (hf : ∀ x : M, x ∈ coordinateSpan b s → f x ∈ coordinateSpan b s) :
    ∃ a : R, exteriorPower.map d f (exteriorLineVector b s) =
      a • exteriorLineVector b s := by
  let c : Basis (Fin d) R (coordinateSpan b s) :=
    Basis.span (b.linearIndependent.comp s s.injective)
  let v : Fin d → coordinateSpan b s :=
    fun i => ⟨f (b (s i)), hf _ (Submodule.subset_span ⟨i, rfl⟩)⟩
  let alt := (exteriorPower.ιMulti R d).compLinearMap (coordinateSpan b s).subtype
  refine ⟨c.det v, ?_⟩
  have he := congrArg (fun a : (coordinateSpan b s) [⋀^Fin d]→ₗ[R] (⋀[R]^d M) => a v)
    (alternatingMap_eq_det_smul c alt)
  have hc (i : Fin d) : (c i : M) = b (s i) :=
    Basis.coe_span_apply (b.linearIndependent.comp s s.injective) i
  change exteriorPower.ιMulti R d (fun i => f (b (s i))) =
    c.det v • exteriorPower.ιMulti R d (fun i => (c i : M)) at he
  simp only [hc] at he
  simpa only [exteriorLineVector, exteriorPower.map_apply_ιMulti, Function.comp_def] using he

/-- An invertible linear map preserves a split subspace exactly when it multiplies
its exterior vector by a unit. This includes arbitrary nonreduced coefficient rings. -/
theorem preserves_coordinateSpan_iff (e : M ≃ₗ[R] M) :
    (∀ x : M, x ∈ coordinateSpan b s → e x ∈ coordinateSpan b s) ↔
      ∃ u : Rˣ, exteriorPower.map d e.toLinearMap (exteriorLineVector b s) =
        (u : R) • exteriorLineVector b s := by
  constructor
  · intro he
    obtain ⟨a, ha⟩ := exists_scalar_exteriorLineVector b s e.toLinearMap he
    have hinv : exteriorPower.map d e.symm.toLinearMap
        (exteriorPower.map d e.toLinearMap (exteriorLineVector b s)) =
        exteriorLineVector b s := by
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, LinearEquiv.symm_comp,
        exteriorPower.map_id, LinearMap.id_apply]
    rw [ha, map_smul] at hinv
    have hu : a * exteriorLineFunctional b s
        (exteriorPower.map d e.symm.toLinearMap (exteriorLineVector b s)) = 1 := by
      simpa [map_smul, smul_eq_mul] using congrArg (exteriorLineFunctional b s) hinv
    obtain ⟨u, hu⟩ := (isUnit_iff_exists_inv.mpr ⟨_, hu⟩ : IsUnit a)
    exact ⟨u, hu.symm ▸ ha⟩
  · rintro ⟨u, hu⟩ x hx
    apply (ι_mul_exteriorLineVector_eq_zero_iff b s (e x)).mp
    have hline : ExteriorAlgebra.map e.toLinearMap
        (exteriorLineVector b s : ExteriorAlgebra R M) =
        (u : R) • (exteriorLineVector b s : ExteriorAlgebra R M) := by
      simpa only [exteriorPower.coe_map, Submodule.coe_smul] using congrArg Subtype.val hu
    have hz := congrArg (ExteriorAlgebra.map e.toLinearMap)
      (ι_mul_exteriorLineVector_eq_zero b s hx)
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, hline, map_zero, mul_smul_comm] at hz
    have hh := congrArg (fun y : ExteriorAlgebra R M => ((↑u⁻¹ : R) • y)) hz
    simp only [smul_smul, Units.inv_mul, one_smul, smul_zero] at hh
    exact hh

end Langlands.GroupScheme.Chevalley

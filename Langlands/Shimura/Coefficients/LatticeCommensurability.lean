import Langlands.Shimura.Coefficients.Lattice
import Langlands.AnthropicFLT.P2M.Sol.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite

/-! # Scalar comparisons between full lattices -/

noncomputable section

universe u v w

namespace Langlands.Shimura.Coefficients

set_option autoImplicit false

variable {R : Type u} [CommRing R] [IsDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type w} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/-- Finitely many individually bounded vectors have one nonzero integral bound. -/
theorem exists_nonzero_smul_mem_finset (N : Submodule R V) (s : Finset V)
    (h : ∀ x ∈ s, ∃ r : R, r ≠ 0 ∧ r • x ∈ N) :
    ∃ r : R, r ≠ 0 ∧ ∀ x ∈ s, r • x ∈ N := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨a, ha, hax⟩ := h x (Finset.mem_insert_self x s)
    obtain ⟨b, hb, hbs⟩ := ih (fun y hy => h y (Finset.mem_insert_of_mem hy))
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · simpa only [mul_comm a b, mul_smul] using N.smul_mem b hax
    · simpa only [mul_smul] using N.smul_mem a (hbs y hy)

/-- A finitely generated submodule can be moved into a full lattice by one scalar. -/
theorem exists_nonzero_smul_mem_of_fg (M N : Submodule R V)
    (hM : M.FG) [Submodule.IsLattice K N] :
    ∃ r : R, r ≠ 0 ∧ ∀ x ∈ M, r • x ∈ N := by
  obtain ⟨s, hs⟩ := hM
  have hden : ∀ x ∈ s, ∃ r : R, r ≠ 0 ∧ r • x ∈ N := by
    intro x _
    have hx : x ∈ Submodule.span K (N : Set V) := by
      rw [Submodule.IsLattice.span_eq_top]
      trivial
    obtain ⟨r, hr, hx⟩ :=
      P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.exists_smul_mem_span
        (A := R) (K := K) (N : Set V) hx
    rw [Submodule.span_eq] at hx
    exact ⟨r, hr, hx⟩
  obtain ⟨r, hr, hs'⟩ := exists_nonzero_smul_mem_finset N s hden
  refine ⟨r, hr, ?_⟩
  have hle : M ≤ N.comap (DistribSMul.toLinearMap R V r) := by
    rw [← hs, Submodule.span_le]
    exact hs'
  exact hle

/-- Two full lattices admit the same nonzero scalar bound in both directions. -/
theorem lattices_scalar_commensurable (M N : Submodule R V)
    [Submodule.IsLattice K M] [Submodule.IsLattice K N] :
    ∃ r : R, r ≠ 0 ∧ (∀ x ∈ M, r • x ∈ N) ∧ (∀ x ∈ N, r • x ∈ M) := by
  obtain ⟨a, ha, hMN⟩ :=
    exists_nonzero_smul_mem_of_fg M N Submodule.IsLattice.fg
  obtain ⟨b, hb, hNM⟩ :=
    exists_nonzero_smul_mem_of_fg N M Submodule.IsLattice.fg
  refine ⟨a * b, mul_ne_zero ha hb, ?_, ?_⟩
  · intro x hx
    simpa only [mul_comm a b, mul_smul] using N.smul_mem b (hMN x hx)
  · intro x hx
    simpa only [mul_smul] using M.smul_mem a (hNM x hx)

variable (M N : Submodule R V)
  [Submodule.IsLattice K M] [Submodule.IsLattice K N]

/-- Choose a proved common scalar bound for these two full lattices. -/
def latticeComparisonScalar : R :=
  Classical.choose (lattices_scalar_commensurable M N)

theorem latticeComparisonScalar_ne_zero : latticeComparisonScalar M N ≠ 0 :=
  (Classical.choose_spec (lattices_scalar_commensurable M N)).1

theorem latticeComparisonScalar_forward (x : V) (hx : x ∈ M) :
    latticeComparisonScalar M N • x ∈ N :=
  (Classical.choose_spec (lattices_scalar_commensurable M N)).2.1 x hx

theorem latticeComparisonScalar_backward (x : V) (hx : x ∈ N) :
    latticeComparisonScalar M N • x ∈ M :=
  (Classical.choose_spec (lattices_scalar_commensurable M N)).2.2 x hx

/-- The actual ambient scalar map from the first lattice to the second. -/
def latticeScaledComparison : M →ₗ[R] N :=
  ((DistribSMul.toLinearMap R V (latticeComparisonScalar M N)).comp M.subtype).codRestrict
    N (fun x => latticeComparisonScalar_forward M N x x.2)

/-- The reverse ambient scalar map uses the identical comparison scalar. -/
def latticeScaledComparisonBack : N →ₗ[R] M :=
  ((DistribSMul.toLinearMap R V (latticeComparisonScalar M N)).comp N.subtype).codRestrict
    M (fun x => latticeComparisonScalar_backward M N x x.2)

@[simp] theorem latticeScaledComparison_coe (x : M) :
    (latticeScaledComparison M N x : V) = latticeComparisonScalar M N • (x : V) := rfl

@[simp] theorem latticeScaledComparisonBack_coe (x : N) :
    (latticeScaledComparisonBack M N x : V) =
      latticeComparisonScalar M N • (x : V) := rfl

/-- The composite in the first lattice is multiplication by the square of the scalar. -/
theorem latticeScaledComparison_back_comp :
    (latticeScaledComparisonBack M N).comp (latticeScaledComparison M N) =
      (latticeComparisonScalar M N * latticeComparisonScalar M N) • LinearMap.id := by
  ext x
  exact (mul_smul _ _ (x : V)).symm

/-- The composite in the second lattice is the same scalar square. -/
theorem latticeScaledComparison_comp_back :
    (latticeScaledComparison M N).comp (latticeScaledComparisonBack M N) =
      (latticeComparisonScalar M N * latticeComparisonScalar M N) • LinearMap.id := by
  ext x
  exact (mul_smul _ _ (x : V)).symm

/-- The forward map is injective because its scalar is nonzero in the fraction field. -/
theorem latticeScaledComparison_injective :
    Function.Injective (latticeScaledComparison M N) := by
  intro x y h
  apply Subtype.ext
  have h' := congrArg (fun z : N => (z : V)) h
  change latticeComparisonScalar M N • (x : V) =
    latticeComparisonScalar M N • (y : V) at h'
  have hK : algebraMap R K (latticeComparisonScalar M N) • (x : V) =
      algebraMap R K (latticeComparisonScalar M N) • (y : V) := by
    simpa only [IsScalarTower.algebraMap_smul] using h'
  have hr : algebraMap R K (latticeComparisonScalar M N) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (latticeComparisonScalar_ne_zero M N))
  exact smul_right_injective V hr hK

/-- The reverse map is injective for the same scalar reason. -/
theorem latticeScaledComparisonBack_injective :
    Function.Injective (latticeScaledComparisonBack M N) := by
  intro x y h
  apply Subtype.ext
  have h' := congrArg (fun z : M => (z : V)) h
  change latticeComparisonScalar M N • (x : V) =
    latticeComparisonScalar M N • (y : V) at h'
  have hK : algebraMap R K (latticeComparisonScalar M N) • (x : V) =
      algebraMap R K (latticeComparisonScalar M N) • (y : V) := by
    simpa only [IsScalarTower.algebraMap_smul] using h'
  have hr : algebraMap R K (latticeComparisonScalar M N) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (latticeComparisonScalar_ne_zero M N))
  exact smul_right_injective V hr hK

end Langlands.Shimura.Coefficients

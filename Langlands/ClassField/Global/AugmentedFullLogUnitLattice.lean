import Langlands.ClassField.Global.FullLogConstantSplitting

/-! # Adjoining the integer constant direction to the full logarithmic unit lattice -/

noncomputable section

open NumberField
open scoped Classical

namespace Langlands.ClassField.Global

universe u v

/-- The ordinary integer lattice inside the real scalar direction. -/
def fullLogScalarLattice : Submodule ℤ ℝ :=
  Submodule.span ℤ (Set.range (Module.Basis.singleton Unit ℝ))

instance instDiscreteTopologyFullLogScalarLattice : DiscreteTopology fullLogScalarLattice :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ
    (Set.range (Module.Basis.singleton Unit ℝ))))

instance instIsZLatticeFullLogScalarLattice : IsZLattice ℝ fullLogScalarLattice :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ
    (Set.range (Module.Basis.singleton Unit ℝ))))

theorem mem_fullLogScalarLattice (a : ℝ) :
    a ∈ fullLogScalarLattice ↔ ∃ z : ℤ, (z : ℝ) = a := by
  rw [fullLogScalarLattice]
  have h : Set.range (Module.Basis.singleton Unit ℝ) = {1} := by
    ext a
    simp
  rw [h, Submodule.mem_span_singleton]
  simp [zsmul_eq_mul]

variable (E : Type v) [Field E] [NumberField E]

/-- The unit lattice times the ordinary integer lattice in split coordinates. -/
def fullLogProductLattice : Submodule ℤ (fullLogHyperplane E × ℝ) :=
  (fullLogUnitLattice E).prod fullLogScalarLattice

instance instDiscreteTopologyFullLogProductLattice :
    DiscreteTopology (fullLogProductLattice E) := by
  let f : fullLogProductLattice E → fullLogUnitLattice E × fullLogScalarLattice :=
    fun x => (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  apply DiscreteTopology.of_continuous_injective (f := f)
  · fun_prop
  · intro x y h
    apply Subtype.ext
    exact congrArg (fun z : fullLogUnitLattice E × fullLogScalarLattice =>
      ((z.1 : fullLogHyperplane E), (z.2 : ℝ))) h

instance instIsZLatticeFullLogProductLattice : IsZLattice ℝ (fullLogProductLattice E) where
  span_top := by
    change Submodule.span ℝ
      ((fullLogUnitLattice E : Set (fullLogHyperplane E)) ×ˢ
        (fullLogScalarLattice : Set ℝ)) = ⊤
    rw [Submodule.span_prod_eq ℝ (fullLogUnitLattice E).zero_mem fullLogScalarLattice.zero_mem,
      IsZLattice.span_top, IsZLattice.span_top]
    simp

/-- The full logarithmic unit lattice enlarged by integer constant vectors. -/
def augmentedFullLogUnitLattice : Submodule ℤ (InfinitePlace E → ℝ) :=
  ZLattice.comap ℝ (E := fullLogHyperplane E × ℝ) (F := InfinitePlace E → ℝ)
    (fullLogProductLattice E) (fullLogSplit E).toLinearMap

theorem mem_augmentedFullLogUnitLattice (x : InfinitePlace E → ℝ) :
    x ∈ augmentedFullLogUnitLattice E ↔
      fullLogCentered E x ∈ fullLogUnitLattice E ∧ fullLogMean E x ∈ fullLogScalarLattice :=
  Iff.rfl

instance instDiscreteTopologyAugmentedFullLogUnitLattice :
    DiscreteTopology (augmentedFullLogUnitLattice E) :=
  inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ
    (E := fullLogHyperplane E × ℝ) (F := InfinitePlace E → ℝ)
    (fullLogProductLattice E) (fullLogSplit E).toContinuousLinearEquiv.toLinearMap))

instance instIsZLatticeAugmentedFullLogUnitLattice :
    IsZLattice ℝ (augmentedFullLogUnitLattice E) :=
  inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ
    (E := fullLogHyperplane E × ℝ) (F := InfinitePlace E → ℝ)
    (fullLogProductLattice E) (fullLogSplit E).toContinuousLinearEquiv.toLinearMap))

theorem augmentedFullLogUnitLattice_span :
    Submodule.span ℝ (augmentedFullLogUnitLattice E : Set (InfinitePlace E → ℝ)) = ⊤ :=
  IsZLattice.span_top

/-- Membership is precisely a unit-lattice vector plus an integer constant vector. -/
theorem mem_augmentedFullLogUnitLattice_iff (x : InfinitePlace E → ℝ) :
    x ∈ augmentedFullLogUnitLattice E ↔
      ∃ y : fullLogUnitLattice E, ∃ z : ℤ,
        ((y : fullLogHyperplane E) : InfinitePlace E → ℝ) + fullLogConstant E (z : ℝ) = x := by
  constructor
  · intro hx
    obtain ⟨hy, ha⟩ := (mem_augmentedFullLogUnitLattice E x).mp hx
    obtain ⟨z, hz⟩ := (mem_fullLogScalarLattice _).mp ha
    refine ⟨⟨fullLogCentered E x, hy⟩, z, ?_⟩
    change (fullLogCentered E x : InfinitePlace E → ℝ) + fullLogConstant E (z : ℝ) = x
    rw [hz]
    simp
  · rintro ⟨y, z, rfl⟩
    rw [mem_augmentedFullLogUnitLattice]
    constructor
    · simp
    · simp only [map_add, fullLogMean_hyperplane, fullLogMean_constant, zero_add]
      exact (mem_fullLogScalarLattice _).mpr ⟨z, rfl⟩

variable (F : Type u) [Field F] [Algebra F E]

/-- The enlarged full lattice is stable under the actual arithmetic permutation action. -/
theorem augmentedFullLogUnitLattice_invariant (g : E ≃ₐ[F] E)
    (x : InfinitePlace E → ℝ) (hx : x ∈ augmentedFullLogUnitLattice E) :
    fullLogPermutation F E g x ∈ augmentedFullLogUnitLattice E := by
  obtain ⟨hy, ha⟩ := (mem_augmentedFullLogUnitLattice E x).mp hx
  rw [mem_augmentedFullLogUnitLattice, fullLogCentered_equivariant, fullLogMean_permutation]
  exact ⟨fullLogUnitLattice_invariant F E g _ hy, ha⟩

end Langlands.ClassField.Global

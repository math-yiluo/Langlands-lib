import Langlands.FieldTheory.HenselianSeparableDepthLattice
import Mathlib.RingTheory.Localization.Module

/-! # Integral and rational bases for actual separable depth lattices -/

noncomputable section

universe u v

namespace Langlands.FieldTheory

variable {K : Type u} [Field K]
  (v : Valuation K (WithZero (Multiplicative ℤ)))
  (hH : HenselianLocalRing v.valuationSubring)
  (L : Type v) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
  (hv : Function.Surjective v)

include hv

/-- Inverting the nonzero integral scalars in an actual depth lattice gives
the extension field. -/
theorem henselianSeparableDepthLattice_isLocalizedModule (r : ℝ) :
    IsLocalizedModule (nonZeroDivisors v.valuationSubring)
      (henselianSeparableDepthLattice v hH L r).subtype where
  map_units s :=
    (isLocalizedModule_id (nonZeroDivisors v.valuationSubring) L K).map_units s
  surj x := by
    obtain ⟨a, ha, hax⟩ := henselianSeparableDepthLattice_exists_smul v hH L hv r x
    exact ⟨(⟨a • x, hax⟩, ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩), rfl⟩
  exists_of_eq h := ⟨1, by simpa using Subtype.ext h⟩

variable [FiniteDimensional K L]

/-- An integral basis of the actual depth ball, indexed by the field degree. -/
def henselianSeparableDepthIntegralBasis (r : ℝ) :
    Module.Basis (Fin (Module.finrank K L)) v.valuationSubring
      (henselianSeparableDepthLattice v hH L r) := by
  let := integerValuationSubring_isDiscreteValuationRing v hv
  let := henselianSeparableDepthLattice_finite v hH L hv r
  let := henselianSeparableDepthLattice_isLocalizedModule v hH L hv r
  let b := Module.basisOfFiniteTypeTorsionFree'
    (R := v.valuationSubring) (M := henselianSeparableDepthLattice v hH L r)
  let bK := b.2.ofIsLocalizedModule K (nonZeroDivisors v.valuationSubring)
    (henselianSeparableDepthLattice v hH L r).subtype
  have hn : b.1 = Module.finrank K L := by
    simpa using (Module.finrank_eq_card_basis bK).symm
  exact b.2.reindex (finCongr hn)

/-- The same lattice vectors form a basis of the extension field. -/
def henselianSeparableDepthFieldBasis (r : ℝ) :
    Module.Basis (Fin (Module.finrank K L)) K L := by
  let := henselianSeparableDepthLattice_isLocalizedModule v hH L hv r
  exact (henselianSeparableDepthIntegralBasis v hH L hv r).ofIsLocalizedModule K
    (nonZeroDivisors v.valuationSubring) (henselianSeparableDepthLattice v hH L r).subtype

@[simp]
theorem henselianSeparableDepthFieldBasis_apply (r : ℝ) (i : Fin (Module.finrank K L)) :
    henselianSeparableDepthFieldBasis v hH L hv r i =
      (henselianSeparableDepthIntegralBasis v hH L hv r i : L) := by
  simp [henselianSeparableDepthFieldBasis]

@[simp]
theorem henselianSeparableDepthFieldBasis_repr_coe (r : ℝ)
    (x : henselianSeparableDepthLattice v hH L r) (i : Fin (Module.finrank K L)) :
    (henselianSeparableDepthFieldBasis v hH L hv r).repr (x : L) i =
      ((henselianSeparableDepthIntegralBasis v hH L hv r).repr x i : K) := by
  let := henselianSeparableDepthLattice_isLocalizedModule v hH L hv r
  exact (henselianSeparableDepthIntegralBasis v hH L hv r).ofIsLocalizedModule_repr_apply K
    (nonZeroDivisors v.valuationSubring) (henselianSeparableDepthLattice v hH L r).subtype x i

/-- The integral span of the rational basis is exactly the actual depth ball. -/
theorem henselianSeparableDepthFieldBasis_span (r : ℝ) :
    Submodule.span v.valuationSubring
      (Set.range (henselianSeparableDepthFieldBasis v hH L hv r)) =
        henselianSeparableDepthLattice v hH L r := by
  let := henselianSeparableDepthLattice_isLocalizedModule v hH L hv r
  simpa [henselianSeparableDepthFieldBasis] using
    (henselianSeparableDepthIntegralBasis v hH L hv r).ofIsLocalizedModule_span K
      (nonZeroDivisors v.valuationSubring) (henselianSeparableDepthLattice v hH L r).subtype

/-- Membership in the actual depth ball is equivalent to integrality of every
coordinate in the rationalized lattice basis. -/
theorem henselianSeparableDepthFieldBasis_mem_iff (r : ℝ) (x : L) :
    x ∈ henselianSeparableDepthLattice v hH L r ↔
      ∀ i, (henselianSeparableDepthFieldBasis v hH L hv r).repr x i ∈
        v.valuationSubring := by
  classical
  constructor
  · intro hx i
    rw [henselianSeparableDepthFieldBasis_repr_coe v hH L hv r ⟨x, hx⟩ i]
    exact ((henselianSeparableDepthIntegralBasis v hH L hv r).repr ⟨x, hx⟩ i).property
  · intro hx
    rw [← (henselianSeparableDepthFieldBasis v hH L hv r).sum_repr x]
    apply Submodule.sum_mem
    intro i _
    let a : v.valuationSubring :=
      ⟨(henselianSeparableDepthFieldBasis v hH L hv r).repr x i, hx i⟩
    have hi : henselianSeparableDepthFieldBasis v hH L hv r i ∈
        henselianSeparableDepthLattice v hH L r := by
      rw [henselianSeparableDepthFieldBasis_apply]
      exact (henselianSeparableDepthIntegralBasis v hH L hv r i).property
    simpa [a, ← IsScalarTower.algebraMap_smul K a] using
      (henselianSeparableDepthLattice v hH L r).smul_mem a hi

end Langlands.FieldTheory

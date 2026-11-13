import Langlands.GroupScheme.BoundedSubgroupStableLatticeStatement

/-! # Proof of the stable-lattice step of KP Proposition 2.2.13 -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry ValuativeRel
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {K : Type u} [Field K] [ValuativeRel K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffine G.X.left]
  {n : Type} [Fintype n] [DecidableEq n]

/-- The columns of the original matrices of the elements of `B`, that is, the
`B`-translates of the standard basis vectors. -/
def orbitColumns (ρ : MatrixRepresentation G n) (B : Subgroup (rationalPoints G)) :
    Set (n → K) :=
  {w | ∃ g ∈ B, ∃ k : n, w = (ρ.rationalMatrix g : Matrix n n K) *ᵥ Pi.single k 1}

/-- The span over the valuation integer ring of all `B`-translates of the standard
coordinate lattice. -/
def orbitLattice (ρ : MatrixRepresentation G n) (B : Subgroup (rationalPoints G)) :
    Submodule (ValuativeRel.valuation K).integer (n → K) :=
  Submodule.span (ValuativeRel.valuation K).integer (orbitColumns ρ B)

omit [ValuativeRel K] [IsAffine G.X.left] in
theorem rationalMatrix_mul_coe (ρ : MatrixRepresentation G n) (g h : rationalPoints G) :
    (ρ.rationalMatrix (g * h) : Matrix n n K) =
      (ρ.rationalMatrix g : Matrix n n K) * (ρ.rationalMatrix h : Matrix n n K) := by
  rw [map_mul, Units.val_mul]

omit [ValuativeRel K] [IsAffine G.X.left] in
theorem rationalMatrix_one_coe (ρ : MatrixRepresentation G n) :
    (ρ.rationalMatrix 1 : Matrix n n K) = 1 := by
  rw [map_one, Units.val_one]

omit [IsAffine G.X.left] in
/-- The orbit lattice is preserved by every original matrix of `B`. -/
theorem mulVec_mem_orbitLattice (ρ : MatrixRepresentation G n)
    (B : Subgroup (rationalPoints G)) {g : rationalPoints G} (hg : g ∈ B)
    {v : n → K} (hv : v ∈ ρ.orbitLattice B) :
    (ρ.rationalMatrix g : Matrix n n K) *ᵥ v ∈ ρ.orbitLattice B := by
  let f : (n → K) →ₗ[(ValuativeRel.valuation K).integer] (n → K) :=
    (Matrix.mulVecLin (ρ.rationalMatrix g : Matrix n n K)).restrictScalars _
  have hle : ρ.orbitLattice B ≤ (ρ.orbitLattice B).comap f := by
    refine Submodule.span_le.mpr ?_
    rintro w ⟨h, hh, k, rfl⟩
    refine Submodule.subset_span ⟨g * h, B.mul_mem hg hh, k, ?_⟩
    change (ρ.rationalMatrix g : Matrix n n K) *ᵥ
        ((ρ.rationalMatrix h : Matrix n n K) *ᵥ Pi.single k 1) = _
    rw [Matrix.mulVec_mulVec, rationalMatrix_mul_coe]
  exact hle hv

omit [IsAffine G.X.left] in
/-- The standard basis vectors lie in the orbit lattice (take `g = 1`). -/
theorem single_mem_orbitLattice (ρ : MatrixRepresentation G n)
    (B : Subgroup (rationalPoints G)) (k : n) :
    (Pi.single k 1 : n → K) ∈ ρ.orbitLattice B := by
  refine Submodule.subset_span ⟨1, B.one_mem, k, ?_⟩
  rw [rationalMatrix_one_coe, Matrix.one_mulVec]

omit [IsAffine G.X.left] in
/-- Entry bounds put the orbit lattice inside a finitely generated module. -/
theorem orbitLattice_le_span_of_entries (ρ : MatrixRepresentation G n)
    (B : Subgroup (rationalPoints G)) (b : n → n → K) (hb0 : ∀ i j, b i j ≠ 0)
    (hbB : ∀ i j, ∀ g ∈ B, (ρ.rationalMatrix g : Matrix n n K) i j ≤ᵥ b i j) :
    ρ.orbitLattice B ≤ Submodule.span (ValuativeRel.valuation K).integer
      (Set.range fun p : n × n => b p.1 p.2 • (Pi.single p.1 1 : n → K)) := by
  refine Submodule.span_le.mpr ?_
  rintro w ⟨g, hg, k, rfl⟩
  have hmem (i : n) : (ρ.rationalMatrix g : Matrix n n K) i k / b i k ∈
      (ValuativeRel.valuation K).integer := by
    rw [Valuation.mem_integer_iff, ← (ValuativeRel.valuation K).vle_one_iff,
      div_vle_one_iff (hb0 i k)]
    exact hbB i k g hg
  rw [SetLike.mem_coe, ← Finset.univ_sum_single
    ((ρ.rationalMatrix g : Matrix n n K) *ᵥ Pi.single k 1)]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : (Pi.single i (((ρ.rationalMatrix g : Matrix n n K) *ᵥ Pi.single k 1) i) :
      n → K) =
      (⟨_, hmem i⟩ : (ValuativeRel.valuation K).integer) •
        (b i k • (Pi.single i 1 : n → K)) := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [Subring.smul_def, div_mul_cancel₀ _ (hb0 j k)]
    · simp [hj]
  rw [hi]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, k), rfl⟩)

/-- Over a discrete valuation ring, the orbit lattice of an algebraically bounded
subgroup is a stable full lattice. -/
theorem isStableLatticeFor_orbitLattice
    [IsDiscreteValuationRing (ValuativeRel.valuation K).integer]
    (ρ : MatrixRepresentation G n) (B : Subgroup (rationalPoints G))
    (hB : IsAlgebraicallyBounded K G.X (B : Set (rationalPoints G))) :
    ρ.IsStableLatticeFor B (ρ.orbitLattice B) := by
  choose b hb0 hbB using
    ρ.hasBoundedRationalEntries_of_isAlgebraicallyBounded (B : Set (rationalPoints G)) hB
  refine ⟨⟨?_, ?_⟩, fun g hg v hv => ρ.mulVec_mem_orbitLattice B hg hv⟩
  · exact Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _))
      (ρ.orbitLattice_le_span_of_entries B b hb0 hbB)
  · refine eq_top_iff.mpr ?_
    rw [← (Pi.basisFun K n).span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    rw [Pi.basisFun_apply]
    exact Submodule.subset_span (ρ.single_mem_orbitLattice B k)

end MatrixRepresentation

/-- KP Proposition 2.2.13, stable-lattice step, over a discrete valuation ring. -/
theorem boundedSubgroupStableLattice : BoundedSubgroupStableLatticeStatement.{u} := by
  intro K _ _ _ G _ n ρ B hB
  exact ⟨ρ.orbitLattice B, ρ.isStableLatticeFor_orbitLattice B hB⟩

end Langlands.GroupScheme

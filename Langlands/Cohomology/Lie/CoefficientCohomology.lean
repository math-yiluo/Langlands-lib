import Langlands.Cohomology.Lie.CoefficientSquareZeroProof
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Absolute Lie algebra cohomology with coefficients

Cycles, actual boundaries and their quotient are constructed from the published
Chevalley–Eilenberg differential. Equivariant coefficient maps induce linear
maps on the quotient, preserving identities and composition.
-/

noncomputable section

namespace Langlands.Cohomology.Lie

universe u v w w' w''

variable (K : Type u) (L : Type v) (M : Type w)
variable [Field K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- The kernel of the constructed coefficient differential. -/
def cycles (q : ℕ) : Submodule K (Cochains K L M q) :=
  LinearMap.ker (differential q)

/-- There are no boundaries in degree zero; in successor degree they are the
actual image of the preceding differential. -/
def boundaries : (q : ℕ) → Submodule K (Cochains K L M q)
  | 0 => ⊥
  | n + 1 => LinearMap.range (differential n)

variable {K L M}

@[simp] theorem mem_cycles {q : ℕ} {f : Cochains K L M q} :
    f ∈ cycles K L M q ↔ differential q f = 0 := Iff.rfl

@[simp] theorem boundaries_zero : boundaries K L M 0 = ⊥ := rfl

@[simp] theorem boundaries_succ (q : ℕ) :
    boundaries K L M (q + 1) = LinearMap.range (differential q) := rfl

@[simp] theorem mem_boundaries_zero {f : Cochains K L M 0} :
    f ∈ boundaries K L M 0 ↔ f = 0 := Submodule.mem_bot K

@[simp] theorem mem_boundaries_succ {q : ℕ} {f : Cochains K L M (q + 1)} :
    f ∈ boundaries K L M (q + 1) ↔ ∃ g : Cochains K L M q, differential q g = f :=
  Iff.rfl

variable [CharZero K]

/-- Square-zero proves, rather than assumes, that every boundary is a cycle. -/
theorem boundaries_le_cycles (q : ℕ) : boundaries K L M q ≤ cycles K L M q := by
  cases q with
  | zero => exact bot_le
  | succ n =>
    rintro f ⟨g, rfl⟩
    exact differential_differential n g

variable (K L M)

/-- Boundaries as a submodule of cycles, using the proved inclusion. -/
def boundariesInCycles (q : ℕ) : Submodule K (cycles K L M q) :=
  LinearMap.range (Submodule.inclusion (boundaries_le_cycles (K := K) (L := L) (M := M) q))

/-- The actual absolute coefficient cohomology module in degree `q`. -/
abbrev CoefficientCohomology (q : ℕ) := cycles K L M q ⧸ boundariesInCycles K L M q

/-- Send a cycle to its cohomology class. -/
def cohomologyClass (q : ℕ) : cycles K L M q →ₗ[K] CoefficientCohomology K L M q :=
  (boundariesInCycles K L M q).mkQ

variable {K L M}

@[simp] theorem mem_boundariesInCycles {q : ℕ} {f : cycles K L M q} :
    f ∈ boundariesInCycles K L M q ↔ f.val ∈ boundaries K L M q := by
  constructor
  · rintro ⟨g, rfl⟩
    exact g.property
  · intro hf
    exact ⟨⟨f.val, hf⟩, Subtype.ext rfl⟩

theorem cohomologyClass_surjective (q : ℕ) :
    Function.Surjective (cohomologyClass (K := K) (L := L) (M := M) q) :=
  (boundariesInCycles K L M q).mkQ_surjective

/-- A cycle has zero class exactly when it is an actual boundary. -/
@[simp] theorem cohomologyClass_eq_zero {q : ℕ} (f : cycles K L M q) :
    cohomologyClass K L M q f = 0 ↔ f.val ∈ boundaries K L M q := by
  exact (Submodule.Quotient.mk_eq_zero (boundariesInCycles K L M q)).trans
    mem_boundariesInCycles

/-- Equality of classes means that the difference of the cycles is a boundary. -/
theorem cohomologyClass_eq_iff {q : ℕ} (f g : cycles K L M q) :
    cohomologyClass K L M q f = cohomologyClass K L M q g ↔
      f.val - g.val ∈ boundaries K L M q := by
  exact (Submodule.Quotient.eq (boundariesInCycles K L M q)).trans
    mem_boundariesInCycles

/-- The differential with its codomain restricted to cycles. -/
def coboundaryToCycles (q : ℕ) : Cochains K L M q →ₗ[K] cycles K L M (q + 1) :=
  (differential q).codRestrict (cycles K L M (q + 1))
    (fun f => differential_differential q f)

@[simp] theorem coboundaryToCycles_val (q : ℕ) (f : Cochains K L M q) :
    (coboundaryToCycles q f).val = differential q f := rfl

@[simp] theorem cohomologyClass_coboundary (q : ℕ) (f : Cochains K L M q) :
    cohomologyClass K L M (q + 1) (coboundaryToCycles q f) = 0 := by
  apply (cohomologyClass_eq_zero _).mpr
  exact ⟨f, rfl⟩

section CoefficientMaps

variable {N : Type w'} [AddCommGroup N] [Module K N]
variable [LieRingModule L N] [LieModule K L N]
variable {P : Type w''} [AddCommGroup P] [Module K P]
variable [LieRingModule L P] [LieModule K L P]

/-- Coefficient postcomposition carries cycles to cycles. -/
theorem map_mem_cycles (φ : M →ₗ⁅K,L⁆ N) (q : ℕ) (f : Cochains K L M q)
    (hf : f ∈ cycles K L M q) : map φ q f ∈ cycles K L N q := by
  rw [mem_cycles, ← map_differential, mem_cycles.mp hf, map_zero]

/-- Coefficient postcomposition carries actual boundaries to actual boundaries. -/
theorem map_mem_boundaries (φ : M →ₗ⁅K,L⁆ N) (q : ℕ) (f : Cochains K L M q)
    (hf : f ∈ boundaries K L M q) : map φ q f ∈ boundaries K L N q := by
  cases q with
  | zero =>
    rw [mem_boundaries_zero] at hf ⊢
    rw [hf, map_zero]
  | succ n =>
    obtain ⟨g, rfl⟩ := hf
    exact ⟨map φ n g, (map_differential φ n g).symm⟩

/-- The linear map on cycles induced by an equivariant coefficient map. -/
def mapCycles (φ : M →ₗ⁅K,L⁆ N) (q : ℕ) :
    cycles K L M q →ₗ[K] cycles K L N q :=
  (map φ q).restrict (map_mem_cycles φ q)

@[simp] theorem mapCycles_val (φ : M →ₗ⁅K,L⁆ N) (q : ℕ) (f : cycles K L M q) :
    (mapCycles φ q f).val = map φ q f.val := rfl

/-- The restricted cycle map preserves the boundary submodules. -/
theorem mapCycles_mem_boundariesInCycles (φ : M →ₗ⁅K,L⁆ N) (q : ℕ)
    (f : cycles K L M q) (hf : f ∈ boundariesInCycles K L M q) :
    mapCycles φ q f ∈ boundariesInCycles K L N q := by
  apply mem_boundariesInCycles.mpr
  exact map_mem_boundaries φ q f.val (mem_boundariesInCycles.mp hf)

/-- The induced linear map on the actual cohomology quotients. -/
def mapCohomology (φ : M →ₗ⁅K,L⁆ N) (q : ℕ) :
    CoefficientCohomology K L M q →ₗ[K] CoefficientCohomology K L N q :=
  (boundariesInCycles K L M q).mapQ (boundariesInCycles K L N q)
    (mapCycles φ q) (mapCycles_mem_boundariesInCycles φ q)

/-- On a class, the induced map is represented by coefficient postcomposition. -/
@[simp] theorem mapCohomology_class (φ : M →ₗ⁅K,L⁆ N) (q : ℕ)
    (f : cycles K L M q) :
    mapCohomology φ q (cohomologyClass K L M q f) =
      cohomologyClass K L N q (mapCycles φ q f) := rfl

@[simp] theorem mapCycles_id (q : ℕ) :
    mapCycles (LieModuleHom.id : M →ₗ⁅K,L⁆ M) q = LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply AlternatingMap.ext
  intro x
  rfl

theorem mapCycles_comp (φ : M →ₗ⁅K,L⁆ N) (ψ : N →ₗ⁅K,L⁆ P) (q : ℕ) :
    mapCycles (ψ.comp φ) q = (mapCycles ψ q).comp (mapCycles φ q) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply AlternatingMap.ext
  intro x
  rfl

/-- Identity coefficient maps induce the identity in cohomology. -/
@[simp] theorem mapCohomology_id (q : ℕ) :
    mapCohomology (LieModuleHom.id : M →ₗ⁅K,L⁆ M) q = LinearMap.id := by
  apply LinearMap.ext
  intro z
  obtain ⟨f, rfl⟩ := cohomologyClass_surjective q z
  rw [mapCohomology_class, mapCycles_id, LinearMap.id_apply, LinearMap.id_apply]

/-- Composition of coefficient maps induces composition on cohomology. -/
theorem mapCohomology_comp (φ : M →ₗ⁅K,L⁆ N) (ψ : N →ₗ⁅K,L⁆ P) (q : ℕ) :
    mapCohomology (ψ.comp φ) q = (mapCohomology ψ q).comp (mapCohomology φ q) := by
  apply LinearMap.ext
  intro z
  obtain ⟨f, rfl⟩ := cohomologyClass_surjective q z
  simp only [mapCohomology_class, LinearMap.comp_apply, mapCycles_comp]

end CoefficientMaps

end Langlands.Cohomology.Lie

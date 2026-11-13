import Langlands.Sheaf.Renard.ProjectorVectorSheafSections
import Langlands.Sheaf.Renard.BasisStalk

/-!
# The stalk quotient of a nondegenerate pointwise-test module

Renard (9 July 2026), II.2.5, printed pp.40–41 / PDF pp.46–47.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Langlands.Algebra Langlands.HarmonicAnalysis

universe u v

namespace Langlands.Sheaf.Renard.ProjectorStalk

open ProjectorBasisSheaf ProjectorVectorSheaf

section IndependentUniverses

variable {X : Type u} [TopologicalSpace X]
  (hX : Langlands.Topology.IsLocallyProfinite X)
  {M : Type v} [AddCommGroup M]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
  (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M)

/-- Renard's literal subspace `M(x)`: some compactly supported locally constant test,
nonzero at `x`, kills the original vector. -/
def annihilatorSubmodule (x : X) :
    letI := originalModule hM
    Submodule ℂ M := by
  letI := originalModule hM
  exact
    { carrier := {m | ∃ f : PointwiseTestAlgebra.Carrier X, f x ≠ 0 ∧ f • m = 0}
      zero_mem' := by
        obtain ⟨U, hxU, _⟩ := (compactOpenBasis hX).exists_subset ⊤ (x := x) (by trivial)
        refine ⟨test hX U, ?_, smul_zero _⟩
        simp [test, PointwiseTestAlgebra.characteristic_apply, hxU]
      add_mem' := by
        rintro m n ⟨f, hfx, hfm⟩ ⟨g, hgx, hgn⟩
        refine ⟨f * g, ?_, ?_⟩
        · simpa only [PointwiseTestAlgebra.mul_apply] using mul_ne_zero hfx hgx
        · rw [smul_add]
          have hm : (f * g) • m = 0 := by
            change NonUnitalModuleCorner.originalAction (f * g) m = 0
            rw [mul_comm f g, NonUnitalModuleCorner.originalAction_mul]
            change g • (f • m) = 0
            rw [hfm, smul_zero]
          have hn : (f * g) • n = 0 := by
            change NonUnitalModuleCorner.originalAction (f * g) n = 0
            rw [NonUnitalModuleCorner.originalAction_mul]
            change f • (g • n) = 0
            rw [hgn, smul_zero]
          rw [hm, hn, add_zero]
      smul_mem' := by
        rintro c m ⟨f, hfx, hfm⟩
        exact ⟨f, hfx, by rw [action_smul_comm hM, hfm, smul_zero]⟩ }

@[simp] theorem mem_annihilatorSubmodule (x : X) (m : M) :
    letI := originalModule hM
    m ∈ annihilatorSubmodule hX hM x ↔
      ∃ f : PointwiseTestAlgebra.Carrier X, f x ≠ 0 ∧ f • m = 0 :=
  Iff.rfl

/-- The compact-open relation printed immediately before the quotient description. -/
def SameProjectorGerm (x : X) (m n : M) : Prop :=
  ∃ U : CompactOpen hX, x ∈ U.obj ∧ action hX M U m = action hX M U n

/-- The literal test-annihilator condition agrees with vanishing on a compact-open
neighborhood, at independent space and original-module universes. -/
def AnnihilatorDescription : Prop :=
  ∀ x : X, ∀ m : M,
    letI := originalModule hM
    m ∈ annihilatorSubmodule hX hM x ↔ SameProjectorGerm hX x m 0

/-- The quotient is the actual additive stalk colimit on compact-open neighborhoods.
The compatibility is required for every neighborhood, so the comparison is canonical. -/
def BasisStalkComparison : Prop :=
  ∀ x : X,
    letI := originalModule hM
    ∃ e : (M ⧸ annihilatorSubmodule hX hM x) ≃+
        rawStalk (rawPresheaf hX M) x,
      ∀ (U : CompactOpen hX) (hx : x ∈ U.obj) (m : M),
        e ((annihilatorSubmodule hX hM x).mkQ m) =
          rawGerm (rawPresheaf hX M) U x hx
            (NonUnitalModuleCorner.projection (idempotent hX U) m)

end IndependentUniverses

section VectorStalk

variable {X : Type u} [TopologicalSpace X]
  (hX : Langlands.Topology.IsLocallyProfinite X)
  {M : Type u} [AddCommGroup M]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
  (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M)

/-- The original-vector section followed by the actual all-open colimit germ. -/
def originalGerm (x : X) :
    letI := originalModule hM
    M →ₗ[ℂ] (ProjectorVectorSheaf.presheaf.{u,u} hX hM).stalk x :=
  letI := originalModule hM
  ((ProjectorVectorSheaf.presheaf.{u,u} hX hM).Γgerm x).hom.comp
    (originalSection.{u,u} hX hM ⊤)

/-- The original-vector germ map is onto the actual vector-sheaf stalk. -/
def GermSurjective : Prop :=
  ∀ x : X, Function.Surjective (originalGerm hX hM x)

/-- Its kernel is the literal test-annihilator submodule, rather than a subspace
defined by requiring this kernel equality. -/
def GermKernel : Prop :=
  ∀ x : X,
    letI := originalModule hM
    LinearMap.ker (originalGerm hX hM x) = annihilatorSubmodule hX hM x

/-- Equality in the actual stalk is exactly equality after some neighborhood projector. -/
def GermEquality : Prop :=
  ∀ (x : X) (m n : M),
    originalGerm hX hM x m = originalGerm hX hM x n ↔ SameProjectorGerm hX x m n

/-- The canonical complex-linear identification `M/M(x) ≃ ℳ_x`, characterized on all
original vectors by the actual germ map. -/
def VectorStalkComparison : Prop :=
  ∀ x : X,
    letI := originalModule hM
    ∃ e : (M ⧸ annihilatorSubmodule hX hM x) ≃ₗ[ℂ]
        (ProjectorVectorSheaf.presheaf.{u,u} hX hM).stalk x,
      ∀ m : M, e ((annihilatorSubmodule hX hM x).mkQ m) = originalGerm hX hM x m

end VectorStalk

/-- Renard II.2.5, printed pp.40–41: the compact-open and annihilator descriptions of
the module's stalk, both as the independent-universe basis colimit and as the actual
complex-vector-sheaf stalk where Mathlib's germ universe agrees with the space universe. -/
def ProjectorStalkDescription : Prop :=
  (∀ (X : Type u) [TopologicalSpace X]
    (hX : Langlands.Topology.IsLocallyProfinite X)
    (M : Type v) [AddCommGroup M]
    [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
    (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M),
      AnnihilatorDescription hX hM ∧ BasisStalkComparison hX hM) ∧
  (∀ (X : Type u) [TopologicalSpace X]
    (hX : Langlands.Topology.IsLocallyProfinite X)
    (M : Type u) [AddCommGroup M]
    [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
    (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M),
      GermSurjective hX hM ∧ GermKernel hX hM ∧ GermEquality hX hM ∧
        VectorStalkComparison hX hM)

end Langlands.Sheaf.Renard.ProjectorStalk

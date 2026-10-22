import Langlands.Representation.Smooth.FixedVectors.Definitions
import Langlands.Representation.Category.Subquotients
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Basic.Complex.Basic

/-!
# Fixed-vector detection and fixed-vector dimension descent

Proposition targets only. Fixed vectors generate a semisimple representation
when they meet every simple subrepresentation, generation detects zero
intertwiners, and finite fixed-vector dimension strictly drops for actual
kernels, images and cokernels of endomorphisms of smooth representations.
-/

open CategoryTheory

namespace Langlands

/-- If every simple subrepresentation of a semisimple representation contains
a nonzero `K`-fixed vector, every invariant subspace containing all `K`-fixed
vectors is the whole representation. Any field, group and carrier; no topology,
smoothness or finite dimension is assumed. -/
def FixedVectorsGenerateSemisimpleStatement.{uR, uG, uV} : Prop :=
  ∀ (R : Type uR) [Field R] (G : Type uG) [Group G]
    (V : Type uV) [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (K : Subgroup G)
    [Representation.IsSemisimpleRepresentation ρ],
    (∀ S : Subrepresentation ρ, IsAtom S →
      ∃ v : V, v ∈ S ∧ v ∈ fixedVectors ρ K ∧ v ≠ 0) →
    ∀ T : Subrepresentation ρ, fixedVectors ρ K ≤ T.toSubmodule → T = ⊤

/-- If the `K`-fixed vectors generate the source, an intertwiner whose
restriction to `K`-fixed vectors is zero is itself zero. -/
def FixedVectorsDetectIntertwinerStatement.{uR, uG, uV, uW} : Prop :=
  ∀ (R : Type uR) [Field R] (G : Type uG) [Group G]
    (V : Type uV) [AddCommGroup V] [Module R V]
    (W : Type uW) [AddCommGroup W] [Module R W]
    (ρ : Representation R G V) (σ : Representation R G W) (K : Subgroup G),
    (∀ S : Subrepresentation ρ, fixedVectors ρ K ≤ S.toSubmodule → S = ⊤) →
    ∀ f : ρ.IntertwiningMap σ, fixedVectorsMap f K = 0 → f = 0

namespace SmoothRep

/-- For an endomorphism of a smooth representation with finite-dimensional
`K`-fixed space, a nonzero restriction to `K`-fixed vectors makes the
`K`-fixed space of the actual kernel strictly smaller. Any field, any group
with any topology, and any subgroup `K`. -/
def FixedVectorsKernelFinrankLtStatement.{uR, uG, uV} : Prop :=
  ∀ (R : Type uR) [Field R] (G : Type uG) [Group G] [TopologicalSpace G]
    (A : SmoothRep.{uR, uG, uV} R G) (K : Subgroup G)
    [FiniteDimensional R (fixedVectors A.representation K)] (f : A ⟶ A),
    fixedVectorsMap (hom f) K ≠ 0 →
      Module.finrank R (fixedVectors (SmoothRep.kernel f).representation K) <
        Module.finrank R (fixedVectors A.representation K)

/-- For a complex smooth endomorphism and a compact open subgroup `K` with
finite-dimensional ambient `K`-fixed space, noninjectivity on `K`-fixed vectors
makes the `K`-fixed space of the actual image strictly smaller. -/
def FixedVectorsImageFinrankLtStatement.{uG, uV} : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : SmoothRep.{0, uG, uV} ℂ G) (K : OpenSubgroup G),
    IsCompact (K : Set G) →
    ∀ [FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup)] (f : A ⟶ A),
    ¬ Function.Injective (fixedVectorsMap (hom f) K.toSubgroup) →
      Module.finrank ℂ (fixedVectors (SmoothRep.image f).representation K.toSubgroup) <
        Module.finrank ℂ (fixedVectors A.representation K.toSubgroup)

/-- For a complex smooth endomorphism and a compact open subgroup `K` with
finite-dimensional ambient `K`-fixed space, a nonzero restriction to `K`-fixed
vectors makes the `K`-fixed space of the actual cokernel strictly smaller. -/
def FixedVectorsCokernelFinrankLtStatement.{uG, uV} : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : SmoothRep.{0, uG, uV} ℂ G) (K : OpenSubgroup G),
    IsCompact (K : Set G) →
    ∀ [FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup)] (f : A ⟶ A),
    fixedVectorsMap (hom f) K.toSubgroup ≠ 0 →
      Module.finrank ℂ (fixedVectors (SmoothRep.cokernel f).representation K.toSubgroup) <
        Module.finrank ℂ (fixedVectors A.representation K.toSubgroup)

/-- Let `i : C ⟶ A` be injective and `q : C ⟶ D` surjective, with endomorphisms
`fC` of `C` and `fA` of `A` satisfying `i ∘ fC = fA ∘ i` and `q ∘ fC = 0`. For a
compact open subgroup `K`, if the `K`-fixed space of `A` is finite dimensional
and that of `D` is nonzero, then `fA` is not injective on `K`-fixed vectors.
No irreducibility or semisimplicity is assumed. -/
def FixedVectorsSubquotientWitnessStatement.{uG, uV} : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A C D : SmoothRep.{0, uG, uV} ℂ G) (K : OpenSubgroup G),
    IsCompact (K : Set G) →
    ∀ [FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup)]
      [Nontrivial (fixedVectors D.representation K.toSubgroup)]
      (i : C ⟶ A) (q : C ⟶ D),
    Function.Injective (hom i) → Function.Surjective (hom q) →
    ∀ (fA : A ⟶ A) (fC : C ⟶ C),
    (hom i).comp (hom fC) = (hom fA).comp (hom i) →
    (hom q).comp (hom fC) = 0 →
      ¬ Function.Injective (fixedVectorsMap (hom fA) K.toSubgroup)

end SmoothRep

/-- The six fixed-vector detection and dimension-descent statements, with
independent coefficient, group and carrier universes. -/
def FixedVectorDetectionDescentStatement.{uR, uG, uV, uW} : Prop :=
  FixedVectorsGenerateSemisimpleStatement.{uR, uG, uV} ∧
  FixedVectorsDetectIntertwinerStatement.{uR, uG, uV, uW} ∧
  SmoothRep.FixedVectorsKernelFinrankLtStatement.{uR, uG, uV} ∧
  SmoothRep.FixedVectorsImageFinrankLtStatement.{uG, uV} ∧
  SmoothRep.FixedVectorsCokernelFinrankLtStatement.{uG, uV} ∧
  SmoothRep.FixedVectorsSubquotientWitnessStatement.{uG, uV}

end Langlands

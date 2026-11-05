import Langlands.Geometry.Building.AffineWeylGroups

/-!
# Geometric chamber walls and simple affine reflections

Definitions on the existing affine-root arrangement. A wall contains a face whose affine
span is that nonconstant root hyperplane. Simple affine roots retain positivity and
indivisibility. Reflections are the actual coroot reflections, as elements of `W(Ψ)`.
No Coxeter generation or chamber transitivity assertion is proved here.
-/

noncomputable section

namespace Langlands.Geometry.Building.AffineRootSystem

open scoped Affine

universe uV uA

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]

/-- A root hyperplane is a wall of a chamber when it is the affine span of a face of that
chamber. Nonconstancy makes this a codimension-one face (KP Remark 1.3.16). -/
def IsChamberWall (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A) (H : AffineSubspace ℝ A) : Prop :=
  IsChamber Ψ C ∧
    (∃ ψ ∈ Ψ, ψ.linear ≠ 0 ∧ H = hyperplane ψ) ∧
      ∃ Fa : Set A, IsFaceOf Ψ Fa C ∧ affineSpan ℝ Fa = H

/-- The positive indivisible affine roots whose hyperplanes are walls of `C`
(KP Definition 1.3.19). -/
def simpleAffineRoots (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A) : Set (A →ᵃ[ℝ] ℝ) :=
  {ψ | ψ ∈ positiveRoots Ψ C ∧ ψ ∈ nonDivisibleRoots Ψ ∧
    IsChamberWall Ψ C (hyperplane ψ)}

/-- The geometric simple reflections of `C`, literally in the reflection-generated affine
Weyl group. Each reflection is `x ↦ -ψ(x) • v +ᵥ x` for a coroot of a simple affine root. -/
def chamberSimpleReflections (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A) :
    Set (affineWeylGroup Ψ) :=
  {s | ∃ ψ ∈ simpleAffineRoots Ψ C, ∃ (v : V) (hv : IsCoroot Ψ ψ v),
    (s : A ≃ᵃ[ℝ] A) = affineReflection ψ hv.1}

/-- The chamber-simple affine roots vanishing at every point of `Fa`
(KP Proposition 7.5.5). The face premise is supplied by the consumer. -/
def facetSimpleAffineRoots (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C Fa : Set A) :
    Set (A →ᵃ[ℝ] ℝ) :=
  {ψ | ψ ∈ simpleAffineRoots Ψ C ∧ ∀ x ∈ Fa, ψ x = 0}

/-- The geometric chamber-simple reflections associated with a facet, by vanishing of
its defining simple affine roots on the facet (KP Proposition 7.5.5). -/
def facetSimpleReflections (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C Fa : Set A) :
    Set (affineWeylGroup Ψ) :=
  {s | ∃ ψ ∈ facetSimpleAffineRoots Ψ C Fa, ∃ (v : V) (hv : IsCoroot Ψ ψ v),
    (s : A ≃ᵃ[ℝ] A) = affineReflection ψ hv.1}

theorem simpleAffineRoots_subset (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A) :
    simpleAffineRoots Ψ C ⊆ Ψ :=
  fun _ h => h.1.1

theorem facetSimpleReflections_subset (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C Fa : Set A) :
    facetSimpleReflections Ψ C Fa ⊆ chamberSimpleReflections Ψ C := by
  rintro s ⟨ψ, hψ, v, hv, hs⟩
  exact ⟨ψ, hψ.1, v, hv, hs⟩

/-- With no roots there are no simple affine roots, including the rank-zero apartment. -/
@[simp] theorem simpleAffineRoots_empty (C : Set A) :
    simpleAffineRoots (∅ : Set (A →ᵃ[ℝ] ℝ)) C = ∅ := by
  exact Set.eq_empty_iff_forall_notMem.2 fun _ h => h.1.1

/-- Rank zero has an empty simple-reflection set. -/
@[simp] theorem chamberSimpleReflections_empty (C : Set A) :
    chamberSimpleReflections (∅ : Set (A →ᵃ[ℝ] ℝ)) C = ∅ := by
  simp [chamberSimpleReflections]

end Langlands.Geometry.Building.AffineRootSystem

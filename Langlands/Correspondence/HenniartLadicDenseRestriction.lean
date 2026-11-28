import Langlands.Correspondence.HenniartLadicClasses
import Langlands.Weil.Representation.DenseRestriction
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Restriction of continuous ℓ-adic representations along a map with dense image

For a topological group `G`, a group `H` and a homomorphism `φ : H →* G` with dense image,
restriction along `φ` of representations of `G` over `E = PadicAlgCl ℓ` that satisfy
`IsLadicContinuous` preserves and reflects intertwiners, isomorphism, irreducibility and
the finite-model condition `IsLadicDefinedOverFiniteExtension`. The last uses that a
finite-dimensional intermediate field of `E / ℚ_ℓ` is closed in `E`.
-/

noncomputable section

universe uG uH uW

namespace Langlands.Henniart.LocalNumerical

open FiniteRepresentation

variable (ℓ : ℕ) [Fact ℓ.Prime]

local notation "E" => PadicAlgCl ℓ

/-- A finite-dimensional intermediate field of `PadicAlgCl ℓ / ℚ_ℓ` is closed in
`PadicAlgCl ℓ`: as a finite-dimensional subspace over the complete field `ℚ_ℓ` it is
complete. -/
theorem isClosed_intermediateField_of_finiteDimensional (L : IntermediateField ℚ_[ℓ] E)
    [FiniteDimensional ℚ_[ℓ] L] : IsClosed (L : Set E) := by
  have : FiniteDimensional ℚ_[ℓ] (Subalgebra.toSubmodule L.toSubalgebra) :=
    inferInstanceAs (FiniteDimensional ℚ_[ℓ] L)
  exact Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule L.toSubalgebra)

variable {G : Type uG} [Group G] [TopologicalSpace G] {H : Type uH} [Group H] (φ : H →* G)

/-- Along a homomorphism with dense image, a representation satisfying `IsLadicContinuous`
has its matrix entries in a finite extension of `ℚ_ℓ`, in some basis, if and only if its
restriction does. -/
theorem isLadicDefinedOverFiniteExtension_restrict_iff (hφ : DenseRange φ)
    {A : FiniteRepresentation.{0, uG, uW} E G} (hA : IsLadicContinuous ℓ A) :
    IsLadicDefinedOverFiniteExtension ℓ A ↔
      IsLadicDefinedOverFiniteExtension ℓ (restrict φ A) := by
  constructor
  · rintro ⟨L, hL, b, hb⟩
    exact ⟨L, hL, b, fun h i j => hb (φ h) i j⟩
  · rintro ⟨L, hL, b, hb⟩
    let : TopologicalSpace (Module.End E A) := moduleTopology E (Module.End E A)
    have : IsModuleTopology E (Module.End E A) := ⟨rfl⟩
    exact ⟨L, hL, b, Representation.repr_mem_of_denseRange φ hφ hA b
      (isClosed_intermediateField_of_finiteDimensional ℓ L) hb⟩

/-- Along a homomorphism with dense image, restriction of representations satisfying
`IsLadicContinuous` preserves and reflects intertwiners, isomorphism, irreducibility and
`IsLadicDefinedOverFiniteExtension`. -/
theorem ladicRestriction_of_denseRange (hφ : DenseRange φ)
    (A B : FiniteRepresentation.{0, uG, uW} E G) (hA : IsLadicContinuous ℓ A)
    (hB : IsLadicContinuous ℓ B) :
    (∀ f : A →ₗ[E] B, (∀ g v, f (A.representation g v) = B.representation g (f v)) ↔
        ∀ h v, f (A.representation (φ h) v) = B.representation (φ h) (f v)) ∧
      (IsIsomorphic A B ↔ IsIsomorphic (restrict φ A) (restrict φ B)) ∧
      (A.representation.IsIrreducible ↔ (restrict φ A).representation.IsIrreducible) ∧
      (IsLadicDefinedOverFiniteExtension ℓ A ↔
        IsLadicDefinedOverFiniteExtension ℓ (restrict φ A)) := by
  let : TopologicalSpace (Module.End E A) := moduleTopology E (Module.End E A)
  have : IsModuleTopology E (Module.End E A) := ⟨rfl⟩
  let : TopologicalSpace (Module.End E B) := moduleTopology E (Module.End E B)
  have : IsModuleTopology E (Module.End E B) := ⟨rfl⟩
  exact ⟨fun f => Representation.intertwines_iff_of_denseRange φ hφ hA hB f,
    isIsomorphic_restrict_iff_of_denseRange φ hφ hA hB,
    isIrreducible_restrict_iff_of_denseRange φ hφ hA,
    isLadicDefinedOverFiniteExtension_restrict_iff ℓ φ hφ hA⟩

end Langlands.Henniart.LocalNumerical

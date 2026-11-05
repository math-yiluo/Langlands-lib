import Langlands.LinearAlgebra.IrreducibleRepresentationSpanStatement
import Langlands.Algebra.SandwichDimensionBoundProof
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Burnside span and its matrix-action form -/

noncomputable section

universe u v w

open scoped MonoidAlgebra Matrix

namespace Langlands.LinearAlgebra

/-- Burnside surjectivity for the monoid-algebra action of an irreducible representation. -/
theorem asAlgebraHom_surjective_of_irreducible
    {K : Type u} [Field K] [IsAlgClosed K]
    {H : Type v} [Monoid H]
    {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K H V) [Representation.IsIrreducible ρ] :
    Function.Surjective ρ.asAlgebraHom := by
  exact SandwichDimensionBound.action_surjective K K[H] ρ.asModule

/-- The operators of an irreducible representation span all endomorphisms. -/
theorem irreducibleRepresentationSpan_proof :
    IrreducibleRepresentationSpanStatement.{u,v,w} := by
  intro K _ _ H _ V _ _ _ ρ hirr
  let := hirr
  apply top_unique
  intro f _
  obtain ⟨a, rfl⟩ := asAlgebraHom_surjective_of_irreducible ρ f
  apply MonoidAlgebra.induction_on a
  · intro h
    rw [Representation.asAlgebraHom_of]
    exact Submodule.subset_span ⟨h, rfl⟩
  · intro a b ha hb
    simpa only [map_add] using Submodule.add_mem _ ha hb
  · intro c a ha
    simpa only [map_smul] using Submodule.smul_mem _ c ha

/-- The natural linear action of a monoid of invertible matrices. -/
def matrixAction {K : Type u} [Field K] {H : Type v} [Monoid H]
    {n : Type w} [Fintype n] [DecidableEq n] (r : H →* GL n K) :
    Representation K H (n → K) :=
  Matrix.toLinAlgEquiv'.toAlgHom.toMonoidHom.comp ((Units.coeHom _).comp r)

@[simp]
theorem matrixAction_apply {K : Type u} [Field K] {H : Type v} [Monoid H]
    {n : Type w} [Fintype n] [DecidableEq n] (r : H →* GL n K)
    (h : H) (x : n → K) : matrixAction r h x = (r h : Matrix n n K) *ᵥ x := rfl

/-- The matrices of an irreducible action span the entire matrix algebra. -/
theorem matrix_span_eq_top_of_irreducible
    {K : Type u} [Field K] [IsAlgClosed K] {H : Type v} [Monoid H]
    {n : Type w} [Fintype n] [DecidableEq n] (r : H →* GL n K)
    [Representation.IsIrreducible (matrixAction r)] :
    Submodule.span K (Set.range fun h => (r h : Matrix n n K)) = ⊤ := by
  let e : Matrix n n K ≃ₗ[K] Module.End K (n → K) := Matrix.toLinAlgEquiv'.toLinearEquiv
  have he : (Submodule.span K (Set.range fun h => (r h : Matrix n n K))).map
      e.toLinearMap = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact irreducibleRepresentationSpan_proof K H (n → K) (matrixAction r) inferInstance
  apply Submodule.map_injective_of_injective e.injective
  rw [he, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]

end Langlands.LinearAlgebra

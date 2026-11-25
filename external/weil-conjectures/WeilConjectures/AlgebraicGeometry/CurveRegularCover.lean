/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

module

public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# A finite regular cover of a curve

A scheme `C` of finite type and of dimension at most one over a field (not necessarily reduced)
is covered by the images of finitely many finite morphisms from regular schemes: the
normalizations of its irreducible components, the latter with their reduced induced closed
subscheme structures. A normal noetherian scheme of dimension at most one is regular, its local
rings being fields or discrete valuation rings.

## Main statements

- `AlgebraicGeometry.Scheme.isRegular_normalization`
- `AlgebraicGeometry.Scheme.exists_isFinite_isRegular_cover`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The normalization of an integral scheme of finite type and of dimension at most one over a
field is regular: its local rings are integrally closed noetherian local domains of dimension at
most one, hence fields or discrete valuation rings. -/
theorem isRegular_normalization {k : Type u} [Field k] (X : Scheme.{u}) [IsIntegral X]
    (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] (hdim : topologicalKrullDim X ≤ 1) :
    IsRegular X.normalization := by
  have := X.isFinite_fromNormalization_of_locallyOfFiniteType q
  have : IsLocallyNoetherian X.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (X.fromNormalization ≫ q)
  exact IsRegular.of_isIntegrallyClosed_stalk
    (fun y ↦ ⟨inferInstance, X.fromSpecFunctionField.isIntegrallyClosed_stalk_normalization
      (isIntegrallyClosed_stalk_Spec X.functionField) y⟩)
    ((X.topologicalKrullDim_normalization q).trans_le hdim)

/-- **A curve has a finite regular cover.** A scheme `C` of finite type and of dimension at most
one over a field is covered by the images of finitely many finite morphisms `ν_i : Y_i ⟶ C`
from regular locally noetherian schemes: the normalizations of the irreducible components of
`C`, with their reduced induced closed subscheme structures. -/
theorem exists_isFinite_isRegular_cover {k : Type u} [Field k] {C : Scheme.{u}}
    (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim C ≤ 1) :
    ∃ (ι : Type u) (_ : Finite ι) (Y : ι → Scheme.{u}) (ν : ∀ i, Y i ⟶ C),
      (∀ i, IsFinite (ν i)) ∧ (∀ i, IsRegular (Y i)) ∧ (∀ i, IsLocallyNoetherian (Y i)) ∧
        ∀ x : C, ∃ i, x ∈ Set.range (ν i).base := by
  have : IsNoetherian C := isNoetherian_of_locallyOfFiniteType p
  let ι := {Z : Set C // Z ∈ irreducibleComponents C}
  have : Finite ι := (finite_irreducibleComponents_of_isNoetherian (X := C)).to_subtype
  let I (i : ι) := Scheme.IdealSheafData.vanishingIdeal
    (⟨i.1, isClosed_of_mem_irreducibleComponents _ i.2⟩ : TopologicalSpace.Closeds C)
  have hr (i : ι) : Set.range (I i).subschemeι = i.1 := by
    simp [I]
  have hint (i : ι) : IsIntegral (I i).subscheme := by
    have : IrreducibleSpace (I i).subscheme := by
      exact Subtype.irreducibleSpace i.2.1
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  have hdim' (i : ι) : topologicalKrullDim (I i).subscheme ≤ 1 :=
    ((I i).subschemeι.isClosedEmbedding.isInducing.topologicalKrullDim_le).trans hdim
  refine ⟨ι, inferInstance, fun i ↦ (I i).subscheme.normalization,
    fun i ↦ (I i).subscheme.fromNormalization ≫ (I i).subschemeι, fun i ↦ ?_, fun i ↦ ?_,
    fun i ↦ ?_, fun x ↦ ?_⟩
  · have := (I i).subscheme.isFinite_fromNormalization_of_locallyOfFiniteType
      ((I i).subschemeι ≫ p)
    infer_instance
  · exact isRegular_normalization _ ((I i).subschemeι ≫ p) (hdim' i)
  · have := (I i).subscheme.isFinite_fromNormalization_of_locallyOfFiniteType
      ((I i).subschemeι ≫ p)
    exact LocallyOfFiniteType.isLocallyNoetherian
      ((I i).subscheme.fromNormalization ≫ (I i).subschemeι ≫ p)
  · let i : ι := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    refine ⟨i, ?_⟩
    obtain ⟨z, hz⟩ : x ∈ Set.range (I i).subschemeι := by
      rw [hr i]
      exact mem_irreducibleComponent
    obtain ⟨w, rfl⟩ := (I i).subscheme.fromNormalization.surjective z
    exact ⟨w, by simp [hz]⟩

end AlgebraicGeometry.Scheme

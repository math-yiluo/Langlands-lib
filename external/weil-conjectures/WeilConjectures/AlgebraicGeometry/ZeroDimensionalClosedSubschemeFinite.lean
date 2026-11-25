/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.DimZeroFiniteOverField
import WeilConjectures.AlgebraicGeometry.Dimension

/-!
# Zero-dimensional closed subschemes are finite over the base field

Source: Stacks Project, Varieties, Tag 06LH (Lemma algebraic-scheme-dim-0), algebraic case;
Morphisms, Tag 03J3, opening paragraph
(blueprint: lem-pc-zero-dimensional-closed-subscheme-finite).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A closed subscheme of a finite-type scheme over a field, with topological dimension
at most zero, is finite over the field and affine, with finite-dimensional global sections.

Source: Stacks Project, Varieties, Tag 06LH (Lemma algebraic-scheme-dim-0), algebraic case;
Morphisms, Tag 03J3, opening paragraph
(blueprint: lem-pc-zero-dimensional-closed-subscheme-finite).

Proof: (1) Mathlib's closed-immersion instances give that `i` is finite, hence locally
of finite type and quasi-compact. Composition with `f` makes `Z` finite type over `k`.
(2) Rewrite the dimension bound using `Scheme.dim_eq_topologicalKrullDim` and apply
`isAffine_and_isFinite_of_dim_le_zero` to the structure morphism `i ≫ f`. This includes
empty `Z`, whose dimension is `⊥`, without a separate case.
(3) The ring map on global sections is finite by `Scheme.Hom.finite_appTop`. Composing
with the inverse of `Scheme.ΓSpecIso` gives a finite ring map from `k`; this is exactly
finite-dimensionality for the algebra structure `(i ≫ f).ΓAlgebra`.
-/
theorem closed_subscheme_finite_of_topologicalKrullDim_le_zero
    {k : Type u} [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i] (hZ : topologicalKrullDim Z ≤ 0) :
    IsFinite (i ≫ f) ∧ IsAffine Z ∧
      (letI := (i ≫ f).ΓAlgebra; FiniteDimensional k Γ(Z, ⊤)) := by
  let : Z.Over (Spec (.of k)) := ⟨i ≫ f⟩
  have : LocallyOfFiniteType (Z ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (i ≫ f)
    infer_instance
  have : QuasiCompact (Z ↘ Spec (.of k)) := by
    change QuasiCompact (i ≫ f)
    infer_instance
  have hdim : Z.dim ≤ 0 := by
    rwa [Scheme.dim_eq_topologicalKrullDim]
  obtain ⟨haff, hfin⟩ := isAffine_and_isFinite_of_dim_le_zero (k := k) Z hdim
  have : IsFinite (i ≫ f) := hfin
  refine ⟨hfin, haff, ?_⟩
  let := (i ≫ f).ΓAlgebra
  change (((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ f).appTop).hom).Finite
  rw [CommRingCat.hom_comp]
  exact (i ≫ f).finite_appTop.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)

end AlgebraicGeometry

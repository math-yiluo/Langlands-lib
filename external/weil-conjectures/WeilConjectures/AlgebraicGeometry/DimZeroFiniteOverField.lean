/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Dimension
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.RingTheory.Jacobson.Artinian

/-!
# Zero-dimensional schemes of finite type over a field

Source: Stacks Project, Varieties, Lemma 33.20.2 (Tag 06LH), algebraic case
(blueprint: lem-pc-algebraic-dim-zero-affine-finite).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme of finite type over a field and of dimension at most zero is affine, and its
structure morphism is finite (Stacks, Tag 06LH).
(blueprint: lem-pc-algebraic-dim-zero-affine-finite)

Proof: The equality of `Scheme.dim` and topological Krull dimension makes `Y` locally
Artinian, since finite type over a field makes it locally Noetherian. Quasi-compactness gives
a compact underlying space, which is finite because it is discrete. A finite discrete scheme
is affine. Its coordinate ring is Artinian and its structure map on global sections is of
finite type. The base ring `Γ(Spec k, ⊤)` is Artinian as well. Mathlib's
`Module.finite_iff_krullDimLE_zero` now makes this ring map finite, which is precisely the
affine criterion for a finite scheme morphism. All these steps include the empty scheme. -/
theorem isAffine_and_isFinite_of_dim_le_zero {k : Type u} [Field k]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (hY : Y.dim ≤ 0) : IsAffine Y ∧ IsFinite (Y ↘ Spec (.of k)) := by
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsLocallyArtinian Y := IsLocallyArtinian.of_topologicalKrullDim_le_zero
    ((Y.dim_eq_topologicalKrullDim).symm ▸ hY)
  have : Finite Y := finite_of_compact_of_discrete
  have : IsAffine Y := inferInstance
  refine ⟨inferInstance, ?_⟩
  apply (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mpr
  refine ⟨inferInstance, ?_⟩
  let f := (Y ↘ Spec (.of k)).appTop.hom
  let := f.toAlgebra
  have : Algebra.FiniteType Γ(Spec (.of k), ⊤) Γ(Y, ⊤) :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  exact (Module.finite_iff_krullDimLE_zero Γ(Spec (.of k), ⊤) Γ(Y, ⊤)).mpr inferInstance

end AlgebraicGeometry

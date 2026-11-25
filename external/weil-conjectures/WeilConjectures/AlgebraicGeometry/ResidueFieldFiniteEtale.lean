/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Etale.Field
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.PointCount

/-!
# Residue fields of points with finite residue field over a finite field

For a scheme `X` over a finite field `k` and a point `x` with finite residue field, the spectrum
`Spec κ(x)` is finite and étale over `k`, and its closed point has finite residue field.

## Main statements

- `AlgebraicGeometry.isFinite_and_etale_specMap_residueFieldAlgebraMap`
- `AlgebraicGeometry.closedPoint_mem_finitePoints`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The spectrum of the residue field of a point with finite residue field, over a finite base
field `k`, is finite and étale over `k`: `κ(x)` is a finite, hence separable, extension of the
perfect field `k`. -/
theorem isFinite_and_etale_specMap_residueFieldAlgebraMap {k : Type u} [Field k] [Finite k]
    {X : Scheme.{u}} (f : X.Hom (Spec (.of k))) {x : X} (hx : x ∈ X.finitePoints) :
    IsFinite (Spec.map (CommRingCat.ofHom (f.residueFieldAlgebraMap x))) ∧
      Etale (Spec.map (CommRingCat.ofHom (f.residueFieldAlgebraMap x))) := by
  have : Finite (X.residueField x) := hx
  let := (f.residueFieldAlgebraMap x).toAlgebra
  have : Module.Finite k (X.residueField x) := Module.Finite.of_finite
  refine ⟨(IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 this),
    HasRingHomProperty.Spec_iff.2 ?_⟩
  have : Algebra.FormallyEtale k (X.residueField x) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  have : Algebra.FinitePresentation k (X.residueField x) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  exact ⟨inferInstance, inferInstance⟩

/-- The closed point of the spectrum of a finite field has finite residue field: the residue
field embeds into the field. -/
theorem closedPoint_mem_finitePoints {K : Type u} [Field K] [Finite K] :
    IsLocalRing.closedPoint K ∈ (Spec (CommRingCat.of K)).finitePoints := by
  obtain ⟨ι, -⟩ := Scheme.exists_eq_spec_map_comp_fromSpecResidueField (𝟙 (Spec (.of K))) _ rfl
  exact (Spec (.of K)).mem_finitePoints.2 (Finite.of_injective _ ι.hom.injective)

end AlgebraicGeometry

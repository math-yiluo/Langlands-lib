/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
import Mathlib.Algebra.CharP.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # The geometric domain of the curve monodromy comparison

Source: latest blueprint, `sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/`
`sk-l-dl-a1-endpoints.proof.md`, smooth curve duality and monodromy hypotheses.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedCurve

/-- A curve has the absolute hypotheses needed for the monodromy fibre.
Source: step 1 of `lem-per-geometric-curve-compact-cohomology`
(blueprint: lem-per-geometric-curve-context).

Proof: curve hypotheses supply finite type and separatedness.
Finite type over a field gives local
Noetherianness; quasi-compactness then gives Noetherianness. Separatedness over a
field gives absolute separatedness. The coefficient prime is nonzero in the base
field, hence a unit, and its image is a unit in each residue field.
No descent or Weil structure enters this argument. -/
theorem geometricCurve_context
    (k : Type u) [Field k] (p ℓ : ℕ)
    [CharP k p] [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (C₀ : Over (Spec (.of k))) [IsCurve C₀.hom] :
    ∃ (_hN : IsNoetherian C₀.left) (_hSep : C₀.left.IsSeparated),
      Nonempty (∀ z : C₀.left, Invertible (ℓ : C₀.left.residueField z)) := by
  have : IsLocallyNoetherian C₀.left :=
    LocallyOfFiniteType.isLocallyNoetherian C₀.hom
  have : CompactSpace C₀.left :=
    QuasiCompact.compactSpace_of_compactSpace C₀.hom
  have hN : IsNoetherian C₀.left := {}
  have hSep := Scheme.isSeparated_of_isSeparated_hom C₀.hom
  have hunit : IsUnit (ℓ : k) :=
    (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime) hℓp.symm).isUnit
  refine ⟨hN, hSep, ⟨fun z ↦ ?_⟩⟩
  let φ := ((Scheme.ΓSpecIso (.of k)).inv ≫ C₀.hom.appTop ≫
    C₀.left.Γevaluation z).hom
  exact (show IsUnit (ℓ : C₀.left.residueField z) by
    simpa using hunit.map φ).invertible

end AlgebraicGeometry.ProEtale.CondensedCurve

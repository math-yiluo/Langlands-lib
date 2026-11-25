/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinVanishing.Reduction

/-!
# The affine Artin vanishing bound

Let `K` be a field with `cd_tor(K) ≤ c` and `X` an affine `K`-scheme of finite type. Then
`cd_tor(X) ≤ dim X + c` (`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine`).

## Implementation details

The proof is by induction on `dim X`, over all ground fields at once; it reduces to algebraically
closed `K` and, by Noether normalisation, to affine space, where the Leray spectral sequence of
`𝔸ᵈ ⟶ ℙ¹ × 𝔸ᵈ⁻¹ ⟶ 𝔸ᵈ⁻¹` and a computation of the stalks of the higher direct images conclude.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- The affine torsion cohomological dimension bound: if `cd_tor(K) ≤ c` and `X` is an affine
`K`-scheme of finite type of dimension at most `d`, then `cd_tor(X) ≤ d + c`, i.e.
`Hᵠ(X_ét, F) = 0` for every torsion abelian étale sheaf `F` on `X` and every `q > d + c`. -/
theorem hasTorsionCohomologicalDimensionLE_of_isAffine {K : Type u} [Field K] {c d : ℕ}
    (hK : (Spec (.of K)).HasTorsionCohomologicalDimensionLE c) {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [IsAffine X]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    X.HasTorsionCohomologicalDimensionLE (d + c) :=
  artinBound d K c hK X a inferInstance inferInstance hX

end AlgebraicGeometry.Scheme

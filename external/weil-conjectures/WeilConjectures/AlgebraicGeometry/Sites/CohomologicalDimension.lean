/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension

/-!
# Torsion cohomological dimension of a scheme of finite type over a field

Let `K` be a field whose torsion étale cohomological dimension is at most `c`, i.e.
`H^q(Spec K_ét, F) = 0` for every torsion abelian sheaf `F` and every `q > c`, and let `X` be a
`K`-scheme of finite type of dimension at most `d`. Then `H^q(X_ét, F) = 0` for every torsion
abelian sheaf `F` on `X_ét` and every `q > 2d + c`
(`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_add_lt`). For `K` separably closed one may
take `c = 0` (`AlgebraicGeometry.Scheme.subsingleton_H_of_isSepClosed`), so that `H^q(X_ét, F) = 0`
for `q > 2d` (`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed`).

## Implementation details

The Leray spectral sequence `Hᵖ(X_Zar, Rᵠε_* F) ⟹ Hᵖ⁺ᵠ(X_ét, F)` for the comparison `ε_*` of the
étale with the Zariski site has `Hᵖ = 0` for `p > d` by Grothendieck vanishing, and
`Rᵠε_* F = 0` for `q > d + c` since `Rᵠε_* F` is the sheafification of `V ↦ Hᵠ(V_ét, F|_V)`,
which vanishes on affine opens `V` by the affine bound
`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine`; see
`WeilConjectures.AlgebraicGeometry.Sites.EtaleZariskiComparison`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Torsion cohomological dimension of a finite-type scheme: if `cd_tor(K) ≤ c` and `X` is a
finite-type `K`-scheme of dimension at most `d`, then `cd_tor(X) ≤ 2d + c`, i.e.
`H^q(X_ét, F) = 0` for every torsion abelian étale sheaf `F` on `X` and every `q > 2d + c`. -/
theorem subsingleton_H_of_two_mul_add_lt {K : Type u} [Field K] (c d : ℕ)
    (hK : ∀ F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}, F.IsTorsion →
      ∀ q : ℕ, c < q → Subsingleton (Sheaf.H F q))
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : 2 * d + c < q) : Subsingleton (Sheaf.H F q) := by
  have := LocallyOfFiniteType.isLocallyNoetherian a
  have := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian X := {}
  refine subsingleton_H_of_isZero_rightDerived_etaleToZariski (e := d + c) hX F
    (fun p hp ↦ isZero_rightDerived_etaleToZariski_of_subsingleton_H F p fun U hU ↦ ?_) q
    (by lia)
  have : IsAffine U := hU
  exact hasTorsionCohomologicalDimensionLE_of_isAffine hK (U.ι ≫ a)
    ((topologicalKrullDim_subspace_le X U).trans hX) _
    (Etale.isTorsion_upperStar U.ι hF) p hp

/-- The cohomological-dimension bound over a separably closed field: if `K` is separably closed
and `X` is a finite-type `K`-scheme of dimension at most `d`, then `cd_tor(X) ≤ 2d`, i.e.
`H^q(X_ét, F) = 0` for every torsion abelian étale sheaf `F` on `X` and every `q > 2d`. -/
theorem subsingleton_H_of_two_mul_lt_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K]
    (d : ℕ) {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : 2 * d < q) : Subsingleton (Sheaf.H F q) :=
  subsingleton_H_of_two_mul_add_lt 0 d
    (fun G _ q hq ↦ by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hq
      simpa using subsingleton_H_of_isSepClosed K G n)
    a hX F hF q hq

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension

/-!
# Torsion cohomological dimension of an affine scheme of finite type over a separably closed field

Let `K` be a separably closed field and `X` an affine `K`-scheme of finite type of dimension at
most `d`. Then `H^q(X_ét, F) = 0` for every torsion abelian sheaf `F` on `X_ét` and every `q > d`
(`AlgebraicGeometry.Scheme.subsingleton_H_of_lt_of_isAffine_of_isSepClosed`). This is the case
`c = 0` of Artin's affine vanishing theorem
`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine`, which applies since
`cd_tor(Spec K) = 0`
(`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_zero_of_isSepClosed`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The affine torsion cohomological dimension bound over a separably closed field: for an
affine finite-type `K`-scheme `X` of dimension at most `d`, `H^q(X_ét, F) = 0` for every torsion
abelian étale sheaf `F` and every `q > d`. -/
theorem subsingleton_H_of_lt_of_isAffine_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K]
    (d : ℕ) {X : Scheme.{u}} [IsAffine X] (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : d < q) : Subsingleton (Sheaf.H F q) :=
  hasTorsionCohomologicalDimensionLE_of_isAffine
    (hasTorsionCohomologicalDimensionLE_zero_of_isSepClosed K) a hX F hF q (by simpa using hq)

end AlgebraicGeometry.Scheme

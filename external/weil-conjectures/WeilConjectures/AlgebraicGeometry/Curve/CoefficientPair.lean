/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Curve coefficient pairs

Let `k` be an algebraically closed field. A *curve coefficient pair* `(C, F)` over `k`
consists of a curve `C` over `k` (separated of finite type of dimension at most one,
`AlgebraicGeometry.IsCurve`) and a torsion abelian sheaf `F` on the small étale site of `C`.

## Main definitions

- `AlgebraicGeometry.CurveCoefficientPair`: a curve coefficient pair
  (blueprint: `theorem-cohomology-curves`).
- `AlgebraicGeometry.CurveCoefficientPair.IsConstructible`: the sheaf `F` of a curve
  coefficient pair is constructible, i.e. `AlgebraicGeometry.Scheme.IsConstructibleSheaf F`
  (blueprint: `def-weil-pbc-constructible-torsion`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A *curve coefficient pair* over an algebraically closed field `k`: a curve `C` over `k`
together with a torsion abelian sheaf `F` on the small étale site of `C`.
(blueprint: `theorem-cohomology-curves`) -/
structure CurveCoefficientPair (k : Type u) [Field k] [IsAlgClosed k] where
  /-- The underlying scheme of the curve. -/
  C : Scheme.{u}
  /-- The structure morphism of `C` over `k`. -/
  toSpec : C ⟶ Spec (.of k)
  /-- `C` is separated of finite type over `k` of dimension at most one. -/
  isCurve : IsCurve toSpec
  /-- The coefficient sheaf, an abelian sheaf on the small étale site of `C`. -/
  F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}
  /-- The coefficient sheaf is torsion. -/
  isTorsion : CategoryTheory.Sheaf.IsTorsion F

namespace CurveCoefficientPair

/-- The sheaf `F` of a curve coefficient pair `(C, F)` is *constructible* if `C` has a finite
partition into locally closed constructible subschemes on each of which `F` is locally
constant with finite stalks. (blueprint: `def-weil-pbc-constructible-torsion`) -/
def IsConstructible {k : Type u} [Field k] [IsAlgClosed k] (P : CurveCoefficientPair k) :
    Prop :=
  Scheme.IsConstructibleSheaf P.F

end CurveCoefficientPair

end AlgebraicGeometry

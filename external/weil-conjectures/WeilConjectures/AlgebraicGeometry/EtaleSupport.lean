/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ZetaSeries
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories

/-!
# Transcendence-degree strata and support on the small etale site

Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/def-kun-support.md`
(blueprint: def-kun-support).

Closed points are the existing `closedPoints X`, defined by `IsClosed {x}`.
The residue field is `X.residueField x`; its base-field structure is induced by the
structure morphism through `Scheme.Hom.residueFieldAlgebraMap`.

## Main definitions

* `Scheme.Hom.pointsOfTrdegLE`: the set `E_a(X)`.
* `Scheme.etaleSheafSupport`: points with some nonzero geometric stalk.
* `Scheme.etaleComplexSupport`: the union of the supports of all cohomology sheaves.

The support constructions do not require a base field or finite-type hypotheses, and
in particular apply to the finite-type schemes over a field considered in the source.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- For a structure morphism `p` of finite type over a field `k`, `E_a(X)` is the set
of points whose residue field has transcendence degree at most the nonnegative integer `a`.
The algebra structure is the one induced by `p`, not an independently chosen algebra.
Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/def-kun-support.md`
(blueprint: def-kun-support). -/
def Hom.pointsOfTrdegLE {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p] (a : ℕ) : Set X :=
  {x | letI := (p.residueFieldAlgebraMap x).toAlgebra
    Algebra.trdeg k (X.residueField x) ≤ (a : Cardinal.{u})}

/-- The support of an abelian etale sheaf is the set of points `x` admitting a geometric
point over `x` with nonzero stalk. No independence-of-geometric-point lemma is used here.
Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/def-kun-support.md`
(blueprint: def-kun-support). -/
def etaleSheafSupport {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : Set X :=
  {x | ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (s : Spec (.of Ω) ⟶ X), s default = x ∧
        ¬ IsZero (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F)}

/-- The support of a derived abelian etale sheaf is the union, over every integer `q`,
of the supports of its cohomology sheaves `H^q`.
Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/def-kun-support.md`
(blueprint: def-kun-support). -/
def etaleComplexSupport {X : Scheme.{u}}
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) : Set X :=
  ⋃ q : ℤ, etaleSheafSupport
    ((DerivedCategory.homologyFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj K)

end AlgebraicGeometry.Scheme

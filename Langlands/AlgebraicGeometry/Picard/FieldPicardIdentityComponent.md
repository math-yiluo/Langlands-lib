# The identity-component open of an actual universal Picard family over a field

This module adds two small definitions and one immediate lemma. Fix an
arbitrary field `k : Type u` in an arbitrary universe `u`, and write

```text
S = Scheme.Spec.obj (Opposite.op (CommRingCat.of k)).
```

The inputs are the existing data `A : AbelianScheme S`, a parameter scheme
`P : Over S`, an actual rigidified family `L : RigidifiedFamily A P`, and a
proof

```text
hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A)
       (unitSection_comp A) L.
```

None of these is redefined. `RigidifiedFamily`, `unitSection` and
`unitSection_comp` come from `Langlands.AlgebraicGeometry.Picard.RelativePicardZero`.
`IsUniversal` is the full all-test-scheme universal property from
`Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalBundle`. In all
declarations below, `k`, `A`, `L` and `hL` are explicit and `P` is implicit,
because the type of `L` determines it.

## The origin point

The published section

```text
e := RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A)
       (unitSection_comp A) L hL : Over.mk (𝟙 S) ⟶ P
```

from `Langlands.AlgebraicGeometry.Picard.UniversalFamilyTriviality` is the
classifying morphism of the canonically rigidified trivial relative line bundle
`relativeTrivial` over the base object `Over.mk (𝟙 S)`. This module reuses it and builds no second
classifier or origin section.

`fullPicardOriginPoint k A L hL : P.left` is defined as the point

```text
e.left (IsLocalRing.closedPoint k).
```

It is the image, under the underlying scheme morphism `e.left : S ⟶ P.left`, of
the closed point of `Spec k`, the zero prime ideal. Since `k` is a field, this
is the only point of `S`. Because `hL` is a proof of a proposition, the point
does not depend on which proof is supplied.

## The identity-component open predicate

For `U : P.left.Opens`, `IsFullPicardIdentityComponentOpen k A L hL U` is the
proposition

```text
(U : Set P.left) = connectedComponent (fullPicardOriginPoint k A L hL),
```

where `connectedComponent` is Mathlib's topological connected component in the
underlying topological space of `P.left`. The predicate is a `def` returning
`Prop`. It says only that the specified open subset has exactly the carrier of
the connected component of the specified origin point.

`fullPicardOriginPoint_mem` proves that the origin point lies in every such `U`.
It rewrites by the defining equality and applies Mathlib's
`mem_connectedComponent`.

## What the predicate does not assert

The predicate identifies a *given* open subset. It does not prove that the
connected component of the origin is open, nor that any `U` satisfying the
predicate exists. No local finite type hypothesis is imposed on `P.hom`; in a
general topological space a connected component need not be open, which is why
the open subset is part of the data.

It equips neither the full parameter scheme `P` nor `U` with a group-scheme
structure. The predicate also does not compare `U` with the existing geometric
Picard-zero subfunctor. The equality of carriers is the definition of the chosen
identity-component open. It is not the all-test-scheme criterion
`IsPicardZeroOpenLocus A L U` from `Langlands.AlgebraicGeometry.Picard.OpenLocus`,
and nothing here proves either predicate from the other.

Later applications should form the open subscheme with the existing
`openLocusParameter P U`, its inclusion `openLocusInclusion P U`, and the actual
restricted family `restrictedRigidifiedFamily A L U` from
`Langlands.AlgebraicGeometry.Picard.OpenLocus`. That construction is the actual
open restriction `U.toScheme` of `P.left`. It keeps the structure sheaf of `P.left`
on `U`, including nilpotents, and does not pass to a reduced subscheme. This
module adds no other restriction construction and no aliases for those
declarations.

The following substantial results are later work. None of them is a hypothesis,
conclusion or theorem of this module:

- local finite type of the full parameter scheme over `k`;
- openness of the connected component of the origin, and so existence of an
  open satisfying the predicate;
- a group-scheme structure on the full parameter scheme or on the component;
- a comparison of this component with `IsPicardZeroOpenLocus` on every test
  scheme over `S`;
- smoothness of the component, or of the chosen dual scheme in
  `Langlands.AbelianScheme.FieldDualSchemeSmoothStatement`.

## Provenance

The registered original is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft, source ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

- Paragraph (3.16), printed p.38 (PDF p.42), considers a group scheme `G` over
  a field `k`. The image of its identity section is a single closed point `e` of
  degree 1. When `G` is in addition locally of finite type, the source defines
  the identity component `G⁰` as the connected component of `G` containing `e`.
  That component is then open.
- Proposition (3.17), printed pp.38-39 (PDF pp.42-43), proves stronger facts
  about `G⁰`. It is an open and closed, geometrically irreducible subgroup
  scheme, and smoothness can be tested at the origin.
- Chapter VI, §3, printed pp.95-96 (PDF pp.99-100), applies this to `Pic_{X/k}`.
  Printed p.95 notes that `Pic_{X/k}` also represents the functor of line
  bundles rigidified along the zero section, with a rigidified Poincaré bundle.
  Theorem (6.18), printed p.96, proves that `Pic⁰_{X/k}` is reduced and hence
  an abelian variety, and Definition (6.19) calls it the dual.

The two declarations here are an internal interface derived from the
pointed-topological part of (3.16). The source's origin `e` is the image of the
identity section. Here it is the image of the unique point of `Spec k` under the
published section classifying the trivial rigidified family. The group law of
the Picard functor comes from tensor product of line bundles, so its unit is
the trivial class. That is the standard reason for this choice of origin. This
module does not construct the group law, and does not prove that this section is
the unit of one.
The source's set-theoretic definition of `G⁰` as the connected component
containing `e` becomes an equality of carriers with Mathlib's
`connectedComponent`.

The source's hypotheses that `G` is a group scheme locally of finite type are
not imported, and the openness conclusion of (3.16) is not asserted. The open
is supplied, so that no openness theorem is hidden in the definition. This
module does not implement the full classical identity-component construction.
Its universe-general field base and its actual universal-family input follow
the existing field Picard statements, such as
`FieldPicardZeroOpenLocusStatement`.

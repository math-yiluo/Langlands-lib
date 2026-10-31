# Reducedness of a group scheme from its identity stalk

`Langlands.GroupScheme.AlgClosedFieldReducedOfOriginStatement` is a
universe-polymorphic proposition definition. This module states the implication;
it supplies no proof or axiom.

For every algebraically closed field `k : Type u`, it quantifies over an
arbitrary object `P : Over (Spec (CommRingCat.of k))` with Mathlib's actual
`GrpObj P` structure. Assume that its structure morphism `P.hom` is locally of
finite type and that the ring

```text
P.left.presheaf.stalk ((η[P]).left (IsLocalRing.closedPoint k))
```

is reduced. The conclusion is `AlgebraicGeometry.IsReduced P.left`.
Here `η[P]` is the unit morphism of the group object. The tensor unit of
`Over (Spec k)` is the identity of `Spec k`, so evaluating its underlying
scheme morphism at `IsLocalRing.closedPoint k` gives the identity point of `P`.
The hypothesis uses ring-theoretic `_root_.IsReduced` on that stalk, and the
conclusion uses Mathlib's scheme-theoretic `IsReduced`.

The group need not be commutative, connected, quasi-compact, proper, or
smooth. The statement assumes local finite type and reducedness of this
one actual stalk; it assumes no reduced neighbourhood and no global
reducedness or regularity. It does not assert existence of a group scheme
or a Picard parameter.

The imports supply the usual schemes, stalks, reducedness predicates, and
the cartesian monoidal structure on the over category. No new mathematical
object is introduced.

The provenance is derived from the algebraically closed case of
Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft,
Proposition (3.17)(ii), printed pp.38–39 (PDF pp.42–43). The registered
source is `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
That proposition treats a group scheme locally of finite type over a
field. Its proof reduces to an algebraically closed field and uses
translations to propagate reducedness at the origin to the group.
This declaration isolates that implication, with the extension field in
the source's reducedness condition taken to be `k` itself. It does not
state the proposition's additional smoothness equivalences.

A separate proof can translate the origin stalk to each closed point,
using that closed points are `k`-rational, and then use the Jacobson
property and affine maximal localizations to deduce global reducedness.
This is a proposed proof route, not a result of this statement module.
It is independent of Picard representability, tangent and cohomology
comparisons, and existence of ample line bundles or finite stabilizers.

Worker 453 prepared this interface for the generic propagation step of
the rigidified Picard reducedness argument.

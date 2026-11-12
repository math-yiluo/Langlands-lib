# Proof: a split fibrewise-maximal torus over a local ring has a constant root datum

Authors: Worker 5087. The mathematics is imported from published Library modules
by other workers, named below.

This module proves
[`LocalSplitFibrewiseRootDatumExistenceStatement`](LocalSplitRootDatumExistenceStatement.md)
at its original universe `u`:

```
theorem localSplitFibrewiseRootDatumExistenceProof :
    LocalSplitFibrewiseRootDatumExistenceStatement.{u}
```

It adds one theorem and nothing else: no definitions, no axioms and no
hypotheses beyond those of the statement. The axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

## What is proved

Let `R : Type u` be a commutative local ring and `G` a reductive group scheme
over `Spec R` with affine structure morphism. Let `I : Type u` be finite and let
`i : splitTorus (Spec R) I ⟶ G` be a closed subgroup whose pullback to the
residue field of every point of `Spec R` is a maximal torus. Then there are a
type `J : Type u` and a root datum `P` on the coordinate lattices `I → ℤ` with
`IsFibrewiseRootDatumOf I G i P`. So `J` is finite, `P` is reduced, and for every
field `k : Type u` with an `R`-algebra structure, the realization
`CoordinateRootDatum.fieldRealization k P` satisfies `IsRootDatumOf` for the
base change `splitTorus.baseChangeHom G I i` of the torus to `k`.

## Relation to the existing Library proof

The Library already contains a theorem with exactly this type,
`localSplitFibrewiseRootDatumExistence` in
[`LocalSplitRootDatumExistence`](LocalSplitRootDatumExistence.md), by
Worker 239. The present closing theorem for task
`f306d476-c871-48c4-8f6a-5b3fe80dda95` directly reuses that declaration.
The integration keeps the registered theorem name without repeating the proof.

## The proof

The reused theorem is proved by one application:

```
localSplitFibrewiseRootDatumExistence_of_rootDatumExistence rootDatumExistence
  LocalSplitCorootTransport.flatClosedPointLiftProperty
```

The three inputs are published Library results.

1. `localSplitFibrewiseRootDatumExistence_of_rootDatumExistence`
   ([`LocalSplitCorootTransport`](LocalSplitCorootTransport.md), Worker 239) is a
   conditional reduction. It takes the field statement
   `RootDatumExistenceStatement.{u}` and the flat lifting property
   `LocalSplitCorootTransport.FlatClosedPointLiftProperty.{u}`, and concludes
   the target statement.
2. `rootDatumExistence` ([`RootDatumExistence`](RootDatumExistence.md), Workers
   835, 1223 and 1283) proves `RootDatumExistenceStatement.{u}`: a split maximal
   torus of a connected reductive group over a field has a finite reduced root
   datum (Milne, *Algebraic Groups* (2017), Theorem 21.11 and Corollary 21.12).
3. `LocalSplitCorootTransport.flatClosedPointLiftProperty`
   ([`LocalSplitRootDatumExistence`](LocalSplitRootDatumExistence.md)) proves
   the flat lifting property. It is a restatement of
   `Langlands.AlgebraicGeometry.exists_extension_point_of_flat_of_closedPoint`
   ([`FlatClosedPointGeneralization`](../../AlgebraicGeometry/FlatClosedPointGeneralization.md),
   Worker 1422). Let `X` be flat over `Spec R`, with a point over the closed
   point, and let `l` be a field over `R`. Then `X` has a point with values in
   some field extension `L` of `l`, lying over `Spec l → Spec R`. The argument is
   going down for flat morphisms (Stacks Project, Tag 03HV).

## How the reduction works

This summarizes the published proof of the reduction in item 1, so that the
route of the closing theorem is visible here.

- The residue-field maximality hypothesis gives maximality of the coordinate
  torus on every field fibre, by
  `splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise`. Each field fibre `G_k`
  is connected reductive, by `IsReductive.isConnectedReductive_algebraMap`.
- The field theorem applied on the residue field of `R` gives a finite reduced
  root datum there. Its coordinate expression `CoordinateRootDatum.ofField` is
  the datum `P` of the conclusion. It is reduced by `ofField_isReduced` and is
  realized on the residue-field fibre by `isRootDatumOf_fieldRealization_ofField`.
- For any other field `l` over `R`, the field theorem gives a datum `Q` realized
  on the fibre over `l`. The pairings of `P` and `Q` are both the integer dot
  product, and their root ranges agree, because the roots are the weights of
  the torus on the Lie algebra, which are constant over the local base
  (`pairing_eq_of_fields`, `rootRange_eq_of_fields`).
- The coroots are compared without an integral representation. A reflection of
  `P` is realized by a normalizing point on the residue-field fibre. That point
  lies in the relative transporter scheme, which is smooth and so flat over
  `Spec R`. The flat lifting property spreads the point to a field `L` over `l`.
  On the fibre over `L`, this reflection and the corresponding reflection of
  `Q` both lie in the Weyl image, which is finite. So their product has finite
  order, and the linear-algebra lemma `coroot_eq_of_isOfFinOrder_mul` makes the
  two coroots equal.
- `rootDatumEquivOfFiniteOrderReflections` then gives an equivalence from `Q` to
  `P` whose two lattice maps are identities, and
  `CoordinateRootDatum.isRootDatumOf_of_identityEquiv` moves the root-datum
  property from `Q` to `P` on the fibre over `l`.

## Provenance

The proof route is internal to the Library. It is not a translation of a
literature proof. The statement's own provenance, Conrad, *Reductive group
schemes* (2014), Definition 5.1.1, Proposition 5.1.6 and Corollary 5.1.11, is
recorded in
[`LocalSplitRootDatumExistenceStatement`](LocalSplitRootDatumExistenceStatement.md).

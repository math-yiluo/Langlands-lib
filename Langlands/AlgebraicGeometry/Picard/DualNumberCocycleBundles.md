# Actual line bundles of normalized dual-number cocycles

This internal prerequisite constructs actual line bundles from additive
structure-sheaf cocycles on a cover, proves that their actual zero-section
pullbacks are trivial, and proves the tensor and isomorphism-class laws.

Let `k` be any field in universe `u`, let `X` be a scheme in that universe,
and let `f : X ⟶ Spec k`. Write `Xε = thickening f`, `p = projection f`,
and `i = closedPoint f` for the actual fiber product with `Spec k[ε]`,
its projection to `X`, and its zero section. Let `T : ι → X.Opens`,
where `ι : Type u`. When required, `hT : (⨆ a, T a) = ⊤` asserts that
these opens cover `X`. No affineness, separatedness, quasi-compactness,
smoothness or properness hypothesis is needed in this module.

An additive cochain is a family `z a b ∈ Γ(X, T a ⊓ T b)`.
The cocycle condition is exactly the existing `CechDegreeOne.IsCocycle`
for the actual module sheaf `structureSheaf X`: restrictions satisfy
`z a b + z b c = z a c` on every smaller triple-overlap open.
The actual unit cochain `unitCochain f T z` has entries `1 + ε*z a b`
on the inverse-image cover, using the actual section-ring equivalence
and actual projection map. The existing unit-cocycle equivalence turns
an additive cocycle into a multiplicative cocycle.

## Construction and zero-section trivialization

`CocycleGluing.gluedOneIso T hT` identifies the sheaf glued from the
constant unit cochain with the actual structure module. Its proof uses
the section `1` of the structure sheaf as a local frame on each open.
Multiplication by its restriction is the identity, and its transitions
are the unit cochain. The existing `frameIso`, inverted, gives the
claimed isomorphism. This auxiliary result works for an arbitrary
scheme and cover.

`pullbackCocycle_closedPoint_unitCochain` proves that the actual
zero-section pullback of every coefficient-unit cochain is the unit
cochain. This assertion needs neither a cover nor a cocycle condition.
For each overlap, the actual pullback cocycle applies the actual
`closedPoint.appLE` to the unit. The pulled-back overlap equals the
original overlap because `i ≫ p = 𝟙 X`. Transporting across this equality
identifies the map with `unitReduction`; the existing
`coefficientUnit_reduction` says its value is one.

`cocycleBundle f T hT z hz` is an actual `LineBundle Xε`:
its underlying module sheaf is `CocycleGluing.glued (unitCochain f T z)`.
Its local rank-one property is the proved gluing theorem, using the
inverse-image cover and the proved multiplicative cocycle condition.
There is no replacement line-bundle carrier or assumed presentation.

`cocycleBundleReductionIso f T hT z hz` is an actual isomorphism

```
(Scheme.Modules.pullback i).obj (cocycleBundle f T hT z hz).obj
  ≅ structureModule X.
```

It first applies the actual pullback gluing comparison `pullbackIso`,
then identifies the pulled-back transition cochain with the unit
cochain, then uses `gluedOneIso` on the pulled-back cover. Thus it proves
triviality of the actual pullback, rather than assuming a reduction
comparison.

## Tensor product and equality of isomorphism classes

`unitCochain_add` proves that adding coefficient cochains multiplies the
actual unit cochains. This follows entrywise from `coefficientUnit_add`
and does not require either cochain to be a cocycle.

`cocycleBundleTensorIso` identifies the actual sheaf tensor product of
the bundles of two cocycles `z` and `w` with the sheaf glued from
`unitCochain f T (z+w)`. It composes the existing actual gluing tensor
isomorphism with the equality `unitCochain_add`, in the appropriate
direction.

`isoClass_cocycleBundle_add` consequently states that the isomorphism
class of the bundle of `z+w` is the product of the two bundle classes.
It has an explicit proof parameter
`preservation : pullbackTensorComparisonIsIsoStatement` because this
is how the existing `LineBundle.IsoClasses` group records the tensor
preservation theorem. It also takes the cocycle proofs for `z`, `w`
and their sum. These parameters do not assume the deformation/H1
comparison; the actual tensor comparison of the glued bundles is
proved by `cocycleBundleTensorIso` without `preservation`.

`isoClass_cocycleBundle_eq_iff`, with the same tensor-preservation
parameter and cover hypothesis, states

```
isoClass (cocycleBundle z) = isoClass (cocycleBundle w)
  ↔ CechDegreeOne.IsCoboundary T (fun a b ↦ w a b - z a b).
```

The coboundary convention is `b_b| - b_a|`. The proof uses the quotient's
isomorphism criterion, forgets or lifts the actual line-bundle
isomorphism, and applies the existing arbitrary-unit-gauge criterion
`nonempty_iso_unitCochain_iff`. It imposes no compatibility with a
chosen reduction trivialization.

## Provenance and scope

These are internal applications of the proved actual coefficient-unit,
frame, pullback and tensor gluing constructions. Worker 509 authored
this specialization; Worker 207 authored the reused gluing
constructions. The module does not assert the final tangent-space or
rigidified Picard comparison. The ordinary deformation-class quotient,
its comparison with actual derived H1, rigidification and scalar
compatibility are subsequent obligations.

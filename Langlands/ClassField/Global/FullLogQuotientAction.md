# Natural quotient-unit action and the full logarithm

Let `E : Type v` be a number field, let `F : Type u` be a field, and give
`E` an `F`-algebra structure. Write `G = E ≃ₐ[F] E`,
`U = (𝓞 E)ˣ`, `T = NumberField.Units.torsion E`, and
`M₀ = fullLogUnitLattice E`. The universes `u` and `v` are independent.
No Galois or cyclicity hypothesis is needed. The quotient action itself
also makes sense without the number-field hypothesis.

This module descends the actual arithmetic action on `U` to `U/T` and
identifies its additive representation with the full logarithmic lattice.
The coefficient ring is the existing
`NormalizedTwoCocycle.CoefficientScalars.{v} = ULift.{v} ℤ`.

## Quotient action

`unitsModuloTorsionAut F E` is a group homomorphism from `G` to the
multiplicative automorphisms of `U/T`. For every actual unit `x`,

```text
unitsModuloTorsionAut F E g [x] = [g • x].
```

Here `g • x` is Mathlib's arithmetic action on ring-integer units,
installed locally through `Units.mulDistribMulActionRight`. A
multiplicative equivalence preserves the torsion subgroup
(`MulEquiv.map_torsion`), so `QuotientGroup.congr` descends this action.
The identity and composition laws are proved by quotient induction,
using the corresponding laws for the actual units.

`unitsModuloTorsionAction` packages these automorphisms as a
`MulDistribMulAction`. It is an explicitly named instance-reducible
definition, installed as an instance only locally in this module.
Thus no new global quotient-action instance is imposed.

## Equivariant logarithm

The previously constructed integer linear equivalence

```text
fullLogEmbeddingEquiv E : Additive (U/T) ≃ₗ[ℤ] M₀
```

has the exact actual-unit formula from `FullLogUnitLattice`.
`fullLogEmbeddingEquiv_equivariant` proves

```text
fullLogEmbeddingEquiv E (ofMul (unitsModuloTorsionAut F E g x.toMul))
  = fullLogUnitLatticeAut F E g (fullLogEmbeddingEquiv E x).
```

The proof chooses a representative of the quotient element, applies
subtype extensionality, and reduces the claim to the already proved
`fullLogEmbeddingToHyperplane_equivariant`. In particular, the lattice
action is the restriction of the genuine arithmetic permutation action
on full infinite-place coordinates, rather than an action defined by
transport across this equivalence.

## Representations and cohomology

`unitsModuloTorsionRepresentation F E` uses the existing
`coefficientRepresentation` for the above natural multiplicative
quotient action. Its carrier is `Additive (U/T)`, and its action is the
additive form of `unitsModuloTorsionAut`.

`fullLogUnitLatticeRepresentation F E` has carrier `M₀`. Its action is
`fullLogUnitLatticeAut F E`, regarded as linear over the lifted integer
coefficient ring by restriction of scalars. Both representations have
carrier universe `v` and group `G`; there is no identification of the
field universes.

`fullLogEmbeddingRepresentationIso F E` is an isomorphism in this
category of representations. Its underlying map is exactly
`fullLogEmbeddingEquiv E`; its linearity over the lifted integers is
obtained by scalar restriction, and its intertwining equation is the
equivariance theorem above. `Rep.mkIso` packages the linear equivalence
with this equation, retaining its inverse.

For every natural number `n`, `fullLogEmbeddingCohomologyIso F E n` is
an isomorphism of the actual ordinary group cohomology modules

```text
Hⁿ(G, unitsModuloTorsionRepresentation F E)
  ≅ Hⁿ(G, fullLogUnitLatticeRepresentation F E).
```

It is the image of the representation isomorphism under Mathlib's
`groupCohomology.functor`. This applies in all degrees, including zero.

## Provenance and scope

The source motivation is Milne, *Class Field Theory*, version 4.03
(2020), Chapter VII, proof of Proposition 3.1, printed p.209
(PDF page 218). That proof uses the equivariant unit logarithm, whose
kernel is the roots of unity and whose image is `M₀`. Here the set of
places is all infinite places, so its units are ordinary ring-integer
units. The source's normalized logarithms are implemented by the
previously constructed multiplicity-weighted full logarithm.

The explicit quotient automorphism homomorphism, categorical
representation isomorphism and all-degree cohomology isomorphisms are
derived adapters of that equivariant logarithm. They use the proved
kernel/image equivalence and arithmetic equivariance from the full-log
modules; they do not assume a Herbrand quotient identity.

This contribution does not compare the cohomology of `U` with that of
`U/T`: a further finite-torsion argument is needed for the Herbrand
calculation. It asserts neither cohomology finiteness nor a quotient
formula, and it does not prove `CyclicIdeleClassHerbrandQuotient`.

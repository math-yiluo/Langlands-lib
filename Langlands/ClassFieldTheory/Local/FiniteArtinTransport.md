# Fixed-equivalence transport of finite Artin families

Author: Worker 1232.

This internal construction pulls a supplied `FiniteArtinFamily K'` back to
`FiniteArtinFamily K` through one fixed compatible pair of field
equivalences. It proves preservation of `FiniteArtinSystemRelation`, which
includes the exact actual norm kernels, component surjectivity and all actual
finite-field restrictions. The source and target base fields may inhabit
independent universes.

## Supplied data and direction

Let `K` and `K'` be fields, and supply

```lean
eK : K ≃+* K'
eC : AlgebraicClosure K ≃+* AlgebraicClosure K'
h : (algebraMap K' (AlgebraicClosure K')).comp eK.toRingHom =
  eC.toRingHom.comp (algebraMap K (AlgebraicClosure K))
```

For the family construction, supply topologies on both base fields and
`heK : Continuous eK`. No topology on either algebraic closure is required.
No continuity assumption on `eK.symm` is needed for this direction of
transport. The finite automorphism groups carry their existing discrete
Krull topologies.

For an actual intermediate field `L` of `AlgebraicClosure K`,
`intermediateField eK eC h L` is the subfield of `AlgebraicClosure K'` whose
members have inverse image under `eC` in `L`. Its base-field containment
follows from `h`. `fieldEquiv` restricts this same `eC` to `L`, and
`fieldEquiv_compatible` proves its algebra-map square.

`finiteGaloisField` transports finiteness with
`Module.Finite.of_equiv_equiv` and the Galois property with
`IsGalois.of_equiv_equiv`. `galoisEquiv` conjugates automorphisms through a
compatible pair of field equivalences, permitting four independent field
universes. `extension` transports each actual `FiniteAbelianExtension K`
to an actual `FiniteAbelianExtension K'`; commutativity of its actual
Galois group follows from conjugacy and the source's commutativity.
`extensionGaloisEquiv` is the resulting continuous group isomorphism.
`extension_mono` preserves actual inclusions. This construction does not
assert an equivalence of the complete index types or a family round trip.

## One supplied family at every index

All declarations are in
`Langlands.LocalClassField.FiniteArtinTransport`. The main definition is

```lean
pullback eK eC h heK (a' : FiniteArtinFamily K') : FiniteArtinFamily K
```

At an actual index `L` and unit `b : Kˣ`, `pullback_apply` states exactly

```lean
pullback eK eC h heK a' L b =
  (extensionGaloisEquiv eK eC h L).symm
    (a' (extension eK eC h L) (Units.mapEquiv eK.toMulEquiv b))
```

The definition composes the unit map induced by `eK`, the indicated
component of the one supplied family `a'`, and inverse Galois conjugacy.
The unit map is continuous by `heK.units_map`; the two other maps are
continuous by their supplied or constructed continuous structures. There
is no choice of a different candidate family for different indices.

## Inverse-action evaluation

For the same supplied data, family, index and base unit, and any
`x : L.field`, `pullback_symm_apply` proves

```lean
fieldEquiv eK eC h L.field ((pullback eK eC h heK a' L b).symm x) =
  (a' (extension eK eC h L) (Units.mapEquiv eK.toMulEquiv b)).symm
    (fieldEquiv eK eC h L.field x)
```

The inverse of the conjugated automorphism is the conjugate of the
inverse. Unfolding the construction reduces the equality to cancellation
of `fieldEquiv` with its inverse. In particular, the inverse in the
geometric normalization clause requires no new choice of equivalence or
family.

`pullback_symm_sub_pow` combines this identity with the ring
equivalence's preservation of subtraction and natural powers. For every
`n : ℕ`, write
`eL : L.field ≃+* (extension eK eC h L).field` for the same `fieldEquiv`.
The image of
`(pullback eK eC h heK a' L b).symm x - x ^ n` is

```lean
(a' (extension eK eC h L) (Units.mapEquiv eK.toMulEquiv b)).symm
    (eL x) - (eL x) ^ n
```

Both formulas hold for an arbitrary supplied family without a
norm-residue, restriction, valuation or normalization hypothesis. They
compare actual field elements. Valuation comparison and identification
of the residue-cardinality exponent are separate inputs needed to use
them in a geometric normalization proof.

## Norm and restriction proofs

`normUnits_map` follows from Mathlib's determinant-norm identity
`Algebra.norm_eq_of_equiv_equiv`, applied to a compatible base and
extension equivalence. Equality of unit norms reduces to equality of
their underlying field elements. `mem_normSubgroup_map_iff` uses the
actual range definition of `normSubgroup` and bijectivity of the two unit
equivalences to preserve and reflect membership in the actual norm image.

`pullback_finiteNormResidueRelation` uses injectivity of Galois conjugacy
to identify its kernel with the preimage of the supplied component's
kernel. The preceding norm-image comparison identifies that preimage
with `normSubgroup K L.field`. For surjectivity, map the desired source
automorphism through conjugacy, choose a unit using the supplied target
component's surjectivity, and pull that unit back through `eK`.

`restrictionOfLE_apply_coe` obtains evaluation of the actual
`restrictionOfLE` by using the literal intermediate-field inclusion as
the algebra structure and applying `AlgEquiv.restrictNormal_commutes`.
`extensionGaloisEquiv_restriction` proves that conjugacy commutes with
these same actual restrictions: after coercing to the target closure,
both sides are `eC` applied to the same source automorphism evaluation.
`pullback_finiteArtinRestrictionRelation` then combines this square with
the supplied family's restriction equality at the two image indices.

Finally, `pullback_finiteArtinSystemRelation` combines component norm
relations and restriction coherence:

```lean
FiniteArtinSystemRelation a' →
  FiniteArtinSystemRelation (pullback eK eC h heK a')
```

## Provenance and scope

This is an internal transport construction derived from the existing
actual-field definitions in `FiniteArtin`, `Galois` and `Norms`, and from
the cited Mathlib declaration names. It makes no new claim attributed to
an external mathematical source. Its supporting proofs explain the
implemented transport directly.

The supplied family is an input. This module does not construct a local
Artin map, prove arithmetic existence, prove the geometric residue
normalization or prove uniqueness of geometric systems. Specialization
to a named arithmetic family, compatible model choices and comparison of
supplied valuation and residue data remain separate obligations for
`GeometricFiniteArtinSystemExistenceUniqueness`. The published target and
its imported Lean/Markdown pairs are unchanged.

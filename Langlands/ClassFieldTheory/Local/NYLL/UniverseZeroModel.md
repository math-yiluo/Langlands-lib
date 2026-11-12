# Universe-zero models of p-adic fields and their transport maps

This module, in namespace `Langlands.LocalClassField.NYLL`, constructs an
explicit universe-zero model of every p-adic field. It also constructs the maps
that move norm quotients, Galois groups and arithmetic data between a field and
its model. It is the model layer for the three published universe-transport
targets in [`UniverseTransportStatement`](UniverseTransportStatement.lean):

- `FiniteAbelianReciprocityUniverseTransportStatement`;
- `FiniteAbelianNormTransferUniverseTransportStatement`;
- `FiniteAbelianRestrictionUniverseTransportStatement`.

It proves none of those targets and constructs no reciprocity map. It assumes no
reciprocity property, no comparison premise and no new axiom.

## The model

| Declaration | Meaning |
| --- | --- |
| `padicField_small F` | `Small.{0} F.Carrier`, from Mathlib's `Module.Finite.small`: `F.Carrier` is a finite module over `Padic p`, which lies in `Type 0`. |
| `universeZeroModel F : PadicField.{0} p` | The carrier is `Shrink.{0} F.Carrier`. Its `Field` and `Algebra (Padic p)` structures are Mathlib's instances transported along `equivShrink`. Finite dimensionality over `Padic p` is transported along `Shrink.algEquiv`. |
| `universeZeroEquiv F` | Mathlib's `Shrink.algEquiv (Padic p) F.Carrier`. It is an actual `Padic p`-algebra equivalence from `(universeZeroModel F).Carrier` to `F.Carrier`. |
| `universeZeroAlgebra F E` | Given the supplied `Algebra F.Carrier E.Carrier`, this is the algebra structure on the models whose map is `(universeZeroEquiv E).symm ∘ algebraMap F.Carrier E.Carrier ∘ universeZeroEquiv F`. It is a definition, not a global instance. Consumers install it locally. |

`F` and `E` have independent universes `u` and `v`. Each field has one model and
one model equivalence, whatever extension it appears in. Every field map is
transported by the same conjugation. For a tower `F ⊆ E ⊆ L` with supplied maps
`F → E`, `F → L` and `E → L`, the three transported maps therefore form a tower
again. The scalar inclusion `F → E` and the field norm `E → F` are transported
separately, so their directions are kept.

## Transported structure

With `universeZeroAlgebra` installed locally:

- `universeZeroEquiv_algebraMap` and `universeZeroEquiv_symm_algebraMap`: the
  model equivalences and their inverses intertwine the transported and supplied
  field maps.
- `universeZeroAlgebra_compatible` and `universeZeroAlgebra_symm_compatible`
  state the same relations as ring-homomorphism equalities. This is the form
  taken by `FiniteArtinTransport.galoisEquiv` and Mathlib's `*_of_equiv_equiv`
  lemmas.
- `universeZeroAlgebra_isScalarTower`: `IsScalarTower (Padic p)` passes from
  the supplied extension to the models.
- `universeZeroAlgebra_finiteDimensional` transports finite dimensionality,
  using `Module.Finite.of_equiv_equiv`.
- `universeZeroAlgebra_finrank`: the model degree equals the supplied degree,
  using `Algebra.finrank_eq_of_equiv_equiv`.
- `universeZeroAlgebra_isAbelianGalois` transports abelian Galois extensions.
  Galois follows from `IsGalois.of_equiv_equiv`. Commutativity follows from the
  injective conjugation homomorphism `FiniteArtinTransport.galoisEquiv`.
- `universeZeroAlgebra_isScalarTower_tower`: for supplied maps with
  `IsScalarTower F.Carrier E.Carrier L.Carrier`, the three transported maps
  satisfy `IsScalarTower` on the models.

## Galois groups

`universeZeroGaloisEquiv F E` requires `FiniteDimensional F.Carrier E.Carrier`.
It is an isomorphism of topological groups, `≃ₜ*`, between the actual group
`Gal((universeZeroModel E).Carrier/(universeZeroModel F).Carrier)` and
`Gal(E.Carrier/F.Carrier)`. Its multiplicative equivalence is the published
`FiniteArtinTransport.galoisEquiv`, applied to the two model equivalences: σ is
sent to `universeZeroEquiv E ∘ σ ∘ (universeZeroEquiv E).symm`. Both groups carry
Mathlib's Krull topology, which is discrete for finite extensions. The two maps
are therefore continuous.

The following lemmas give the action:

- `universeZeroGaloisEquiv_apply` describes the automorphism.
- `universeZeroGaloisEquiv_apply_symm` describes the inverse automorphism `.symm`.
- `universeZeroGaloisEquiv_symm_apply` describes the inverse identification.

The next two lemmas describe compatibility with towers:

- `universeZeroGaloisEquiv_restrictScalars`: for `τ` in the model group of the
  top extension over the middle field, transporting `τ.restrictScalars` over
  `F` gives the restriction of scalars of the transported `τ`. This is the
  Galois inclusion used by the norm and transfer diagrams.
- `universeZeroGaloisEquiv_restrictNormalHom`: if both middle fields are normal
  over their bases, transport commutes with `AlgEquiv.restrictNormalHom`. This
  is the restriction used by the tower diagram.

## Norm quotients

- `universeZeroEquiv_norm`: `universeZeroEquiv F` carries the actual model norm
  `Algebra.norm (universeZeroModel F).Carrier` to the actual norm
  `Algebra.norm F.Carrier` of the supplied extension. This is Mathlib's
  `Algebra.norm_eq_of_equiv_equiv`.
- `universeZeroNormRange_map`: the units map of `universeZeroEquiv F` carries the
  range of the model's `Units.map (Algebra.norm …)` onto the range of
  `Units.map (Algebra.norm F.Carrier (S := E.Carrier))`.
- `universeZeroEquiv_continuous T₀ T`: the model equivalence and its inverse are
  continuous for arbitrary supplied data `T₀` on the model and `T` on `F`. Both
  topologies are module topologies over `Padic p`. Linear maps out of a module
  topology are continuous (Mathlib's `IsModuleTopology.continuous_of_linearMap`).
- `universeZeroNormQuotientEquiv F E T₀ T` is an isomorphism of topological
  groups, `≃ₜ*`. Its source is the actual norm quotient of the model extension,
  with the quotient topology induced by `T₀.topology`. Its target is the actual
  quotient
  `F.Carrierˣ ⧸ (Units.map (Algebra.norm F.Carrier (S := E.Carrier))).range`
  used by the host statements, with the quotient topology induced by
  `T.topology`. The group isomorphism is Mathlib's `QuotientGroup.congr`,
  applied to the units map of `universeZeroEquiv F`. Continuity in both
  directions follows from the quotient-map property of `QuotientGroup.mk`.
- `universeZeroNormQuotientEquiv_mk` and `universeZeroNormQuotientEquiv_symm_mk`
  describe both directions on classes of units.

## Arithmetic data of supplied topological data

Let `e : F.Carrier ≃ₐ[Padic p] F'.Carrier` be an algebra equivalence between
p-adic fields in independent universes `u` and `u'`. Let `T : F.TopologicalData`
and `T' : F'.TopologicalData` be arbitrary. The section proves three equalities,
each including the convention at zero:

- `residueCardinality_eq_of_algEquiv`: `T'.residueCardinality = T.residueCardinality`;
- `ord_eq_of_algEquiv`: `T'.ord (e x) = T.ord x`;
- `discreteValuation_eq_of_algEquiv`: `T'.discreteValuation (e x) = T.discreteValuation x`.

These lemmas compare arbitrary supplied data `TF` and `TE` with any data used on
the models, for example `PadicField.canonicalTopologicalData`. The proof reuses
published Library results.

- Residue cardinality. `FiniteArtinSystemUniqueness.residueCardinality_eq_canonical`
  shows that any supplied data have the canonical residue cardinality.
  `PadicField.CanonicalTransport.residueCardinality_eq` shows that the canonical
  residue cardinality is preserved by `e`.
- Order. `TopologicalData.normalizedAbs_eq_canonicalNorm_pow_degree` writes the
  normalized absolute value of arbitrary data as
  `canonicalNorm x ^ finrank (Padic p) F.Carrier`. `Weil.Local.canonicalNorm_map`
  shows that algebra maps preserve the spectral norm, and `e` preserves the
  degree. Since `normalizedAbs x = q ^ (-ord x)` with `q > 1`, the orders agree.
- Discrete valuation. It is `exp (-ord)` away from zero.

The order and valuation arguments follow `CanonicalTransport.ord_map` and
`CanonicalTransport.discreteValuation_map`, which prove the canonical-data case.
These lemmas extend them to arbitrary supplied data and to two independent
universes.

## Provenance and design

These are internal formalization constructions authored by Worker 11. They are
not attributed as definitions of the external literature. Mathematically they
are transport of structure along explicit field isomorphisms. The design follows
unit 3(b) and API problem 1 (section 5) of the
[NYLL source audit](../../../../notes/reuse/nyll-finite-local-reciprocity-audit.md),
and the universe-transport boundary in section 7 of the
[port-feasibility report](../../../../notes/reuse/nyll-port-feasibility.md).

The audit lists NYLL's `ShrinkTransport` route: it moves the valuative relation,
the topology and `IsNonarchimedeanLocalField` to `Shrink.{0} K`. Some adapted
pieces of it are in the Library under `Langlands.NYLL`, for example
`shrinkLocalFieldValuation` and `shrinkLocalFieldValuativeRel`. This module does
not use them; it takes a smaller replacement route.
`Shrink` is used only for the algebraic model, and smallness comes from finite
dimensionality over `Padic p`. No valuation or topology is transported. Every
model is a `PadicField`, so it already has `PadicField.canonicalTopologicalData`
and any other supplied topological data. The lemmas in the arithmetic section
compare those data with the original supplied data. The module copies no NYLL
code and needs no NYLL license header.

The universe-transport proofs are expected to take the following route. They are
separate proof tasks and are not proved here.

1. Install the transported algebra structures and their scalar-tower,
   finite-dimension and abelian-Galois facts.
2. Apply the Type 0 statement to the models with canonical topological data.
3. Conjugate the resulting witnesses by `universeZeroNormQuotientEquiv` and
   `universeZeroGaloisEquiv`.
4. Translate each clause with the lemmas above.

Every host field, map, quotient and Galois group stays the actual supplied one.
This module provides no global coherent-system uniqueness, cohomological
comparison or Weil-group component.

# Semisimplicity and finite coordinate transport

This internal helper module compares two definitions of semisimplicity and
transports representations to finite coordinate spaces. Its namespace is
`Langlands.RepresentationSemisimpleTransport`.

## Invariant subspaces and semisimplicity

Let `k : Type u` be a field, `G : Type v` a monoid, and `V : Type w₁` and
`W : Type w₂` be `k`-vector spaces. The four universes are independent.
Neither finite dimension nor characteristic zero is required in this part.

For `ρ : Representation k G V` and `U : Submodule k V`, `IsStable ρ U`
means that `ρ g v` belongs to `U` whenever `v` belongs to `U`, for every
`g : G`. The predicate `IsSimple ρ U` means that `U` is stable and nonzero,
and that every stable subspace contained in `U` is either zero or `U`.
The construction `subrepresentation ρ U hU` bundles a stable subspace as a
Mathlib subrepresentation.

`isSimple_iff_isAtom` identifies this predicate on the underlying subspace
of a subrepresentation with being an atom in the order of
subrepresentations. The proof applies the minimum property in each
direction, using injectivity of the underlying-subspace map.

`isSemisimple_iff_sSup_simples` proves

```text
ρ.IsSemisimpleRepresentation ↔
  sSup {U : Submodule k V | IsSimple ρ U} = ⊤.
```

Here Mathlib's left-hand predicate says that every subrepresentation has a
complement. The proof uses
`Subrepresentation.subrepresentationSubmoduleOrderIso` to identify simple
subrepresentations with simple `k[G]`-submodules of `ρ.asModule`. It then
applies `sSup_simples_eq_top_iff_isSemisimpleModule` and the equivalence of
semisimple representations with semisimple group-algebra modules.
Restriction of scalars from `k[G]` to `k` preserves the supremum and
reflects equality with the top submodule. This gives precisely the displayed
sum of invariant subspaces, including the zero-space case.

## Equivariant transport

`isSemisimple_iff_of_equiv` proves that an equivariant linear equivalence
`e : ρ.Equiv σ` preserves and reflects semisimplicity. It applies
`LinearMap.isSemisimpleModule_iff_of_bijective` to the bijective
group-algebra-linear map associated to `e.toIntertwiningMap`.
The carriers of `ρ` and `σ` may lie in different universes.

For an arbitrary linear equivalence `e : V ≃ₗ[k] W`, the representation
`coordinates ρ e` is conjugation of `ρ` by `e`. Thus its action on `w` is
`e (ρ g (e.symm w))`. Preservation of the identity and multiplication
comes from composition of monoid homomorphisms.
`coordinatesEquiv ρ e` is the resulting equivariant linear equivalence;
its intertwining law follows by cancelling `e.symm (e v)`.
`isSemisimple_coordinates_iff` applies the preceding transport theorem.

`tensorEquiv e f` tensors two equivariant linear equivalences. Its
underlying linear equivalence is `TensorProduct.congr`, and its
intertwining law is supplied by the tensor of the two intertwining maps.
The four carrier universes are independent.

## Finite coordinates and the conditional tensor reduction

When `V` is finite-dimensional, `finiteCoordinates ρ` transports `ρ`
along `(Module.finBasis k V).equivFun` to
`Fin (Module.finrank k V) → k`. The definition
`finiteCoordinatesEquiv ρ` bundles this equivalence.
The coordinate index lies in universe zero, regardless of the universe of
`V`. A dimension of zero is allowed.

The theorem `tensor_semisimple_of_coordinates` assumes the tensor
semisimplicity result for all pairs of representations of the same monoid
on `Fin n → k` and `Fin m → k`, where the tensor action on product
coordinates is `CoordinateTensor.representation`. Under that hypothesis it
proves tensor semisimplicity for arbitrary finite-dimensional carriers
`V` and `W`. The proof transports both semisimplicity hypotheses to finite
coordinates, applies the assumed coordinate result, and transports the
conclusion back through `tensorEquiv` followed by
`CoordinateTensor.equiv`. The universes of the coefficient field, monoid,
and original two carriers remain independent.

## Provenance and scope

These are internal constructions and lemmas derived from Mathlib's
subrepresentations, semisimple modules, linear equivalences, finite bases,
and tensor products. The product-coordinate comparison is the published
`Langlands.Representation.Tensor.Coordinates` construction, used by its
Lean names. No additional correspondence with external literature is
claimed. This module proves the conditional coordinate reduction, without
assuming or proving the characteristic-zero abstract-group tensor
semisimplicity statement.

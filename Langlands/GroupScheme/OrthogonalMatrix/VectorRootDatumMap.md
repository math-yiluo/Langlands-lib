# Vector morphism from the actual split orthogonal root datum

This internal construction works over an arbitrary field `k : Type u`, in every characteristic. Let `n ≥ 4`. Let `Q` be a finite reduced root datum on the actual character and cocharacter lattices of the standard split orthogonal torus, with `IsRootDatumOf (identityTorus (Fin n) k) Q`. Let `P : RootDatum I X Y` be a finite reduced integral root datum, let `B : P.Base`, and assume `P.corootSpan ℤ = ⊤`. A numbering `e : B.support ≃ Fin n` must identify all pairings on the supplied base with `CartanMatrix.D n` in exactly that order.

`OrthogonalMatrix.TypeDNumbering.vectorHom` chooses a morphism `Q → P`. Its `vectorHom_spec` proves that both its weight map and its contravariant coweight map are injective. On the simple indices, its index equivalence agrees with the numbered orthogonal base followed by `e.symm`. Its full integral weight-map image is

```text
P.rootSpan ℤ ⊔ Submodule.span ℤ
  {Langlands.RootDatum.fundamentalWeightBasis P B hspan (e.symm 0)}.
```

Here `0` is the first element of `Fin n`. In particular the assertion retains the specified vector vertex for D₄, without a relabeling of the terminal vertices. `exists_vectorHom` gives the existential form with the same specifications. `exists_vectorRootDatum` also supplies a finite reduced actual orthogonal datum and a morphism with the two injectivity assertions and the same image equality. It uses the actual root-datum existence theorem over the field; it places no restriction on the characteristic.

The construction first applies the canonical full-coroot root datum to `Q`. The published orthogonal coroot quotient is finite, so the induced-base constructor applies and both canonical lattice maps are injective. The Cartan-preserving comparison theorem for finite reduced full-coroot data identifies this induced datum with `P`, extending the specified simple-index bijection. Composing gives `exists_numberedHom` and then the chosen morphism.

The image calculation is integral throughout. For `n ≥ 3`, `map_rootSpan_eq_pairLattice` identifies the actual orthogonal root span with the coordinate parity lattice, using the equality of root and coroot coordinates and the published coroot-lattice calculation. Subtracting the sum of a character's coordinates times its first coordinate character leaves a vector in that parity lattice. Consequently `rootSpan_sup_firstCoordinate` shows that roots and this first character generate the whole orthogonal character lattice.

For any morphism respecting the simple numbering, `weightMap_firstCoordinate` identifies the image of this character with the fundamental weight at vertex zero. The transpose relation reduces its pairing with each simple coroot of `P` to the orthogonal coordinate pairing. The first coordinate of a numbered simple vector is one precisely at simple index zero and zero elsewhere. These are exactly the pairings of the claimed fundamental weight; the full-coroot hypothesis makes the simple coroots separate weights. Finally `map_rootSpan` uses the morphism's bijection on all roots to identify the image of the root span with `P.rootSpan ℤ`. Mapping the preceding generation equality gives `range_weightMap` and the full image in `vectorHom_spec`.

The provenance is internal: the construction combines the actual split orthogonal root and coroot formulas, its finite coroot quotient, the induced full-coroot base, the Cartan comparison, and the dual-basis definition of fundamental weights. It does not assert an algebraic-group quotient, a spin cover, descent, or the parent aligned-spin-cover statement. Those require subsequent geometric constructions.

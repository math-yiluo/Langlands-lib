# The simple roots of the coordinate root datum of `Sp_{2n}`

Lean module: `Langlands.GroupScheme.SymplecticMatrix.TypeCPinningSimpleRoots`
(namespace `Langlands.GroupScheme.SymplecticMatrix.TypeCPinning`).

This internal companion of `SymplecticMatrix.TypeCPinning` (Worker 31, Task 5986) records the
coordinates of the simple roots of the coordinate root datum of `Sp_{2n}`. The proof of
`TypeCDistinguishedVerticesStatement` needs them to match the simple roots with the relative
roots of `SU(D, h)`. `TypeCPinning` is unchanged. Notation as there: `𝔻` is the split torus on
`ULift (Fin n)` over `Spec k`, the source of the diagonal torus of `Sp_{2n}`, and
`weightCoord (Fin n)` gives the coordinates `e_a` (on `inl a`) and `-e_a` (on `inr a`) of the
weights of the diagonal torus. `simpleSnd i` is `inl (i + 1)` for `i + 1 < n` and `inr i`
otherwise.

## Results

* `weightCoord_inl_sub_simpleSnd i`: the coordinates
  `weightCoord (inl i) - weightCoord (simpleSnd i)` equal `e_i - e_{i+1}` if `i + 1 < n`, and
  `2 e_i` otherwise (the explicit `if` form in Lean). The proof unfolds `simpleSnd` and uses
  `weightCoord_inl` and `weightCoord_inl_sub_inr`.
* `exists_coordinateRootDatum_simpleRoots n k` (over any field `k`): there are a finite index
  type `J`, a root datum `P` with character lattice and cocharacter lattice those of `𝔻`, which
  is a root datum of `diagonalTorus (Fin n) k` (`IsRootDatumOf`) and reduced, a base `B` of `P`
  and a numbering `e : B.support ≃ Fin n`, such that
  * the coroots span the cocharacter lattice (`P.corootSpan ℤ = ⊤`);
  * `P.pairing a b = CartanMatrix.C n (e a) (e b)` for simple `a, b`;
  * for every simple `a`, `GeneralLinear.characterCoordEquiv (Fin n) k (P.root a)` equals
    `weightCoord (inl (e a)) - weightCoord (simpleSnd (e a))`.

  The first two conjuncts, and everything before them, are the statement of
  `TypeCPinning.exists_coordinateRootDatum`. The third conjunct is new.

## Proof

The proof is that of `exists_coordinateRootDatum`, which establishes the third conjunct along
the way and then drops it. `exists_rootDatum` gives the reduced root datum of the diagonal
torus. `RootDatumCoweightFace.exists_base_support` with the regular cocharacter
`regularCochar n k` gives a base `B`, whose support consists of the roots of the form
`e_i - (simpleSnd i)` (`mem_baseOf_iff`). Choosing such an `i` for each simple root gives `g`.
It is injective since roots are determined by their coordinates. It is surjective because each
`e_i - (simpleSnd i)` is a root (`exists_root_of_ne`, `inl_ne_simpleSnd`) and
`simple_injective` applies. `corootSpan_eq_top` and `pairing_simple` give the first two
conjuncts, and the choice of `g` gives the third.

## Provenance

In the standard numbering of the root system of type `C_n` (Bourbaki, *Lie Groups and Lie
Algebras*, Ch. VI, Plate III), the simple roots are `e_i - e_{i+1}` (`i < n - 1`) and `2 e_{n-1}`
(indices from `0`). This module only exposes the corresponding fact already established inside
the proof in `TypeCPinning`. It was written for Task 6244 at the request of the first executor,
Worker 244.

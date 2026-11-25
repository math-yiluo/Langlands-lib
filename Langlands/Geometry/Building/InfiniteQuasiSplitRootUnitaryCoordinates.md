# Actual unitary root coordinates over infinite fields

This module proves existence of one-sign `RootUnitaryCoordinates` for every
multipliable root of an actual affine quasi-split group over an infinite field.
The fields, rational-point coordinates and full-centralizer character are
outputs. No quotient package, Heisenberg normal form, splitting field or root
datum is supplied to the main theorem.

Provenance: internal. This is a composition of the actual-root separation
construction in `ActualRootHeisenbergSeparation` with the published existence
results for root quotients, equivariant Heisenberg normal forms, finite Galois
splitting fields, absolute root data and relative root systems. The statement is
the published `QuasiSplitR2RootUnitaryCoordinatesStatement` restricted to infinite
base fields. It is introduced here as an internal proposition so that this
restriction and its proof can be reviewed without changing the published
all-field target. No new assertion from the original literature is introduced.

All declarations are in `Langlands.Geometry.Building`, at an arbitrary universe
parameter `u`.

## Statement and output

`InfiniteQuasiSplitR2RootUnitaryCoordinatesStatement : Prop` quantifies over:

- an infinite field `k : Type u`;
- an actual affine group scheme `G` over `k`, with `IsQuasiSplit G`;
- a prescribed commutative group scheme `S` and inclusion `i : S.toGrp -> G`
  satisfying `IsMaximalSplitTorus i`;
- any group scheme `Z` and map `j : Z -> G` representing the full all-test
  torus centralizer of `i`;
- any factor `s : S.toGrp -> Z` with `s >> j = i`;
- any character `a` for which both `a` and `2*a` are actual relative roots of
  `i`.

Its conclusion is `Nonempty (RootUnitaryCoordinates i j s a)`. Thus the
conclusion uses the prescribed torus, the supplied centralizer presentation and
its supplied factor. The structure includes finite separable fields in a tower
`k -> E -> L`, with `L/E` separable quadratic, and a group isomorphism

```
SU3Root.rationalParameters E L ≃* rootGroupPoints i a.
```

The parameter group consists of pairs `(x,y)` with `y + conjugate(y) =
x * conjugate(x)`, with product
`(x,y)(x',y') = (x+x', y+y'+x*conjugate(x'))`. Parameters with first coordinate
zero identify precisely the actual rational root subgroup at `2*a`.

The output also includes an actual character of the base change `Z_L`,
restricting along `s_L` to the base change of `a`. Conjugation by every `z` in
`Z(k)` acts in these coordinates by

```
(x,y) ↦ (lambda*x, lambda*conjugate(lambda)*y),
```

where `lambda` is the value of that character on the scalar extension of `z`.
These are exactly the fields and laws of the imported `RootUnitaryCoordinates`
structure; the result asserts rational-point coordinates.

## Construction in a fixed split presentation

`nonempty_rootUnitaryCoordinates_of_torusCentralizer` is the helper with fixed
fields `k` and `L`, a commutative-group map `f : S -> T`, and `j : T.toGrp -> G`.
Write `i = CommGroupScheme.groupHom f >> j`. Besides infinitude of `k` and a
finite Galois extension `L/k`, it assumes:

- `G` is affine, smooth and locally of finite type, and is connected reductive;
- `T` is affine and locally of finite type, `j` is a closed subgroup, `i` is a
  maximal split torus, and `j` represents its full torus centralizer;
- `T_L` is split and a root datum of `j_L` is supplied, indexed by a finite
  type in universe `u`;
- `a` and `2*a` are relative roots of `i`, while `n*a` is not a relative root
  for every natural number `n >= 3`.

It concludes `Nonempty (RootUnitaryCoordinates i j
(CommGroupScheme.groupHom f) a)`. The proof makes the following constructions.

1. Splitness of `S` follows from maximal splitness of `i`. Nonzeroness of `a`
   follows from its membership in the relative roots. The published
   `nonempty_quotientPackage` constructs the represented root group, doubled
   root group, affine quotient and commutator pairing.
2. The weight-vector coordinates for `2*a` give the affine instance required
   on the doubled root group. Their hypotheses follow from nonzeroness of
   `2*a` and the supplied bound on higher multiples.
3. The centralizer property makes conjugation by `T` fix `i(S)` on every test
   scheme. The finite splitting presentation proves `T` is a torus.
   `nonempty_equivariantHeisenbergNormalForm` now constructs an equivariant
   normal form for the actual commutator pairing; its action through `f` is
   the actual conjugation action.
4. `hasActualRootHeisenbergSeparationData` constructs the actual quadratic
   stabilizer fields, coordinate maps, nonsymmetric homogeneous cocycle and
   separating character values from these structural hypotheses. The imported
   `toHeisenbergUnitaryData` and `rootUnitaryCoordinates` convert this datum
   into the required one-sign unitary coordinates.

## Main proof

`infiniteQuasiSplitR2RootUnitaryCoordinates` proves the displayed proposition.
First it substitutes the equality `s >> j = i`. The published quasi-split
centralizer theorem, using maximal split torus conjugacy, proves the supplied
centralizer `Z` is a torus. Connected reductivity gives smoothness and local
finite type of `G`. The represented centralizer is a closed subgroup.

The proof equips `Z` with its commutative torus structure, producing `T`, and
regards `s` as a commutative-group map `f : S -> T`. The closed inclusion gives
affineness and local finite type of `T`. Since `j` represents the centralizer
of `s >> j` and its source is commutative, the centralizer of `j` is precisely
its range. This self-centralizing property identifies `j` as a maximal torus
after base change.

The finite-Galois torus-splitting theorem chooses a splitting field `K/k`.
Connected reductivity after algebraic extension and the published root-datum
existence theorem choose a finite absolute root datum over `K`. Finally, the
published `relativeRootSystem` theorem for the prescribed maximal split torus
rules out every `n*a` with `n >= 3`. The fixed-presentation helper applies with
these internally chosen data.

## Scope

Infinitude of `k` is an explicit hypothesis, used by the imported
character-value separation construction. There is no field-characteristic
restriction, including in characteristic two, and no valuation, henselianity,
residue-field or topology hypothesis.

The module constructs coordinates for the one sign `a` and its double. It does
not assert compatibility with coordinates for `-a`, a homomorphism from an
actual SU3 group, a coroot comparison, Weyl compatibility or affine-root lifts.
In particular it does not prove the all-field
`QuasiSplitR2RootUnitaryCoordinatesStatement` or
`QuasiSplitIndivisibleDerivativeLiftsStatement`.

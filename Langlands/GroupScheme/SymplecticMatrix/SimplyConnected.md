# The split symplectic group over a field is simply connected

This internal module proves that the split symplectic group `SymplecticMatrix.groupScheme l k`
over a field `k` is simply connected, in the sense of the Library's `IsSimplyConnected`.
That structure bundles `IsSemisimple` with the condition that every central isogeny from a
semisimple group is an isomorphism. The module then transports the result to the standard
model `Symplectic.groupScheme K n`. Let `𝔻` be the split torus
`splitTorus.commGroupScheme (Spec k) (ULift l)`, the source of `diagonalTorus l k`
(`SymplecticMatrix.Torus`). No assumption is made on `l` (it may be empty) or on the
characteristic.

## Long coroots

Coordinates of cocharacters are the Library's `GeneralLinear.cocharacterCoordEquiv l k`.
Under these coordinates, `latticePairing` is the dot product (`GeneralLinear.latticePairing_coord`).

* `latticePairing_longRoot`: the long root `2e_b` (`longRoot l k b`, from
  `SymplecticMatrix.Roots`) pairs with a cocharacter `ν` to `2 ν_b`.
* `cocharacterCoordEquiv_coroot_of_root_eq_longRoot` (**long coroots**): let `P` be a root
  datum of the diagonal torus (`IsRootDatumOf (diagonalTorus l k) P`), and `j` an index with
  `P.root j = 2e_a`. Then `P.coroot j` has coordinates `e_a`. Proof: let `ν = P.coroot j`.
  The pairing of `P` is `latticePairing`, so `2 = ⟨2e_a, ν⟩ = 2 ν_a` and `ν_a = 1`. For
  `b ≠ a`, the long root `2e_b` is `P.root j'` for some `j'` (`longRoot_mem_roots`). Put
  `p = ⟨2e_b, ν⟩ = 2 ν_b`. The reflection of `2e_b` in `2e_a` is again a root of the torus,
  with coordinates `2e_b - p · 2e_a`. Its coordinate at `b` is `2`, so by
  `eq_single_two_of_mem_roots` it equals `2e_b`. Comparing coordinates at `a` gives
  `2p = 0`, so `ν_b = 0`.
* `corootSpan_eq_top` (**coroot span**): for every such root datum, `P.corootSpan ℤ = ⊤`.
  The coroots of the long roots `2e_a` form the standard basis `e_a` of the cocharacter
  lattice, transported along `cocharacterCoordEquiv`.

## Simple connectedness

* `exists_rootDatum l k`: the diagonal torus has a reduced root datum. This is the Library's
  `rootDatumExistence` for the connected reductive group `groupScheme l k`
  (`isConnectedReductive`) with the split maximal torus `diagonalTorus l k`
  (`isSplitTorus_diagonalTorus`, `isMaximalTorus_diagonalTorus`).
* `isSimplyConnected l k` (**simple connectedness**): `groupScheme l k` is simply connected.
  Take a root datum `P` from `exists_rootDatum`. The group is semisimple by the Library's
  `splitSemisimpleRootDatum`, which says that a split connected reductive group is semisimple
  exactly when `Y(T) ⧸ P.corootSpan ℤ` is finite. Here the quotient is by `⊤`
  (`corootSpan_eq_top`), so it is finite. The Library's `splitCorootSpanSimplyConnected`
  then gives simple connectedness from `P.corootSpan ℤ = ⊤`. Semisimplicity is proved inside
  this proof, not as a separate declaration. It is available as the `isSemisimple` field of
  the result.
* `Symplectic.isSimplyConnected_groupScheme K n`: the standard symplectic group
  `Symplectic.groupScheme K n` over a field `K` is simply connected. This transports
  `isSimplyConnected (Fin n) K` along the Library's isomorphism
  `SymplecticMatrix.comparisonIso K n` (`SymplecticMatrix.StandardComparison`), using
  `IsSimplyConnected.of_iso`. It holds for every `n`, including `n = 0` and `n = 1`.

## Provenance

The simple connectedness of `Sp_{2n}` is standard. Milne, *Algebraic Groups* (2017),
Summary 21.98 (printed p. 460), states that the split symplectic group of the type `C_n` root
system is simply connected, because its character lattice is the weight lattice. This module
is internal, and the proof is written from the cited Library results. It uses the coroot criterion: the coroots of the
long roots `2e_a` are the basis `e_a^∨` of the cocharacter lattice. It does not compute the
root system or the Weyl group explicitly.

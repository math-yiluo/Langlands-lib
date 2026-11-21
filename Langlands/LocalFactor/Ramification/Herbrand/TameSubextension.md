# Herbrand rescaling across a tame totally ramified subextension

`TameSubextensionHerbrandStatement` concerns an actual finite intermediate
field `E` of the fixed algebraic closure of a p-adic field `K`. Its degree
`m` is computed along the literal embedding. Its residue degree must be
one and its degree prime to `p`; the field need not be Galois over `K`.

The first assertion is `relativeHerbrandPsi E v = m * v` for nonnegative
real `v`. The second is an equality of subgroups of the actual Weil group
of `K`: for `v > 0`, the image of `W_E^{m v}` under `intermediateWeilMap`
is `W_K^v`. This assertion about strictly positive indices does not
identify the two inertia groups at index zero.

**Derived provenance.** J.-P. Serre, *Local Fields* (1979), IV §2,
Corollary 3 (printed pp. 67–68), and IV §3, the floor formula on p. 73
and Remark 2 after the proof of Proposition 14 on p. 75 (PDF pp. 80, 82).
In a finite Galois field containing `E`, the first lower group over `K`
is a normal `p`-group, so it is contained in the automorphisms fixing `E`,
a subgroup of index prime to `p`. Positive lower groups thus agree under
restriction and the zeroth orders have ratio `m`. This rescales the
positive Herbrand function; Serre's relative formula then gives the
stated inverse index. Taking the actual absolute upper filtration and
pulling it back to Weil groups gives the second assertion. This module
states the compatibility, not a conductor or representation identity.

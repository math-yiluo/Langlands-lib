# Global Jacquet–Langlands for the Harris division algebra

`Langlands.Shimura.HarrisClozel.HarrisClozelGlobalJLStatement` is the division-group
step. The input is a central simple datum `D` with second-kind involution on the
actual degree-`r+1` algebra `A` over the CM center `E`. The algebra is a division
algebra, division locally at the two distinct places `v` and `conjPlace E v`, and
split at all other finite places. The source is a cuspidal realization `S` of
`GL_(r+1)` over `E` with an irreducible admissible spectral presentation `P`,
square-integrable at both places. The input unitary character and form for
`S` are those for its actual adelic Hilbert completion. The source must be
trivial on the positive diagonal split center, in the sense of
`CuspidalPairPoles.IsTrivialOnSplitCentre S`: its forms are invariant under
scalar ideles whose finite component is 1 and whose infinite values are all
the same positive real number.

The output is one nonzero closed irreducible invariant subspace of the actual
right regular `L²` on the canonical positive split-center quotient for the unit
group of `A` over `E`. The existing connected-reductive and split-torus-character
inputs give this action. At each finite place an irreducible admissible
constituent embeds equivariantly in the restriction of this same subspace by
the actual place inclusion. At the two division places it satisfies
`completionJacquetLanglandsPair` with the source at that place, in an algebra
chart on the actual completed algebra. At every other finite place an actual
matrix-algebra chart identifies it with the source local component. At infinity,
the actual matrix chart on the scalar extension to the infinite adele ring
gives a common irreducible closed constituent of the two archimedean
restrictions; there is no claim equating their multiplicity spaces.

## Provenance and boundary

This is the narrow existence part of Clozel 1991, *Représentations galoisiennes
associées aux représentations automorphes autoduales de GL(n)*, §3.1, Theorem
3.3(i), p. 108, used for a conjugate pair in §5.3, pp. 142–144. The split
local relation at any complex place is the ordinary identification of the
split groups. The target quotient kills the positive diagonal, so unitary
central character alone would not suffice for matching at infinity. In
Clozel's CM application, the positive diagonal is fixed by CM conjugation;
conjugate self-duality makes the character there equal to its inverse, and
continuity on the connected positive reals forces it to be trivial.
The statement specifies the target using the Library's actual
scalar-extension, quotient and local representation APIs. The two-place
hypothesis is already imposed; this comparison does not construct the division
algebra. Nor does it assert strong multiplicity one, stability under the
involution, stable descent to the unitary group, or extension to similitudes.
The latter steps must compare the same target of the global transfer with a
unitary and then a similitude representation. The arithmetic fields and
representation carriers are in `Type 0`, as at the native PEL boundary.
Only the interface, not a proof of global transfer, is given here.

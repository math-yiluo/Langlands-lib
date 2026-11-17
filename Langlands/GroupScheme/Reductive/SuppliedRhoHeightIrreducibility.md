# Entire-space Steinberg-height irreducibility from supplied root coordinates

This derived internal unit assumes an actual split pinning, integral coroot
span, and a supplied `SimpleRootCoordinateFamily` over an algebraically closed
field `k`. Let `q : ℕ` be its exponential characteristic, expressed by
`ExpChar k q`, and let `r : ℕ` be a height. The unit proves the existing
`CanonicalRhoSteinbergHeightIrreducibility`
interface under these inputs. This is conditional support for law 7 of the
independent Steinberg big-cell construction; existence of the supplied
structural data remains an outstanding obligation.

For any supplied highest-weight representation of weight `(q^r - 1) rho`,
the highest weight space is nonzero. Choose a nonzero highest vector. The
supplied-family actual Frobenius orbit computation gives the lower bound
`(q^r)^N` on the representation dimension. Independently, supplied-family
whole-space detection proves that the entire canonical covariant coordinate
subspace is finite and has dimension at most `(q^r)^N`.

The generic scalar-rho eigenrow construction gives a nonzero covariant row
of the supplied irreducible rational representation. Its coefficient map
into the entire covariant subspace is injective. The two bounds force this
map to be bijective, producing `suppliedRhoSteinbergCoefficientEquiv`.
Generic coefficient-map transport then makes the rational right regular
representation on every finite basis of that whole subspace irreducible.
The result applies at every height, hence fills the published fixed-height
interface from the supplied family.

Only generic scalar eigenrow and coefficient-space algebra are reused. The
lower and upper dimension arguments come from the supplied-family units,
not the existing unconditional canonical-rho height theorem. No canonical
linked-root choice, excluded root-dimension proof, Borel identification of a
regular dynamic subgroup, or old Borel/big-cell assembly is used. This unit
adds no external source assertion.

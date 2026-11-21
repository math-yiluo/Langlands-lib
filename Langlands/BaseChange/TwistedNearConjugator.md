# Small twisted conjugators from cyclic bases

Consider two families of elements of `GL_n(E)` along a filter, both tending
to the same element. Suppose the limiting cyclic norm has a cyclic vector
over `E` and the characteristic polynomials of the two norms eventually
agree. The theorem constructs a family tending to the identity whose twisted
conjugation eventually sends the first family to the second. The base is a
`T1` topological field of characteristic zero. The finite commutative
algebra `E` is a topological ring with the module topology, and the
base-linear algebra automorphism `σ` has a positive power equal to the
identity.

The cyclic basis matrix on a fixed vector is continuous. Its unit lifts for
the two norm families therefore converge to the same basis matrix. Their
quotient `c` converges to the identity and intertwines the two norms because
equal characteristic polynomials give the same action in cyclic coordinates.

For family values `s` and `x`, put `T(a) = s σ(a) x⁻¹` on matrices. Its
`l`-th iterate is `a ↦ N(s) a N(x)⁻¹`, so it fixes `c`. The average of
the first `l` iterates of `c` is fixed by `T`. Every term converges to the
identity, whence the average has a unit lift tending to the identity. The
fixed-point equation for this unit `g` is `s σ(g) = g x`, giving the
specified twisted conjugation.

This internal construction supplies the local lifting hypothesis of the
regular twisted orbit chart used in the transfer proof.

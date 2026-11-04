# Two torus-fixed lines in a closed orbit

This is an internal linear-algebra consequence of the published
`FlagCoreLinear` constructions. It uses no additional external result.

`FlagCore.TorusFixedOrbitLinePair ρ τ e` stores two actual group
representatives, proofs that their orbit vectors are torus-fixed, and
a proof that the first vector is not a scalar multiple of the second.
`FlagCore.twoTorusFixedOrbitLines` constructs such a pair by classical
choice from the existence theorem below. It has the same hypotheses
as that theorem; the nonzero initial vector ensures both selected
orbit vectors are nonzero.

`FlagCore.exists_two_torusFixed_orbitLines` works over any infinite field,
in arbitrary universes, with a finite coordinate set and a finite set of
torus parameters. A group acts through an actual homomorphism to the
general linear group. The parameterized torus action has a supplied
simultaneous diagonalization with integral weights. The orbit of the
nonzero initial vector is closed in the published homogeneous-equation
sense `IsClosedOrbit`. If one orbit vector does not span a line fixed by
all torus parameters, the theorem produces two orbit vectors spanning
torus-fixed lines, with neither a scalar multiple of the other.

The implemented proof chooses an integral cocharacter separating all
the finitely many weights. In diagonal coordinates, the given nonzero
vector has a minimum and a maximum occurring cocharacter weight.
If these coincide, its support has a single torus weight, which would
make its line torus-fixed. They therefore differ. The published
lowest-weight contraction lemma, applied to the cocharacter and its
negative, places both extreme-weight parts back in the same projective
orbit up to nonzero scalars. Their single-weight supports give torus
fixedness. Evaluating a hypothetical proportionality at a nonzero
minimum-weight coordinate contradicts the zero coordinate in the
maximum-weight part.

The fixedness predicate here is the published linear predicate
`FlagCore.IsTorusFixed`, which tests all parameters in the supplied
torus parametrization on vectors over the original field. The theorem
does not construct a scheme quotient, a projective embedding, an
all-test fixed section, or a normalizer representative. In a group-scheme
application these comparisons and existence inputs must still be
supplied. In particular it does not by itself prove positive-root
uniqueness or a general projective fixed-point dimension bound.

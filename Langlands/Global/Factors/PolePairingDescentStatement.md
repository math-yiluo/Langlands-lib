# Local pair-factor poles and the generated integral isometry

This module states
`Langlands.Global.PoleComparison.PolePairingDescentStatement`. Its two
components are the pole-to-Gram comparison and the resulting unique
degree-preserving isometry of the generated integral spans. This file
defines the target and the concrete comparison data; it contains no proof.

`PairFactorComparisonData J A B` supplies actual complex functions for
each pair of generators, the finite sets of omitted places, their omitted
local functions, and their boundary functions. The generator index and
both omitted-place types have independent universes. The two basis types
also have independent universes, making five independent universes in
the target. `RegularPairComparisonsAt d 0` assumes meromorphy of the two
distinguished pair factors, local holomorphy and nonvanishing of each
omitted factor, separate boundary holomorphy and nonvanishing, and
equality of the completed punctured germs at zero.

`RealizesPairingAtZero` is the required local representation-theoretic
pole formula, not a theorem supplied here: the order of the supplied
pair factor is minus the integral coefficient pairing. Applications
must use the factor pairing the first representation with the dual of
the second, and establish that formula for their actual basis classes.
The equality is in `WithTop ℤ`; in particular it asserts a finite order
and retains multiplicities and their signs. Together with completed
germ comparison and removal of the regular omitted factors, it implies
equality of all generator pairings.

The lattice objects are the published `IntegralLattice` objects:
finitely supported integer combinations on an arbitrary specified basis.
Their supports are finite even when the bases and the family of
generators are infinite. No ambient spanning assumption is made.
`PoleGeneratedDescentStatement` requires a common positive rank for each
corresponding pair of generators, expressed using the supplied
natural-number basis weights and integer degree. It concludes equality
of their actual integral relation submodules and existence of exactly
one equivalence between their generated spans that sends paired
generators to each other, preserves pairings and degrees, and sends
every positive-degree norm-one element to a unique positive target
basis element. It asserts no surjectivity on the ambient bases.

The intended algebraic dependency is the already published
`Langlands.VirtualRepresentation.integralDescentAndPositivity` and its
component theorems from `Langlands.VirtualRepresentation.DescentProof`.
That branch proves relation descent, uniqueness of the generated
equivalence, isometry, degree preservation, and positive basis
extraction. H1 supplies the preceding analytic comparison; it does not
duplicate the pure lattice proof.

The provenance is a derived formulation of Henniart (2000), §§2.5–2.8,
printed pp.445–448: the generated groups and their unique isomorphism
in §2.5, the degree and pairing properties in §2.6, and the pole-order
argument and integral-relation descent in §2.8. This generic formulation
does not construct local representation classes. In applications the
bases must be the appropriate unitary arithmetic and unitary
supercuspidal classes, the generator vectors their actual finite
decompositions, and the rank degrees their actual ranks. Unitarity or
temperedness cannot be inferred from the generic coefficient lattice
or from equality of gamma factors.

All actual global functional equations, highly ramified twist
stability, factor existence, and global boundary regularity remain
separate inputs. In particular, regularity of the finitely many omitted
local factors does not supply the Shahidi (1981), Theorem 5.2 boundary
nonvanishing input. Its discharge belongs to the parent program
`34b81620-20d7-4059-9b08-6bedd1c1c029` and the common library track.
The actual arithmetic and automorphic instantiations are further
conditional adapters, with their original realization, character,
measure, and arithmetic quantifiers retained.

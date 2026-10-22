# Actual local Weil lattice operations and unramified orbits

Author: Worker 24.

For every prime `p` and actual `PadicField F`, this module instantiates the
published genuine twist and dual constructions on `LocalWeil.Basis F` and
`LocalWeil.Lattice F`. The field universe and representation-carrier universe
remain independent. The local Weil group, its topology and geometric degree
are the constructed objects from the local assembly, with no supplied group,
degree map or arithmetic certificate.

`twistBasisEquiv` is the actual scalar character twist on each continuous
irreducible isomorphism class. `twistLatticeEquiv` extends that equivalence to
integer coefficients. The forgetful formula identifies it with the genuine
twisted representation class. The identity, composition and inverse laws are
the published character group laws. Generator and coefficient formulas express
the concrete reindexing. Representation dimension degree, the coefficient
pairing and nonnegative effectiveness are preserved; effectiveness is also
reflected. The pairing assertion is a coefficient calculation and uses no
character orthogonality.

`dualBasisEquiv` is actual contragredience and `dualLatticeEquiv` its integral
extension. The forgetful formula recovers the full algebraic dual class.
Double application is identity on genuine classes and on the lattice; the
inverse is the same map. The generator, coefficient, rank, degree, pairing
and effectiveness laws specialize the published generic proofs. The actual
local group has the topological-group instance those proofs require.

The unramified twist uses `localUnramifiedCharacter F z`, for every complex
unit `z`, along the actual `localDegree F`. This character has value `z` at
geometric Frobenius. `normTwistLatticeEquiv` uses the existing local norm
character, whose value there is the inverse of the actual residue cardinality.
Its equality with the unramified twist at that inverse unit is definitional.
Thus no arbitrary normalization parameter is introduced.

The unramified orbit quotient uses this full complex-unit action. Orbit equality
means exactly that an actual unramified character carries the second class to
the first. `unramifiedOrbitMap` adds integral coefficients within each orbit;
its generator formula is the finite-support map formula. Positive representation
dimension descends to the quotient, and its fibers define the rank strata.
These strata carry no assumed finiteness, enumeration or transitivity.

## Provenance and proof route

This is derived specialization of
`Langlands.VirtualRepresentation.Weil.Local`, `.Twist` and `.Dual`, all
published. Their paired Markdown records the underlying genuine class,
continuity, rank-wise operation and finite-support constructions. Every
operation law here is obtained by specializing its generic theorem; the
orbit-generator law unfolds the finite-support coefficient map. No new
representation quotient or choice of representative is introduced.

The source motivation is Henniart (2000), sections 1.1–1.2, printed
pp.439–440, and 2.5–2.6, printed pp.446–447: actual positive-rank local
classes, contragredience and character twists, and their extension to the
free integral groups with dimension and coefficient pairing. These original
passages were read in `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The explicit unramified orbit quotient and rank fibers are derived
constructions using the published geometric-degree normalization.

Unitary restrictions, preservation of finite/Galois-type support, global
weak-association images and numerical finiteness remain separate obligations.
No correspondence, isometry between Weil and supercuspidal lattices, or
identification with an exact Grothendieck group is assumed.

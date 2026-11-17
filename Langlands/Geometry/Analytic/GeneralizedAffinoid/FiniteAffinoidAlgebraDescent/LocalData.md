# Finite Banach local algebras and ordinary overlap data

This module defines the inputs for effective descent along an arbitrary actual
finite full-domain cover of the whole spectrum of a presented affinoid algebra.
The coefficient field is any complete ultrametric normed field. All presentations
have arbitrary positive polyradii; trivial valuations, nonreduced algebras,
zero quotients, and empty covers are included.

`LocalAlgebras` stores a presented algebra and an actual bounded structural map
over each original cover algebra, with `BoundedAlgHom.IsFiniteBanach` for each
map. This includes uniform positive norm-controlled coefficient lifts, rather
than merely algebraic module finiteness.

`baseChange` is the Library's actual appended-presentation closed-quotient
`AffinoidPushout.algebra`. The coefficient map for a full subdomain is the unique
bounded restriction from its actual domain representation. The two
`overlapLeft_restriction` and `overlapRight_restriction` lemmas identify these
restrictions with the original intersection quotient legs as whole bounded maps.
`restrict` constructs further restrictions by the bounded pushout universal
property and proves the formulas on both original legs.

`PairTransitions` stores a bounded algebra equivalence between the two original
base changes over each literal intersection, preserving the entire coefficient
algebra. Its `transition` to a further full subdomain is constructed by pushout
from that pair equivalence; it is not additional supplied data.
`DescentData` requires identity on self intersections and the usual cocycle on
the literal repeated intersection `(D_i.inter D_j).inter D_k`. The cocycle is
equality of entire bounded maps between closed quotients. No inference from
spectrum points is used.

These are internal explicit models for the usual algebra descent data appearing
in Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Kiehl's Theorem and Remark 1.2.1(ii), printed p.15 / PDF p.12, and their finite
algebra application in Lemma 1.2.12, printed p.20 / PDF p.17.
Registered source: `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The explicit norm-controlled convention follows Berkovich, *Spectral theory and
analytic geometry over non-Archimedean fields* (1990), printed pp.24–25,
§§2.1.9–2.1.12; registered source
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`.
The counterexample immediately after §2.1.9 explains why no algebraic-finiteness
shortcut with the supplied norm is valid in the stated generality.

The helper proofs use uniqueness of actual domain restrictions and the Library's
proved bounded pushout universal property. This module does not prove effective
descent or supply an affinoid realization of the matching algebra.

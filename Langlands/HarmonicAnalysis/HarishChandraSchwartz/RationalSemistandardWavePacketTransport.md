# Transport of actual semistandard Levi orbits and inducing representatives

Waldspurger uses inverse conjugation on discrete-series classes in VII.2.1
and filters the relative Weyl quotient by the condition \(s\mathcal O =
\mathcal O'\) in VII.2.2(ii). See the registered source
`waldspurger-2003-plancherel`, printed pp. 317–318 (PDF pp. 83–84), and
V.1 for the left quotient convention. The declarations here derive the
corresponding orbit, representative and quotient adapters from the
Library's literal semistandard Levis and discrete-series orbits.

## Literal Levis and inducing objects

`conjugatesLevi_of_map_levi_eq` starts from equality of the image of the
literal rational-point subgroup under \(m\mapsto gmg^{-1}\) and the target
literal subgroup. It uses the closed, smooth, connected affine Levi
models and `SubgroupFunctor.range_le_of_localField_points` in both
directions. This gives the all-test equality `Association.ConjugatesLevi`
with the same \(g\). It applies to the canonical rational-point topology
over any `IsNonarchimedeanLocalField`.

`orbitPointOfClass` regards a discrete-series class with the specified
orbit class as an actual point of the orbit measured by `GlobalForm`.
`orbitPoint_mk` and `mem_orbitConstituents_iff` identify the two
membership descriptions by the defining orbit quotient.
`conjugateOrbitPoint` uses `Association.conjugateFullIndex` and
`Association.conjugateDiscreteSeriesClass` to map such points. For every
source inducing representative, `conjugateOrbitRepresentative` uses the
actual pullback of its object by the inverse of
`Association.leviPointConjugation`. The representative is a member of
the target orbit, where the base representative is the Library's
chosen one. `conjugateOrbitPoint_representative` identifies its
discrete-series point with the transported point. The field and
representation-carrier universes remain independent.

`mem_conjugateFullIndex_iff` tests membership in the transported orbit
by pulling a target class back to the source. Its proof uses the
constituent-set image identity and cancellation of the two pullbacks,
which follows from `SmoothRep.pullbackSymmIso`. For a normalizer lift
of an orbit transporter, `conjugateFullIndex_eq_of_weylTransports`
identifies the computed target full index with the given one using
`Association.WeylTransports.eq_of_same_parabolic`.

## The orbit filter on the left quotient

`conjugacyQuotientToTransporter` includes the equality transporter into
V.1's inclusion transporter. The two left quotient relations are induced
by the very same relation on the ambient relative Weyl group. This makes
the map injective. `OrbitWeylTransporters` uses
`Association.quotientWeylTransports` for the condition that a class
transports the source orbit to the given target orbit.
`orbitWeylTransportersEquiv` gives a bijection with the identically
filtered inclusion quotient. In the surjectivity proof,
`Association.WeylTransports.levi_eq` supplies equality of the transported
Levi functors from the orbit condition itself.

`orbitWeylSum` counts each retained left Weyl class once, so different
classes with the same transported orbit all contribute. The sum agrees
with its reindexing along `orbitWeylTransportersEquiv` and is zero when the
filter is empty. These constructions give the indices for VII.2.1 and
VII.2.2(ii). The normalized coefficient comparison, its descent and the
Fourier and pairing equalities have their own declarations.

# Prime cyclic descent of a stable cusp

`Langlands.Automorphic.Unramified.CyclicPrimeStableCuspidalDescentStatement`
is the existence clause of Arthur–Clozel (1989), Theorem III.4.2(d), printed
p. 202, with its proof on pp. 206–207. Definition III.4.1 and the setup of
III.4.2 use induction from unitary cuspidal data. Here the supplied upper
cuspidal realization has a unitary central character, and the conclusion
retains an actual lower cuspidal realization with a unitary central character.
The ranks on both sides are `r + 1`. The lower witness is needed in the
cyclic descent tower, where it is the upper input of the next step.

`IsoClass.IsWeakBaseChangeOf` attaches genuine spectral presentations of both
classes and uses the finite-place relation of III.1.1, printed p. 199. For an
unramified place in the common cofinite domain, the upstairs eigenvalues
are obtained by raising the downstairs eigenvalues to the residue degree.
The formula concerns weak lifting. The fibre and the exclusion of nontrivial
self-twists are separate inputs to the tower argument. The supplied generator
and faithful norm-kernel character agree with the notation of III.4.2.

For existence, Arthur–Clozel isolate the upper Hecke spectrum in the discrete
trace comparison of II.17.8 and III.4, equations (4.1)–(4.2). Their proof
excludes proper Levi support using the lower-rank lifting alternatives
III.4.2(a)–(b) and partial pair L-functions. This is the full discrete
comparison, which must accommodate a general stable cusp.

`CyclicPrimeStableCuspidalDescentTCStatement` imposes total complexness on
the base. Every infinite place then splits into complex places, so the
archimedean comparison needed in that route is at split complex places.
The carrier universes of the two spectral presentations are independent in
both declarations.

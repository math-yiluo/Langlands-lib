# Torsion numbers and counting versus surjectivity

`Langlands.Henniart.refinedStrata` proves
`Langlands.Henniart.RefinedStrataStatement.{uK, uW, uV}` for independent
field, Weil-carrier, and supercuspidal-carrier universes. The result follows
the registered route note `operator-numerical-llc-route-2026-11-16`,
*The numerical local Langlands correspondence for GL_n: counts on the two
sides and the recommended route of proof* (16 November 2026). It uses §2.2
and the proof of Lemma `lem:countsurj` in §6.1 of `numerical-LLC-route.tex`,
lines 182–202 and 1072–1084. The registered source directory has SHA-256
`faece16e4d4722c37c1ba0e7ebba30a11d94b64639f20f19a6aa7ccff3faba3f`.

## Implemented proof

A numerical injection commutes with unramified twisting. Its injectivity
therefore gives a pointwise equivalence between the two stabilizer predicates
on `ℂˣ`. `Equiv.subtypeEquivRight` and `Nat.card_congr` give equality of the
torsion numbers. The preserved Artin conductor supplies the same witness
for the two Swan exponents.

For each Weil orbit in a refined stratum, the map chooses a representative
witnessing membership and takes the supercuspidal orbit of its image. The
published fixed-rank orbit equality lemmas turn orbit equality into the
existence of an unramified twist. Twist compatibility and injectivity give
equivalent orbit equalities before and after applying the injection. Thus the
map is independent of the representative and injective. Its range lies in
the supercuspidal refined stratum by Swan and torsion preservation. The
extended cardinality of the range equals that of the Weil stratum, giving
the required inequality.

For Lemma `lem:countsurj`(a), the range is a subset of a finite stratum of
equal cardinality, so it equals that stratum. An orbit preimage of `π` gives
a Weil representative whose image lies in the orbit of `π`.
Twisting the Weil representative by the character that carries its image to
`π` gives an actual preimage.

For (b), take the assumed injection in the given rank. A representative `π`
in the supercuspidal stratum has an actual preimage `σ` by the slope bound
and the surjectivity hypothesis. The natural Artin conductor of `σ` given
by the bounded-rank hypothesis and the natural conductor witnessing the
Swan exponent of `π` have equal images in `WithTop ℕ`. The coercion is
injective, so the two natural conductors agree. This puts `σ` in the
required Weil stratum, with the required torsion number by preservation.
Its orbit maps to that of `π`, proving range equality and hence equality
of extended cardinalities.

For finiteness in (b), a representative of Swan exponent `s` in rank
`k + 1` has a natural conductor `a` with `a - (k + 1) = s`, so
`a ≤ s + (k + 1)`. The refined stratum is contained in the finite union of
fixed-conductor orbit strata indexed by this bound. Each is finite by
`Langlands.Henniart.supercuspidalOrbitStratumFiniteness`. This also covers
Swan exponent zero, where truncated subtraction permits several values of
`a`.

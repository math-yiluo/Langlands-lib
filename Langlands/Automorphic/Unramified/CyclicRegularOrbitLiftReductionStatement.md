# Reduction of cyclic regular orbit lifting

`Langlands.Automorphic.Unramified.CyclicRegularOrbitLiftReductionStatement.{uF,uE,uV,uW}`
concludes the published `CyclicRegularOrbitLiftStatement` from the following
premises. `CyclicRegularOrbitLiftReductionTCStatement` uses the totally
complex existence and pair-multiplicity premises and concludes
`CyclicRegularOrbitLiftTCStatement` at the same four universes.

| Premise | Role |
| --- | --- |
| `CyclicRegularInductionExistenceStatement` | Choose an actual lower cusp of the required rank and with unitary central character. |
| `WeakInductionOrbitBaseChangeStatement` | Identify the actual full upper orbit as a weak base change of the singleton lower datum. |
| `CyclicWeakBaseChangePairMultiplicityStatement` | Determine fixation by each norm-character twist and identify any competing unitary lower datum. |

This derived reduction uses Arthur and Clozel, *Simple Algebras, Base
Change, and the Advanced Theory of the Trace Formula* (1989), Chapter III,
Lemma 6.4, printed pp. 217–218, with the pair comparison of III.4.3,
p. 204, the arbitrary-degree local calculation in III.3.1, p. 201, and
the order assertions (2.1)–(2.3), pp. 199–200. It retains the original
quantifiers over the generator, the character with exactly the norm kernel,
and all nonidentity powers of the generator. Both reductions allow
`.{0,0,uV,uV}` for arbitrary `uV`.

The lower cusp is unitarizable by `isUnitarizable_of_hasUnitaryCentralCharacter`.
Every upper conjugate has unitary central character by transport along
its field automorphism, so the full orbit is unitary isobaric data. Let
`d = [E:F]`. Regularity makes the `d` upper constituents pairwise distinct.
Apply pair comparison to the singleton lower cusp with itself, using the
full orbit as each weak base change. There are `d` equal pairs upstairs
and at most one for each of the `d` norm twists downstairs. Each power of
`η` therefore fixes the lower class. In degree one, `η = 1` by the
norm-triviality exponent identity.

Apply pair comparison to this cusp and any unitary competitor downstairs
having the same full orbit as weak base change. Because every twist of the
witness class is equal to that class, the result is `d` times its
multiplicity in the competitor. The upper count is `d`, so the class
occurs once. Weak base change fixes the total rank of the competitor, and
every constituent has positive rank. The competitor is the singleton
of the witness. Conversely, equality with the singleton gives the
required weak base change by the forward induction comparison.

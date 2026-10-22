# Ramification for the actual p-adic integer ring

This module constructs the action of base-field automorphisms on the actual
valuation integer ring `T.Integers` supplied by `F.TopologicalData`.
The base is an intermediate field `K` with its specified compatible
`Padic p` algebra structure. No norm comparison or local reciprocity
statement is assumed.

It then constructs the lower ramification groups and rational Artin and
Swan expressions for representations of the full finite automorphism
group, for representations of its actual inertia subgroup, and for a
representation descended through an explicitly specified finite inertia
quotient. All of these constructions use that same integer ring and its
actual residue field.

An automorphism is linear over `Padic p`, hence continuous for the
supplied canonical module topology. In a nonarchimedean local field,
an element has valuation strictly below one exactly when its powers
tend to zero. The forward implication uses the Archimedean property of
the rank-one value group. The reverse implication tests convergence
against the open unit ball.

If an integral element's image had valuation greater than one, powers
of the inverse image would tend to zero. Applying the continuous inverse
automorphism would imply that the original inverse has valuation below
one, contradicting integrality. Applying this argument in both directions
constructs `integerAutomorphism` as a ring equivalence, with no supplied
stability assumption.

`integerAutHom` proves that these restrictions compose as the original
automorphisms do. Its induced `residueHom` is the actual residue-ring
functor applied to the restricted automorphisms. `inertia` is its kernel.
`lowerRamificationGroup i` consists of automorphisms acting identically
modulo the `(i+1)`st maximal-ideal power. Applying the residue map to
`sigma(x)-x` proves that the zeroth lower group is exactly `inertia`.
The groups are normal and decreasing. Integer indexing puts the full
group at `-1` and uses a constant extension below `-1`.

The supplied local-field certificate makes `T.Integers` a discrete
valuation ring and hence Noetherian. Its fraction field is the original
field, so equality of automorphisms on this integer ring implies equality
on the field. This proves faithfulness, rather than assuming it.
Finite-dimensionality over `Padic p` implies finite-dimensionality over
the intermediate field `K`, which makes the automorphism group finite.
Thus all hypotheses of the generic termination and finite-support
constructions are proved from the accepted field data.

`artinConductor` and `swanConductor` specialize the finite sums of the
preceding module to this action. `inertiaIntegerAction` restricts that
same action to inertia. Its lower groups are the original lower groups
regarded as subgroups of inertia; its zeroth group is the whole inertia
group. Therefore `inertiaArtinConductor` and `inertiaSwanConductor` retain
the denominator `|I|` and apply to an inertia representation without
requiring it to extend to the full automorphism group. The proved tame
term is `dim V - dim V^I`.
Both the full-group and inertia expressions are proved invariant under
representation equivalence, using the linear equivalence on each actual
fixed-vector space.

`descendInertiaRepresentation` takes a group `J`, a specified surjective
homomorphism `pi : J -> inertia T K`, a representation `rho` of `J`, and
a proof that `ker pi` acts trivially. Mathlib's group-homomorphism descent
is applied to the units-valued form of `rho`, then followed by the
inclusion of units into linear endomorphisms. The evaluation lemma proves
that the descended representation evaluated at `pi(j)` is exactly
`rho(j)`. Surjectivity also proves uniqueness among representations whose
pullback is `rho`. The quotient conductor constructors apply the actual finite
inertia sums to this descended representation.

The data `pi` is explicit, not chosen from an assumed existence theorem.
These constructors do not assert that every Weil representation admits
such data, or that the expressions are independent of the finite
extension or quotient. In particular they are not an unconditional
constructor for a Weil conductor. The parameter layer must supply the
actual quotient map, and the companion theorem work must prove quotient
independence. No reciprocity, normal-closure selection, Hasse–Arf, or
integrality theorem is assumed.

For a Galois extension `F.Carrier/K` these are the usual finite-Galois
constructions. The code also forms the same expressions for the
automorphism group of a nonnormal extension, without asserting any
Galois-theoretic independence theorem in that broader domain.

This is an internal construction supporting Serre's actual lower
ramification groups in *Local Fields* (1979), Chapter IV, Section 1,
Lemma 1 and Proposition 1, printed pages 61–62 (PDF pages 68–69).
The source's integer ring and its quotient actions are retained.
The conductor formula is Serre, Chapter VI, Section 2, Proposition 2 and
Corollary 1', printed pages 99–101 (PDF pages 106–108).
The decomposition into Swan and inertia codimension agrees with
Deligne (1973), Section 4.5, equations (4.5.1)–(4.5.4), printed pages
537–538, internal/PDF pages 37–38. That source treats an actual finite
quotient of inertia; its subsequent independence assertion is kept
separate here.

- Literature ID: `serre-1979-local-fields`.
- Retained file: `C:/Central-Library/Serre--Local Fields--1979.pdf`.
- SHA256: `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

- Deligne literature ID: `deligne-1973-local-constants`.
- Retained file:
  `C:/Central-Library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`.
- SHA256: `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.

The exact project integer-ring definitions are accepted version 1
artifacts `ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0` and
`e3d7bbd4-f2b9-4970-a60f-bf6aa0b34bb2`; both were verified current at
Library commit `9007729971e6e6ecea63b5567b6d1621769ccfb0`.
The first artifact's integrated Markdown hash is
`6cfb939cf42a71a81fa648b77bd4bab1076bffe0d62519181f7dc7db742124bf`;
its integration changed a documentation locator only.

The remaining project imports are the paired generic filtration/conductor
modules, using the accepted fixed-vector definition and equivalence
artifacts documented in `Conductor.md`. No pending normalization or
Galois-representation proof is imported. The explicit action data are
installed locally, with no new global field norm, topology, or
integer-ring scalar instance.

Worker 40 authored this work. The review unit comprises the three paired
modules `Filtration`, `Conductor`, and `Galois`. Their native compilation
succeeded without diagnostics. Independent semantic review and current
Library publication are separate requirements.

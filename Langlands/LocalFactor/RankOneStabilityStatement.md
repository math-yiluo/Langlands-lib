# Rank-one highly ramified twist stability

Worker 46 authors this proposition family for task
`e534647a-77a5-4c12-91d7-8a00fe104fc4`. Worker 33 contributed the concrete
rank-one interface and the review of the conductor endpoint translation.
The definitions imported from Workers 20 and 33 retain their authorship.
This is a rank-one specialization of Deligne--Henniart's theorem, expressed
using actual character conductors and the actual Gauss integral. It neither
formalizes the general virtual-representation theorem nor proves stability.
Both exported declarations are definitions returning `Prop`.

## Exact mathematical content

The prime p, finite extension F of Q_p, and carrier universe are arbitrary.
The supplied `TopologicalData` determines the topology, valuation,
principal-unit subgroups, actual residue cardinality, and conductors.
The quasicharacters are actual continuous homomorphisms `F^* -> C^*`;
they need not be unitary. The additive character is continuous, nontrivial,
and circle-valued, with the plus-sign convention in the Gauss integral.

Write a for the actual conductor of chi and n for the actual additive
conductor of psi. The hypothesis is `2 <= a`, so chi is wild. For each
quasicharacter eta with `2*a(eta) <= a`, the first conclusion asserts
`a(chi*eta)=a`. It separately asserts that both L factors equal one
in the actual rational function field `RatFunc C`, and that their
representatives equal one at every complex s. These are ramified factors,
so no evaluation at a pole is used.

The second conclusion supplies an actual field unit gamma, which is a
nonzero field element, of valuation `a+n`. The predicate
`RankOneTwistWitness` requires, for every eta in that same range, every
regular additive Haar measure mu, and every complex s,

```text
epsilon(chi*eta, psi, mu, s)
  = eta(gamma) * epsilon(chi, psi, mu, s).
```

Here `epsilon` is `PadicAbelian.epsilon`, the actual fixed-Haar Gauss
expression with the constructed conductor values. It is not a factor
symbol supplied by the caller. The statement asserts existence of the
witness; it does not take that existence as a premise or choose gamma
from an unproved theorem.

The final equivalence characterizes every witness gamma' by

```text
gamma' * gamma^(-1) in principalUnits(floor(a/2)).
```

The floor is Lean natural-number division by two. The subgroup contains
the identity by construction; the formula does not misuse the totalized
valuation at zero. No valuation condition is imposed on gamma' as a
premise: the witness property with unramified eta already detects its
valuation.

The supplied Haar measure remains the same on both sides. Neither its
normalization nor Fourier self-duality is assumed. Epsilon on this
ramified domain is an entire exponential times a finite Gauss constant,
so every complex s is a legitimate evaluation point. The adopted
companion now proves convergence for precisely these compact-annulus,
continuous-character inputs in `gaussIntegrand_integrable`. Although
the underlying Bochner integral is a total function, this statement
uses convergent integrals. No integrability assumption is used to hide
the desired conclusion.

## Original-source translation and endpoint

Deligne--Henniart 1981, Theorem 4.6, printed page 110, takes a virtual
representation V without tame constituents and a virtual representation W
of dimension zero with the strict bound `beta(W) < alpha(V)/2`.
Take V to be the rank-one chi and W to be `eta-1`. Additivity of
the constant on virtual classes gives the epsilon ratio, and
`det(eta-1)=eta` gives precisely the multiplier eta(gamma), without an
inverse on eta.

For ramified eta, sections 0.5--0.6, printed page 92, and the rank-one
conductor conventions give
`alpha(chi)=a-1` and `beta(eta-1)=a(eta)-1`. The strict inequality is
therefore equivalent to

```text
2 * a(eta) < a + 1,
```

which for integers is exactly `2*a(eta) <= a`. This includes the
endpoint when a is even. A nontrivial unramified eta gives only
break-zero constituents in `eta-1`, and satisfies the bound because
chi is wild. For eta equal to one, W is zero and the asserted formula
is the identity. No extremum of an empty constituent set is assigned.

Theorem 4.6 states uniqueness modulo `U(alpha(V)/2)` and explicitly
observes that rank-one tests W of the form `eta-1` already establish
uniqueness. By section 0.1, printed page 91, `U(t)` uses
`v(u-1) >= t`, not a strict inequality. Integral valuation gives

```text
ceil((a-1)/2) = floor(a/2),
```

which is exactly the subgroup used in the Lean proposition.

The valuation `v(gamma)=a+n` follows from Theorem 4.2(ii)--(iii),
printed page 108, and Theorem 4.6's congruence to that element modulo
U(1). Formula 4.1.1 on page 108 gives the unramified-twist check and
fixes the positive sign of this valuation. Lemma 4.7 on page 110 uses
the truncated exponential from section 0.2, and has gamma equal to the
inverse of its additive linearization parameter. The present statement
does not replace that truncated exponential by `1+y`, or claim an
unimplemented explicit construction of gamma.

The source's constant is unshifted. To obtain the stated formula at
every spectral s, use `a(chi*eta)=a(chi)` and the common spectral
power `q^(-(a+n)*s)`, as in Tate 1979, section 3.2.6 and section
3.4.5 (printed page 15, PDF page 24). The Haar scaling (3.4.3)
on the same page cancels because both representations have
dimension one. This is a derived spectral formulation, not a
literal extra clause of Theorem 4.6. The half-shifted Langlands
normalization is obtained by evaluation at s=1/2 with an actual
self-dual measure when supplied, by Tate (3.6.1) and (3.6.4),
printed page 17 (PDF page 26); no such measure is silently selected.
The q in the callable expression is the actual residue cardinality.

Conductor preservation also follows directly from the unit filtration:
the bound and `a>=2` imply `a(eta)<a(chi)`, so eta is already trivial
at the level witnessing the last nontriviality of chi. The separate
L-factor conclusion then follows from the ramified rank-one formula.
These consequences are included explicitly rather than replacing
separate L and epsilon information with a gamma equality.

## Original sources and retained fingerprints

- Pierre Deligne and Guy Henniart, *Sur la variation, par torsion, des
  constantes locales d'equations fonctionnelles de fonctions L* (1981),
  sections 0.1--0.6, printed pages 91--92, and sections 4.1--4.7,
  printed pages 108--110. The key pages 91, 92, 108 and 110 were
  inspected visually in the original. PDF page 1 is printed page 89.
  Literature ID `deligne-henniart-1981-variation`;
  file `/home/taskhub/central-library/Deligne-Henniart--Sur la variation, par torsion, des constantes locales d'equations fonctionnelles de fonctions L--1981.pdf`;
  SHA-256
  `54fe3348af12263a8d3774a0353fff352cb041728f446fb0cccc4b0f97803a3e`.
- John Tate, *Number theoretic background* (1979), sections 3.1--3.2,
  especially 3.2.6, printed pages 12--14, and (3.4.3), (3.4.5),
  printed page 15 (PDF page 24). The half-shift conventions (3.6.1)
  and (3.6.4) are on printed page 17 (PDF page 26).
  The retained Part II PDF has printed page p at PDF page p+9.
  Literature ID `tate-1979-number-theoretic-background`;
  file `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`;
  SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

## Published dependencies and scope

The imported conductor and abelian constructions were published at
Library commit `30ceb5a0d89d8094c1663fc19f35416519b9a125`. All eight
imported project Lean/Markdown pairs were checked against that historical Library.
Their Lean sources agree with the sources used by the whole-target check
below. In particular, the statement uses these actual constructors:

Integration uses the canonical direct import
`Langlands.LocalFactor.Abelian.Padic` and its dependency
`Langlands.LocalFactor.Abelian.Definitions`. The migration preserves their
mathematical declarations; the table retains the original paths and fingerprints.

| Original Lean module | Historical source SHA-256 |
| --- | --- |
| `Langlands.HarmonicAnalysis.Basic` | `2198cecae146fa7f904dc2c01169d6321aee8e155c99614ed92f861fd2d65aff` |
| `Langlands.HarmonicAnalysis.Conductor` | `1780ea3172b1c84654e647efa3208d12c669a8c51a0942a1b80f4a66f84b4a53` |
| `Langlands.LocalFactor.Abelian` | `18215959be4fdf7359708f2250aa94e60a3a78f6e99919ea0c7ada61cf74ba22` |
| `Langlands.LocalFactor.PadicAbelian` | `1689aa7750d78260e3657d039053e4d496a1c945a43585ecdecc1b7e4ae7bf05` |

Worker 20 adopted Worker 33's callable companion without changing the
used conductor or epsilon expressions, and added rational L-factors,
restricted evaluation, the proved all-spectral-parameter convergence, and
the equality with the separately constructed abelian constant.
The complete independent semantic report approves the three construction
pairs without qualifications; the final integration published them at
`e4e22245747ec04edd4445d4557b746f8f53de29`. The migrated Library retains their
mathematical bodies with canonical dependency imports. The historical published Markdown hashes for `Conductor`,
`Abelian`, and `PadicAbelian` are respectively
`ef4097816de90b81e1be2bc9b1dad6de7896a8b9fb658e122afd8876fa7faeac`,
`129f034c9b060d474b4eab1c2379529ec067b8a16123abc4098f7194f03e87c2`,
and `1f9bbd7495ab99fd5a3d915d44cda05345b1c1fa0bbfee4e3d9e1089b3fd9d0c`.
The imported local-field normalization and continuous-character results
are also present unchanged. No unreviewed project source is needed by
this statement.

The generic virtual theorem still needs actual virtual Weil representations,
upper ramification breaks, tensor and determinant operations on those
classes, and the independently specified local-constant system. This
rank-one statement does not supply those objects or count as completion of
that theorem. It is distinct from Worker 33's abelian functional-equation
family, whose actual expressions it reuses.

## Whole-target development check

Development checks establish well-formedness, not mathematical
verification. Independent semantic review and publication of this
statement remain separate obligations.

Before the pilot restart, the extended target completed managed check
`9f2ffaa4-47d9-43f3-b7db-ca29c1cc0f3d`: the nine-module incremental Lake
build and exact declaration inspection both returned zero, without diagnostics,
and both process trees were quiet. The declaration returns `Prop` at its
independent carrier universe `u`. Its complete target fingerprint is
`24ec0a52922740dd70d76c062ed2c68d34a664b1107599941402de357573983e`;
the Lean source hash is
`67713f7831117f2766cb38f9dd8612e61a5911886a504fe62def9e19db323aa2`.
The checked snapshot is
`a77b61a55844db20f374ae17828a9b7787c66616f12b353d7fca79e9010f7e1c`.
The inspection reports only `propext`, `Classical.choice`, and `Quot.sound`.

The mathematical dependencies are the named Lean modules and declarations
in the current Library. The check identifiers record development evidence.

The pilot recheck on 2026-10-20 completed as
`cf256ca3-5250-49f6-9f86-e11eff0beae6` in the pinned Lean 4.34.0 /
Mathlib 5ed29652 environment. The Lake build returned zero with no
diagnostics, and exact inspection reports `statement_returns_prop: true`,
the same carrier universe `u`, the same complete target fingerprint
`24ec0a52922740dd70d76c062ed2c68d34a664b1107599941402de357573983e`,
and only `propext`, `Classical.choice`, and `Quot.sound`. The Lean source
is unchanged. The imported project files match the assigned pilot Library
`30ceb5a0d89d8094c1663fc19f35416519b9a125`.

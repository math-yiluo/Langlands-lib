# Minimal newvector level

`Langlands.NewvectorStatement` is an unproved proposition definition about
actual complex representations of `GL_(n+1)(F)`, for every `n : Nat`, every
prime `p`, and every finite extension `F : Langlands.PadicField p`.
The field and vector-space universes are independent. The supplied
`T : F.TopologicalData` specifies the topology and compatible valuation;
no extension is restricted by ramification or degree.

The representation is assumed admissible and irreducible. Genericity is
an explicit hypothesis: there is a nonzero complex linear functional
transforming under each upper unitriangular matrix by the product of the
values of `psi` on its adjacent upper entries. The additive character is
continuous, nontrivial and unitary. Genericity is not asserted for all
irreducible representations.

## Congruence condition and conclusion

Write `O` for `T.Integers` and `P` for its actual maximal ideal. For
`a : Nat`, the local predicate `level a g` means that the entries of `g`
and `g` inverse lie in `O`, and that the last row of `g` is congruent to
`(0,...,0,1)` modulo `P^a`. Membership of a field element in `P^a` is
expressed by an element of the actual integer ring with that image.
Thus this condition is on actual matrices, not a supplied family of
subgroups. At level zero `P^0 = O`, so the row condition is automatic
for integral matrices: the group is `GL_(n+1)(O)`. At positive levels
this is the subgroup `K_(n+1)(a)` of the cited conductor theorem.
The inverse-entry condition expresses invertibility over `O`, not merely
invertibility over `F`. In positive level the usual invertibility
requirements on the upper left block and lower right entry follow from
the last-row congruence and invertibility of the reduction.

The conclusion supplies a natural number `m` and a nonzero vector `v`.
Every element satisfying `level m` fixes `v`. Every vector fixed at that
level is a unique complex multiple of `v`. If a nonzero vector is fixed
at any level `a`, then `m <= a`. These assertions express existence,
dimension one at the least level, and minimality, including level zero.
For rank one the empty adjacent-entry product is one and the
unitriangular subgroup is trivial; the statement includes the usual
character conductor case.

The local predicates simply expand the target. The current Library's
[Congruence](Congruence.md) module already constructs
`Langlands.Conductor.integralCongruence`, `congruenceSubgroup` and
`levelSubgroup`. It proves the last-row congruence characterization on
integral representatives, identifies `integralSubgroup` with matrices whose
entries and inverse entries are integral, and proves `levelSubgroup_zero`
and `levelSubgroup_antitone`. With a compatible valuation and topology
and an `IsNonarchimedeanLocalField` instance, `levelOpenSubgroup` and
`isCompact_levelOpenSubgroup` provide the open subgroup and its compactness.
The adapter identifying this target's inline predicate over `T.Integers`
with that bundled subgroup remains unproved, as does the minimal-newvector
theorem itself. No subgroup-closure or openness result is assumed as a
record field. The conductor equality with the exponent of
the epsilon factor, the essential vector's Rankin--Selberg test-integral
identity, and arbitrary-character normalization formulas are separate
targets; they are not asserted by this proposition.

## Original sources and correction

Jacquet, Piatetski-Shapiro and Shalika, *Conducteur des representations du
groupe lineaire*, Mathematische Annalen 256 (1981), 199--214:

- Section 1.1, pages 199--200, fixes the additive-character exponent-zero
  convention and recalls the rank-one conductor.
- Section 5.1 and its theorem, page 211 (PDF page 13), gives the groups
  `K_r(a)`, sets `K_r(0)=K_r`, and states nonnegativity of the epsilon
  exponent, invariance and dimension one at that level, and minimality
  among all `a >= 0`.

The essential-vector existence proof in the original paper is flawed.
The necessary correction is Jacquet, *A correction to Conducteur des
representations du groupe lineaire*, Pacific Journal of Mathematics 260
(2012), 515--525: Theorem 1 on page 517, the corrected argument on pages
518--523, and Remark 1 on page 523. The corrected existence theorem is
used as the source for the existence prerequisite, not the original
flawed argument. The corrected theorem concerns generic representations;
Remark 2 on page 524 extends its integral result to specified standard
induced representations, not to arbitrary nongeneric irreducibles.

The present target extracts the fixed-vector assertions, omitting the
epsilon-exponent identification. Its vector-space assertion is independent
of the chosen additive character. Consequently the genericity hypothesis
may use any nontrivial unitary additive character; it need not be the
exponent-zero character used to normalize the source's epsilon factor.
Transport between nontrivial additive characters and the rank-one
character interpretation are proof obligations, not assumptions of
the proposition's truth.

Retained original files, registered source IDs and SHA256 fingerprints:

- `C:/Central-Library/Jacquet-Piatetski-Shapiro-Shalika--Conducteur des representations du groupe lineaire--1981.pdf`,
  `jpss-1981-conductor`,
  `986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d`.
- `C:/Central-Library/Jacquet--A correction to Conducteur des representations du groupe lineaire--2012.pdf`,
  `jacquet-2012-conductor-correction`,
  `98f02c2aef04bff162c1ceb0a42dd122da746d1304a90d82366a848f22713adf`.

## Exact dependencies and status

The project imports are the following accepted, published definition
artifacts, all at version 1:

- `e3d7bbd4-f2b9-4970-a60f-bf6aa0b34bb2`,
  `Langlands.LocalField.Normalization.Definitions`: actual valuation
  integer ring. Effective Lean SHA256
  `b997a64a0f59ce13d45e2b5349de9ad87466a5e2d3e16ab3f1a4ef97a048214b`,
  Markdown SHA256
  `dac7d3aeb5229c505e5271f66d7decf6c7c4404853e9f15a363b4f9401902436`.
- `ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0`,
  `Langlands.LocalField.Definitions`: the finite extension and topological
  interface, imported transitively by normalization.
- `665022df-625b-44ae-9dbd-425f6e266bab`,
  `Langlands.Representation.Smooth.Definitions`: admissibility, including
  smoothness and finiteness of fixed vectors for all open subgroups.

The remaining interfaces are Mathlib's representations, irreducibility,
general linear matrices, additive characters, dual modules, and maximal
ideal powers, in environment
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1 (Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`).
No pending Whittaker or conductor construction is imported.

Worker 11 authored this target. Development check
`8797da11-4597-47de-9465-a686b62b2926` built the four required modules
with the shared Lake environment, reporting zero errors and warnings.
Exact declaration inspection confirms a proposition definition retaining
the independent universes `uF` and `uV`, with target fingerprint
`98941fe181a833be072adf42cc59d6babc2a0a1a4117d4c0473ca5b196a058ff`.
The reported allowed assumptions are only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. The earlier environment-probe timeout
was an unavailable check, not a mathematical rejection.
Compilation and target inspection do not establish semantic acceptance or
publication. No proof of this proposition or of the broader local-factor
theorem family is claimed.

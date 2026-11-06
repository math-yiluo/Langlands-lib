# Cuspidal embeddings through an actual represented parabolic

Authors: Worker 1758 (original formulation) and Worker 1775 (source and
interface verification and documentation).

This statement records the Corollary and its explicit quotient construction
in Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, VI.2.1, printed p.139 / PDF p.145. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Supercuspidality follows the all-proper-parabolic definition in VI.2.1,
printed p.137 / PDF p.143. The Lean file defines a proposition and does not prove it.

`LeviCuspidalEmbeddingStatement` concerns every connected reductive group
scheme `G` over a nonarchimedean local field `k`. It retains the field
valuation, Hausdorff topology and local-field instances. The topology on
`G(k)` is the canonical `RationalPointFamily.pointTopology`; its local
compactness and nonarchimedean group structure are the same explicit inputs
as in the published represented-parabolic VI.5 and VI.6 statements.

For every irreducible smooth complex representation `π` of `G(k)`, the
conclusion supplies actual group schemes `P`, `M`, `U`, morphisms
`p : P → G`, `l : M → P`, `r : U → P`, and proofs that they are a rational
parabolic, rational Levi and matching geometric unipotent radical, with
`subgroupMultiplication l r` an isomorphism. No such parabolic is assumed
in advance, and it need not be proper.

The topology on `M(k)` is exactly `leviPointTopology l hl`. Affineness,
local compactness and the nonarchimedean group instance are derived using
`hl.isConnectedReductive.isAffineHom`, `leviPoints_locallyCompactSpace` and
`leviPoints_nonarchimedeanGroup`. The published topological group isomorphism
`leviPointsEquiv p l hp hl` identifies these canonical Levi points with the
literal image `pointImage (l ≫ p)` in `G(k)`. The two Levi-valued functors
use pullback along this isomorphism or its inverse, so their actions and
topologies are the actual published ones. Let `J` be the actual
`leviJacquetFunctor p l r hp hr hl hmul` applied to `π`. The conclusion
requires the following data at this same parabolic and Levi:

- `J` is nonzero, expressed by `Nontrivial J`;
- `J` is supercuspidal: for every actual proper rational parabolic of `M`,
  with every rational Levi and matching radical datum, its actual normalized
  `jacquetFunctor` applied to `J` is a subsingleton;
- an irreducible supercuspidal smooth representation `ρ` of `M(k)`;
- a surjective equivariant complex-linear map `J → ρ`;
- an injective equivariant complex-linear map
  `π → leviInductionFunctor p l r hp hr hl hmul (ρ)`.

The two supercuspidality conditions are written out using the same
all-proper-actual-parabolic quantifiers, `¬ IsIso p'` test and
`Subsingleton` predicate as the represented VI.5 interfaces. No
proper-standard-only predicate is substituted.

The universes `u` of the field and rational point groups and `v` of the
representation carriers are independent; there is no inequality between
them. Both `π` and the chosen quotient `ρ` have carrier in `Type v`; the
actual Jacquet quotient also stays in that universe, as does a quotient of
that Jacquet module. Normalized induction has carrier in `Type (max u v)`.
Consequently the embedding is an actual `Representation.IntertwiningMap`
between the two carrier sizes. It is not a categorical morphism that would
force a common representation universe.

Renard's proof chooses a minimal standard parabolic with nonzero Jacquet
module and uses V.3.11 and VI.1.4 to show that module is supercuspidal.
VI.1.3 gives finite generation and hence an irreducible quotient of it.
Exactness preserves supercuspidality of that quotient. Normalized
Frobenius reciprocity produces a nonzero map from `π` into induction, and
irreducibility makes it injective. The displayed surjective map records
the quotient explicitly constructed in this proof. The formulation omits
the optional choice of a standard parabolic; it keeps the source's
all-proper-parabolic notion of supercuspidality from the Definition, using
Remark 1 for the source proof's passage from standard parabolics. The chosen
parabolic may equal `G`; this includes the already supercuspidal case.

This is an unrestricted represented interface for that source assertion.
It adds no maximal split torus, generic cocharacter, standardness,
root-system, parabolic-realization, compact-quotient, admissibility or
functor-exactness premise. All such inputs needed by an implementation
remain proof obligations.

The published `RationalCuspidalEmbeddingStatement` and its proof concern a
supplied standard family with explicit structural inputs and the carrier
universe `max (u + 1) v`. The published
`RepresentedLeviCuspidalEmbedding.cuspidalEmbedding` transports that result
to a represented dynamic Levi while retaining those inputs. They provide
useful proof components but do not state this unrestricted proposition.
Discharging their structural hypotheses, comparing all proper parabolics,
and controlling the actual carrier universes remain necessary for any
proof using that route. Neither support association nor finite length of
induction is asserted here.

Renard VI.6.2, Lemma and proof, printed p.178 / PDF p.184, uses precisely
the irreducible embedding part for an irreducible representation of a Levi:
it embeds into induction from an irreducible supercuspidal representation
of a further Levi. Exact induction and induction in stages then reduce
finite length to VI.5.4. This file supplies the statement of that embedding
input, without proving the separate VI.1 functor properties, VI.3 splitting,
VI.5 finiteness, VI.6 finite-length or VI.7 support assertions. The existing
`RealizedLeviNesting` and `RealizedLeviStages` constructions remain reusable
inputs for a proof; this proposition does not duplicate their constructions
or discharge their remaining structural comparisons.

# Standard parabolic witnesses for discrete-series embeddings

`Langlands.Aubert.General.RepresentedParabolic.discreteSeriesEmbeddingStandardReduction`
proves `DiscreteSeriesEmbeddingStandardReductionStatement`. For an irreducible
smooth complex representation `π`, the theorem equates the existence of an
embedding into normalized induction from a rational parabolic with existence
from a parabolic and Levi at the same index of the fixed standard family.
[Statement](DiscreteSeriesEmbeddingStandardReductionStatement.md)

From a rational witness, `parabolicLeviStandardConjugatingPoint` gives a single
point `g ∈ G(k)` and an index `J` contained in the simple relative roots. The
proof supplies `parabolicDynamic`, `dynamicGeometricUnipotentRadical`,
`smoothMaximalSplitTorusConjugacy`, and `relativeRootSystem` to this construction.
It postcomposes the parabolic inclusion `p` with `(G.innerIso g).hom`, which
makes the ranges of the new parabolic inclusion and the composite Levi
inclusion standard at `J`. The Levi and radical maps into `P` use the same
source schemes. The embedding lemma expresses the Levi map as `e.hom ≫ l`
for `e = Iso.refl M`. The identity law gives the required Levi range equality,
and `isIso_subgroupMultiplication_iso_comp` gives the multiplication isomorphism.

The rational point map of `e` acts as the identity, so the identity linear
equivalence intertwines `σ` with its pullback along that point map. Together
with the irreducibility of `π` and the given embedding, this is the input to
`exists_embedding_conjugate_presentation`, which gives an injective intertwiner
into the new normalized induction. The proof uses the same `σ` with the
canonical topology on `M(k)` defined by `leviPointTopology`. Its irreducibility
and its square-integrability hypothesis for every Borel measurable structure
and Haar measure on `M(k) ⧸ Z(M(k))` therefore apply directly. In the reverse
direction, the standard datum and its embedding already supply a rational
witness.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
of 9 July 2026, VII.2.6 Theorem, printed p. 231 (PDF p. 237), uses a standard
parabolic for the embedding. V.3.8–9, printed pp. 111–112 (PDF pp. 117–118),
fixes the standard family and gives parabolic conjugacy into it. V.3.1, printed
p. 110 (PDF p. 116), gives conjugacy of Levi factors within a parabolic.
The registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

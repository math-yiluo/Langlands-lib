# Renard II.1.2: disjoint decomposition and exact sequences

Worker 6 authored these source-backed closed proposition definitions.
They state the scalar indicator lemma and the two complete open-closed
exact sequences; they supply no proofs of the new targets.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, II.1.2, printed
page 31 / PDF page 37. The lemma is the first assertion on that page,
the test-function proposition is (II.1.2.1), and its distribution
corollary is (II.1.2.2). The function-space conventions begin on printed
page 30 / PDF page 36. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 6 read these complete pages and the following PDF page 38.

## Actual spaces and hypotheses

Every target quantifies an arbitrary `X : Type u`, its supplied topology,
Hausdorffness, local compactness and total disconnectedness. The public
`Langlands.Topology.isLocallyProfinite_iff_mathlib` equivalence identifies
these three classes with the source's Hausdorff compact-open-neighborhood
basis convention. No global compactness, nonemptiness, group structure,
second countability or sigma compactness is assumed. Subsets use their
induced subtype topology.

`SchwartzBruhat X` is the existing complex submodule of actual functions
`X → ℂ` which are locally constant and have compact support.
`Distribution X` is its full complex algebraic linear dual. Neither test
functions nor distributions receive a new topology here, and no continuity
condition is imposed on a distribution. All four maps and all indicator
functions are imported from the public Library by Lean name, without new
carriers or replacement maps.

## Disjoint scalar indicators

`DisjointIndicatorDecomposition` states that every `f : SchwartzBruhat X`
is exactly a finite sum of complex scalar multiples of
`Langlands.Hecke.TestFunction.characteristic` for actual subsets `V i`.
Each subset is compact and clopen. In a Hausdorff space, a compact open
set is closed, so this is exactly the source's compact-open condition.
The proposition's `Pairwise` clause requires distinct indices to have
disjoint sets. The equality is in the actual complex test-function
module, and hence also gives equality of values at every point of X.
The existing characteristic has value one on the specified subset and
zero outside it.

The finite family is indexed by `Fin n` with n an existential natural
number. Zero is permitted, so zero functions and empty spaces are
included. Empty members and zero coefficients are also permitted, as
in the source's assertion. No disjointness or decomposition is supplied
as a hypothesis. The source proves this by a finite compact-open cover
and the disjoint refinement of II.1.1; the new proposition does not
prescribe a proof route.

## The test-function exact sequence

`TestFunctionExactSequence` quantifies every actual open subset U of X.
The closed subset is literally its complement `Uᶜ`; its closedness proof
is `hU.isClosed_compl`. The first map is the existing linear zero
extension `SchwartzBruhat.extendZero hU : SchwartzBruhat U →ₗ[ℂ]
SchwartzBruhat X`. The second is the existing closed restriction
`SchwartzBruhat.restrictClosed hU.isClosed_compl : SchwartzBruhat X →ₗ[ℂ]
SchwartzBruhat Uᶜ`.

The proposition asserts three things: the first map is injective; its
linear-map range is exactly the second map's kernel; and the second map
is surjective. These are precisely exactness at all terms of
0 → D(U) → D(X) → D(Uᶜ) → 0. Range-kernel equality includes the zero
composition and the existence of a zero-extension preimage for every
function with zero closed restriction. Thus the proposition does not
replace middle exactness with only the zero-composition direction.
The existing closed-restriction surjectivity proof is reusable in a
future proof of this aggregate, but it does not alone prove all terms.

## The algebraic distribution exact sequence

`DistributionExactSequence` uses the same X, U and actual closed
complement. Its first map is the existing
`Distribution.closedPushforward hU.isClosed_compl`, the algebraic dual
of closed restriction. Its second map is the existing
`Distribution.restrictOpen hU`, the algebraic dual of zero extension.
Their domains and codomains are exactly D′(Uᶜ), D′(X) and D′(U).

Again the assertion is injectivity of the first map, equality of its
linear-map range with the kernel of the second, and surjectivity of
the second. This expresses the entire source sequence
0 → D′(Uᶜ) → D′(X) → D′(U) → 0. It concerns the original full algebraic
duals; no continuous-dual extension or analytic extension hypothesis
is inserted. The source obtains this sequence by vector-space duality
from the test-function sequence. A future proof must establish the
endpoint surjectivity as well as middle exactness.

`Assertions` is exactly the conjunction of the three closed targets.
The universe u is unrestricted, and U may be empty or all of X.
These statements do not assert the later support-descent formulation,
the pairing with compactly supported distributions, or the vector-valued
and tensor assertions of II.1.2–II.1.3. Those remain separate units.

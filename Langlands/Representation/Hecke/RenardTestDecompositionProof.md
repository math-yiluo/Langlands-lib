# Proof of Renard II.3.5 finite test-function coset expansions

Worker 139 proves
`Langlands.Hecke.RenardTestDecomposition.Statements` in the theorem
`Langlands.Hecke.RenardTestDecomposition.statements`. Its three component
theorems are `doubleCosetExpansion`, `leftInvariantExpansion` and
`rightInvariantExpansion`, in the same namespace. Each proves the exact
published proposition at the unrestricted group universe `uG`.

The source assertion is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.3.5 Lemma (i)–(ii), printed
p.46 / PDF p.52, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The proof uses the published common compact-open bi-invariance theorem for
part (i), then proves all three expansions by compactness. This differs
from the source's refinement through finite subgroup indices. It uses the
original `SchwartzBruhat` carrier and unnormalized characteristic functions.

The internal helper `finitePartitionExpansion` is a derived general
compactness lemma. It applies to a complex function with compact support
and a cell map `C : X → Set X` satisfying self-membership, equality of cells
when one contains the other's representative, openness, and constancy of
the function on each cell. A finite subcover of the support shows that the
image of the support under `C` is finite. This image removes duplicate
cells and excludes cells where the function vanishes. The proof chooses a
representative in the support for each image cell and enumerates the
resulting finite type by `Fin n`. Its coefficient is the function value
at that representative and is therefore nonzero.

If two chosen cells meet, the cell-equality law identifies them; injectivity
of the enumeration then identifies their indices. This proves pairwise
disjointness. A point in the support lies in its own image cell, while a
point in a chosen cell has the nonzero value of its representative. These
two implications prove the exact support equality. At a point in the
support the finite indicator sum has one surviving term, whose coefficient
is the function value there; outside the support all terms vanish. For
the zero function the image of the empty support is empty, so this same
construction gives `n = 0` and the empty sum.

For part (i), `TestFunction.commonCompactOpenBiInvariance G {f} ⊤` supplies
a compact open subgroup `K` on which `f` is invariant on both sides. The
cells are the actual `TestFunction.doubleCosetSet K g`. Their openness,
self-membership and equality on membership follow from the published
double-coset facts. Both invariance laws show that `f` is constant on each
cell. The helper's pointwise equality becomes equality in the actual test
space by extensionality and `doubleCosetIndicator_apply`.

For part (ii), right cosets `K g` are expressed as double cosets for
`K.toSubgroup` and the trivial subgroup, and left cosets `g K` use these
subgroups in the opposite order. The proof establishes the exact set
equalities with the existential coset descriptions in the target. Their
openness follows from openness of `K` under multiplication of sets. The
left fixedness hypothesis is evaluated at `k⁻¹` to obtain
`f (k * x) = f x`; the right fixedness hypothesis directly gives
`f (x * k) = f x`. Thus each helper application returns all the target's
nonzero coefficients, disjointness, exact support and pointwise expansion.
The given subgroup and compactness premise are retained.

The proof requires no countability or measure hypothesis and introduces
no normalization. The published statement pair and its imports are
unchanged. Compilation and exact-target inspection use the task's pinned
Lean environment; independent validation, semantic review and publication
are separate acceptance steps.

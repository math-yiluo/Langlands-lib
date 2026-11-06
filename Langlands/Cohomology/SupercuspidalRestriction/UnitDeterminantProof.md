# The unit-determinant subgroup of GL over a p-adic field

Author: Worker 1580.

This module proves the unchanged Library proposition
`Langlands.Cohomology.SupercuspidalRestriction.UnitDeterminantSubgroupStatement`
from `Langlands.Cohomology.SupercuspidalRestriction.Statement`.
The theorem is
`Langlands.Cohomology.SupercuspidalRestriction.unitDeterminantSubgroupStatement_proof`.
Its parameters are an implicit natural number `p`, an instance `[Fact p.Prime]`,
an explicit `F : PadicField.{0} p`, and an explicit rank `n : ℕ`.
There are no additional hypotheses. The field carrier and general linear
groups are in `Type`; there are no universe parameters beyond those fixed in
the published target. The topology on the field is
`F.canonicalTopologicalData.topology`, and the topology on the group is
`F.canonicalGeneralLinearTopology n`.

Writing `H = unitDeterminantSubgroup F n` and `G = GeneralLinear n F.Carrier`,
the conclusion is the conjunction that `H` is open in `G`, `H ∩ Z(G)` is
compact as a subset of `G`, and `Z(G) ⊔ H` has finite index in `G`.

## Implemented proof

The helper `unitDeterminantSubgroup_eq_determinantNorm_ker F n` identifies the
target subgroup, defined by the canonical spectral norm of the determinant,
with the kernel of `F.canonicalTopologicalData.determinantNorm n`.
The published
`PadicField.TopologicalData.determinantNorm_eq_canonicalNorm_pow_degree`
expresses the residue-normalized norm as the canonical norm raised to
`Module.finrank (Padic p) F.Carrier`. This exponent is positive by
`Module.finrank_pos`. The canonical norm is nonnegative, so
`pow_eq_one_iff_of_nonneg` proves equality of the two unit conditions.
The coercions through nonnegative real units preserve equality.

After rewriting by this equality, openness is exactly the published
`PadicField.TopologicalData.isOpen_ker_determinantNorm`.
For rank zero the matrix group is finite (indeed a singleton), so every
subset is compact and every subgroup has finite index.

For rank `m + 1`, let `T = F.canonicalTopologicalData` and let `B` be the
positive one-block shape `CuspidalSupport.LeviAdmissibility.oneBlock`.
The multiplication equivalence `MulEquiv.piUnique` evaluates the one-block
Levi at its unique index. It is continuous by `continuous_apply`.
The image of `determinantUnitSubgroup T B` is the normalized determinant
kernel: the forward implication evaluates its blockwise unit condition,
and the reverse implication uses the constant family of the given matrix.
`Subgroup.map_center_eq` identifies the image of the actual Levi center
with the actual matrix-group center.

Injectivity of this equivalence permits mapping the intersection using
`Subgroup.map_inf`. The published
`CuspidalSupport.leviDeterminantUnitCentralCompactness F T B` and
`IsCompact.image` then give compactness of the required intersection.
Mapping the join by `Subgroup.map_sup` and applying
`Subgroup.FiniteIndex.map_of_surjective` to the published
`CuspidalSupport.determinantUnit_sup_center_finiteIndex T B` gives the
finite-index conclusion, with the join order exchanged by `sup_comm`.

This transport follows the one-block argument used in the published
`GodementJacquet.determinantNorm_ker_sup_center_finiteIndex`; that larger
module is not needed as an import. All the mathematics about product Levis
is reused from published results. The norm comparison and transport are
internal derived steps, not additional assertions attributed to the source.
The target pair and its imported pairs are unchanged.

## Source and correspondence

I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
GL(n,F), where F is a non-Archimedean local field*, Russian Mathematical
Surveys 31:3 (1976), 1–68, §3.20, printed page 34 (PDF page 34).
Registered source: `bernstein-zelevinsky-1976-representations-gln`,
SHA-256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
The retained text and rendered page were read directly.

The source defines the determinant-unit subgroup for each positive block
and their product. Part (a) states compactness of its intersection with
the center, and part (b) states openness, normality, commutativity of the
quotient, and finiteness after adjoining the center. The target selects
openness, compact central intersection and the last finiteness assertion,
specialized to one block. Normality is already proved in the statement
module. Rank zero is the trivial-group extension required by the published
target, rather than a positive-block claim from the source.

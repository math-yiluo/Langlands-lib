# Generic constancy and geometric-connectedness constructibility

Worker 105. This derived prerequisite states an unproved geometric generic
constancy assertion and proves its conditional implication to the existing
geometric-connectedness constructibility targets. The topological reduction
is proved. The geometric generic constancy assertion remains open.

## Sources and scope

The geometric target is the count-one consequence of Stacks Project
Lemma 37.28.5, tag 055H, in registered source
`stacks-fibre-constructibility-local-dimension-2026-11-04`, SHA-256
`1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`.
That lemma makes the number of geometrically connected fibre components
constant on a nonempty relative open subset of a point closure. Schemes are
sober, so every irreducible closed subset is such a closure. On the relative
open subset the number is either one everywhere or one nowhere. Relative
opens are intersections with ambient opens, giving the stated formulation.

`FiniteTypeGeometricallyConnectedFiberGenericConstancy` quantifies over
arbitrary schemes in universe `u` and morphisms that are locally of finite
type and quasi-compact. For each irreducible closed target subset `Z`, it
requires an ambient open `U` with nonempty `Z ∩ U` that is either contained
in the actual geometric-connectedness fibre locus or disjoint from it.
The actual locus uses residue-field fibres and geometric connectedness
including nonemptiness. There are no affineness, separation, properness,
smoothness, flatness, Noetherianity or surjectivity hypotheses.
This is a Boolean consequence of the component-count result, and does not
define or assert the constancy of the full component count.

The topological argument is the sufficient direction of Stacks
Lemma 5.16.3, tag 053Z, specialized to this Boolean generic-constancy
hypothesis. Registered source
`stacks-noetherian-constructibility-criterion-2026-11-04`, SHA-256
`94135ebdfc1fe3e65d4a2a3e7cfc97857bcf1f3b1b6f32371ce8686defe45076`,
contains the original statement and Noetherian-induction proof.
These prerequisites support Conrad Theorem 3.4(2), printed pages 5–6;
neither generic constancy nor the full filtered-descent theorem is proved here.

## Implemented proof

`isConstructible_of_irreducibleClosed_genericConstancy` works for every
Noetherian topological space, with no separation or sobriety hypothesis.
It uses well-founded induction on closed subsets `Z` to prove that `Z ∩ S`
is constructible in the ambient space. Empty closed subsets are immediate.
A reducible closed subset is covered by two proper closed subsets, to
which induction applies, and the resulting constructible sets are united.

For an irreducible closed subset, the supplied hypothesis gives a nonempty
relative open piece `Z ∩ U` on which membership in `S` is constant. The
closed subset `Z \ U` is strictly smaller. If the piece is included in
`S`, the desired intersection is the union of its intersection with
`Z \ U` and `Z ∩ U`. If it is disjoint from `S`, only the smaller
intersection remains. In a Noetherian space every open is compact and
constructible, and every closed is the complement of such an open.
Induction and the Boolean closure of constructible sets complete both
cases. Taking the top closed subset gives constructibility of `S`.

`isConstructible_geometricallyConnectedFiberLocus_of_genericConstancy`
applies this theorem over any Noetherian target, assuming the geometric
generic constancy target. Its Noetherian affine specialization proves
`noetherianAffineGeometricallyConnectedFiberConstructibility_of_genericConstancy`.
Finally the existing Noetherian affine equivalence gives
`geometricallyConnectedFiberLocalConstructibility_of_genericConstancy`.
Every occurrence of geometric generic constancy in these reductions is
an explicit hypothesis.

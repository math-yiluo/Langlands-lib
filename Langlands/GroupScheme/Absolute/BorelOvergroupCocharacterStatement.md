# Actual cocharacters for absolute smooth Borel overgroups: statement

Worker 1358, with Workers 146, 1240 and 1270 identifying the local geometric
input and the dependency cycles that motivate this formulation.

`Langlands.GroupScheme.AbsoluteBorelOvergroupCocharacterStatement.{u}` is a
proposition about every algebraically closed field `k : Type u`. Let `G` be
connected reductive, let `T` be split, and let `j : T.toGrp ⟶ G` be the torus
map of a specified Borel pair. Let `i : P ⟶ G` be a smooth closed subgroup,
and let `b : B ⟶ P` satisfy `IsBorelPair (b ≫ i) j`. Thus `b ≫ i` is an
ambient Borel, `j` is a maximal torus, and an actual factorization of `j`
through this Borel exists.

The conclusion supplies an actual integral cocharacter
`ζ : cocharacterLattice T`. The image subgroup of `P(k)` in `G(k)` equals
the field points of `Dynamic.parabolic (groupHom ζ ≫ j)`. Here `G(k)` is
the actual group of morphisms from the identity object over `Spec k`;
the equality is between subgroups of that group. The assertion includes
all characteristics, general connected reductive groups, the full ambient
group as an overgroup, empty root systems and rank-zero tori. It imposes
no separate connectedness assumption on `P`.

## Provenance and proof obligations

This is a derived local formulation of Milne, *Algebraic Groups* (2017),
source `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`,
Section 21.i, printed pp.452–455 (one-based PDF pp.468–471), especially
Theorem 21.91 and Corollary 21.92. These pages were read together with the
official 2017 errata snapshot dated 2026-11-02. There is no correction to
21.91 or 21.92 in that snapshot. The defective necessity assertion of
21.68(d) is not a justification for this statement.

Corollary 17.49, printed p.367 (PDF p.383), makes a smooth closed overgroup
of an ambient Borel connected. Section 21.i classifies Borel overgroups
by subsets of the simple roots and identifies the parabolic of a dominant
cocharacter by its vanishing simple-root pairings. Prescribing zero on
the selected simple roots and positive values on the others, followed
by positive denominator clearing, gives an actual integral cocharacter.
The section reduces reductive groups to their semisimple quotient by the
central radical. Applying this route to the present statement still
requires proving the relevant root-subgroup containment and equality,
and retaining the lift of a rational cocharacter to the original torus
in the reductive case. These assertions are proof obligations, not
additional premises of this proposition.

The source gives equality of smooth closed subgroup schemes. This
statement asks only for its field-point consequence. The separately
proved `Dynamic.range_eq_parabolic_iff_algClosed_points` can recover the
all-test equality under the displayed smoothness and closedness hypotheses.
The companion reduction in `SplitParabolicCocharacterAbsoluteReduction`
uses this comparison and split-torus descent to recover the original
arbitrary-field fixed-torus target.

No abstract-subgroup classification, standard-root indexing, relative
Tits system, rational Bruhat decomposition or general standard-cocharacter
statement is assumed here. This file defines the proposition and supplies
no proof of it. Acceptance of this statement or its conditional companion
reduction does not discharge the fixed-torus classification task.

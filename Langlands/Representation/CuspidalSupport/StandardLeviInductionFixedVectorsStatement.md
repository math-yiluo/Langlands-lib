# Fixed-vector detection inside a standard Levi: statement

Module `Langlands.Representation.CuspidalSupport.StandardLeviInductionFixedVectorsStatement`.
Namespace `Langlands.CuspidalSupport`.

`StandardLeviInductionFixedVectorsStatement` is an internal derived proposition
for the standard-Levi form of Renard VI.10.6, Corollary. It has universe parameters
`uF`, `uV` and is parameterized by the local field, the ambient group scheme,
the torus embedding, the cocharacter and a `BernsteinStandardFamily`.
The topology is the published rational-point topology, with the ambient local
compactness and nonarchimedean group instances retained.

For finite standard indices `leviIndex J I ⊆ J`, a compact open subgroup `K`,
a subgroup `K₀` normalizing `K`, the minimal Iwasawa factorization using `K₀`,
and Iwahori intersection decompositions of `K` along every standard parabolic,
the proposition says that normalized induction inside `M_J` has nonzero
`K ∩ M_J` fixed vectors if and only if its coefficient has nonzero
`K ∩ M_{leviIndex J I}` fixed vectors. Coefficients use carrier universe
`max uF uV`; both intersections are literal subgroup comaps. Compactness of
`K₀` and containment `K ≤ K₀` are not premises of this helper.

This proposition is derived from the published ambient normal-level criterion
`Jacquet.nontrivial_standardInduction_fixedVectors_iff` and the published
induction-in-stages isomorphism `bernsteinStandardInductionStagesIso`.
Apply the criterion to outer induction from `M_J` and to direct induction
from `M_{leviIndex J I}`; induction in stages identifies the ambient results.
The module states the proposition only and supplies no proof.

The source context is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, VI.10.6, printed
pp.213–215 / PDF pp.219–221. This internal statement isolates the fixed-vector
step inside a Levi used in the Corollary. Its induction-in-stages derivation
is an alternative to applying compact inheritance and Mackey theory inside
the Levi.

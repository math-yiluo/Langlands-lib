# Represented Levi intersections along a common maximal split torus

Authors: Worker 117 and Worker 3483 (named Worker 15 in the route note).
Worker 3483 supplied the composition route; Worker 117 instantiated it with
the canonical published proofs.

`Langlands.GroupScheme.representedParabolicLeviIntersection` proves exactly
`Langlands.GroupScheme.RepresentedParabolicLeviIntersectionStatement.{u}`,
defined in `Langlands.GroupScheme.Rational.ParabolicLeviIntersectionStatement`,
at the published arbitrary universe `u`, with no added hypotheses.

Over every field, let `P` and `Q` be parabolics of connected reductive `G`,
with supplied rational Levis `M` and `L`. Let `U` be the supplied geometric
unipotent radical of `Q`, with its multiplication isomorphism. If `M` and `L`
contain a common ambient maximal split torus, the conclusion supplies actual
group schemes and inclusions representing `M ∩ Q`, `M ∩ L` and `M ∩ U`.
They form a parabolic of `M`, its rational Levi and complementary geometric
unipotent radical, with an actual multiplication isomorphism. The three
intersection identities are equalities of subgroup functors on every test
scheme.

The proof applies the published reduction
`Langlands.GroupScheme.representedParabolicLeviIntersection_of_dynamic`
from `Langlands.GroupScheme.Rational.ParabolicLeviIntersectionReduction`.
Every input theorem is a published unconditional proof:

| Input theorem | Module |
| --- | --- |
| `Langlands.GroupScheme.parabolicDynamic` | `Langlands.GroupScheme.Absolute.ParabolicDynamicProof` |
| `Langlands.GroupScheme.dynamicCentralizerReductive` | `Langlands.GroupScheme.Dynamic.CentralizerReductiveProof` |

The reduction realizes the supplied parabolics and Levis dynamically, factors
the cocharacters through the common maximal split torus, and constructs the
three intersections as the dynamic parabolic, centralizer and unipotent
subgroup of `M`. Their closed models and multiplication supply the witnesses;
the two input proofs discharge the structural premises. The reduction's
stronger common-torus theorem also factors the torus through `M ∩ L`; its
wrapper discards this extra conclusion to match the exact target.

This is derived content composed from the named Library results. The target's
paired Markdown records its relationship to Renard V.4.6(ii) and V.4.7. The
implemented argument is the published dynamic intersection reduction. It
retains all original field and characteristic quantifiers and all supplied
geometric hypotheses, with no extra structural premise.

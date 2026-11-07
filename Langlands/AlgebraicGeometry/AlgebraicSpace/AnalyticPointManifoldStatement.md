# The analytic manifold structure on rational points of smooth algebraic spaces

Author: Worker 105.

This module states the analytic-manifold assertion of Proposition 5.4 of Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011), printed p.15. It
contains one Prop-valued statement and no proof.

Conrad's sentence reads: "If k is complete and X is smooth then X(k) admits a unique
functorial k-analytic manifold structure which agrees with the scheme case and carries étale
maps to k-analytic local isomorphisms."

## Statement

`AnalyticPointManifoldStatement`: for every complete nontrivially normed field `K : Type u`,

1. there is an `AnalyticPointStructure K` that is admissible (`IsAdmissible`); and
2. any two admissible families are `Equivalent`.

The vocabulary is defined in `AnalyticPointManifold`. An `AnalyticPointStructure K` gives,
for every `n` and every algebraic space `X` over `Spec K` with
`IsSmoothPureDimensional K n X`, a charted space over `Fin n → K` on `X(K)`. Here
`IsSmoothPureDimensional K n X` means quasi-separated, locally separated, locally of finite
type, with an étale atlas smooth of relative dimension `n`. Each charted space is for the
étale-chart topology of `X(K)`. The family is admissible when:

- every structure is a `K`-analytic manifold;
- every morphism induces an analytic map on rational points;
- every étale morphism induces an analytic local diffeomorphism;
- on affine `n`-space, the coordinates are an analytic diffeomorphism onto `Kⁿ`.

Two families are equivalent when the identity of every `X(K)` is analytic in both
directions.

## Relation to the source

The correspondence with Conrad's wording is explained in `AnalyticPointManifold.md`:

- **"Smooth".** It becomes smooth of pure relative dimension `n` for every `n`.
- **"k-analytic manifold structure".** This is a Mathlib analytic manifold
  (`IsManifold 𝓘(K, Fin n → K) ω`) over the topology of Proposition 5.4.
- **"Functorial".** This is analyticity of all induced maps.
- **"Agrees with the scheme case".** This is agreement on affine space; together with the
  étale condition it determines the classical structure on smooth schemes.
- **"Carries étale maps to k-analytic local isomorphisms".** This is `IsLocalDiffeomorph`
  for étale morphisms.
- **"Unique".** This is uniqueness up to the identity being an analytic diffeomorphism.

The source's standing hypotheses are kept: quasi-separated and locally of finite type
(Section 5 convention, printed p.13), and a complete field. Complete fields are henselian, so
this is within the scope of Proposition 5.4.

The class adds local separatedness. This is the same correction as for the topology of
Proposition 5.4 (`HenselianSpacePointTopologyStatement`). The quotient of `A¹` by `x ∼ -x`
for `x ≠ 0` (Stacks Project, Tag 02Z1) is smooth, since `A¹` is an étale atlas, but it is not
locally separated. Its atlas is not locally injective on `K`-points at `0` when the
characteristic of `K` is not `2`. So no structure carries this étale map to a local
isomorphism, and the assertion fails for it.

## Sources

- Conrad, registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, printed p.15,
  Proposition 5.4, third paragraph.
- Stacks Project, Algebraic Spaces, Example 14.1 (Tag 02Z1), registered copy
  `stacks-algebraic-spaces-chapter-ed88ff78-2026-11-05`.

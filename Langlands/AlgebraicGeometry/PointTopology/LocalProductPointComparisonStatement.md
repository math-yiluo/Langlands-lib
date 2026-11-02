# Comparison with points of actual local base changes

Author: Worker 208.

`LocalProductPointComparisonStatement` concerns the existing
`localProductPointMap C R X`. Its domain consists of actual morphisms
`Spec (∀ i, R i) → X` over `Spec C`. Its target is the product of the
actual `R i`-points of `X ×[Spec C] Spec (R i)`.

The four conclusions have independent hypotheses:

- The map is injective when the underlying scheme `X.left` is
  quasi-separated.
- It is surjective when `X.left` is affine, for arbitrary commutative
  value algebras.
- It is surjective when `X.left` is quasi-compact and every `R i` is local.
  Quasi-compactness is expressed by `CompactSpace X.left`.
- It is a homeomorphism when `X.left` is affine and every `R i` is a
  commutative topological ring. Both sides use the independently constructed
  affine global-section evaluation topologies, with the product topology
  on the target.

In particular, the first three clauses use no topology. The surjectivity
clauses impose no quasi-separatedness, and the affine clause imposes no
local-ring condition. In the final clause there is no topology on `C`,
continuity condition on its structure maps, finite-type condition,
Hausdorff condition, local-ring condition or open-unit condition.
All rings, index types and schemes occupy an arbitrary common universe `u`.

This is a derived combination of Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), printed pp.6–8,
Theorem 3.6, formula (3.6.1), formula (3.6.2), and its affine reduction.
Registered source: `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source's general product comparison uses points over a common base.
The local factors of (3.6.1) instead use actual base changes. The present
statement connects those conventions by the existing explicit
pullback-adjunction equivalence. The affine topology clause uses evaluation
at all coordinates, so it is formulated for arbitrary affine schemes,
beyond the finite-type case used in Theorem 3.6.

This statement does not assert the arithmetic realization of the product
as the actual `S`-level adelic ring. Actual global fields of both
characteristics, their local fields and valuation rings, the arithmetic
structure maps, the separation and compactness instances of finite-type
models, the nonaffine local topologies, and change-of-`S` maps remain
separate obligations. Its topology clause concerns the existing affine
evaluation topology; it does not define a topology by transporting it
through the comparison.

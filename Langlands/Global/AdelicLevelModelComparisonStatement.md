# Comparison targets for actual adelic-level model points

Author: Worker 208.

`AdelicLevelModelComparisonStatement` combines the curve-place and
number-field comparison targets for the actual maps constructed in
`AdelicLevelModelPoints`. All fields and schemes occupy one arbitrary
common universe. The curve-place clause quantifies arbitrary fields `k`
and `F` with `Algebra k F`, every finite set `S` of actual curve places,
and every scheme `X` over the actual ring `curvePlaceSIntegers k F S`.
The number-field clause quantifies a number field `K`, every finite set
`S` of finite places, and every scheme over Mathlib's actual S-integer
ring `(S : Set (FinitePlace K)).integer K`. All infinite places occur
among its local factors, including when the finite-place set is empty.

The domain of each map consists of actual relative scheme points with
values in the published adelic level subring. Its target consists of
actual points of the actual local base changes, valued in the corresponding
completed fields or completed valuation rings. The scalar actions are
induced by the original S-integer diagonal, as proved by the defining
unit's coordinate identities. The sum indices simply reindex the
products in the source.

Each target has five independently qualified conclusions:

- Quasi-separatedness of `X.left` implies injectivity.
- Affineness implies surjectivity.
- Quasi-compactness, expressed by `CompactSpace X.left`, implies
  surjectivity. Every local factor is already a local ring.
- Quasi-compactness and quasi-separatedness together imply bijectivity.
- Affineness implies that the actual map is a homeomorphism for the
  independently defined global-section evaluation topologies, with
  the product topology on the target.

The first four conclusions are statements about sets and require no
point topology. The final clause uses the published topology on each
actual adelic level and on every completed local factor. It imposes
no finite-type, Hausdorff or open-unit hypothesis and no topology on the
S-integer base. It concerns affine schemes only.

This is derived arithmetic specialization of the published
`LocalProductPointComparisonStatement`, using its proof, the explicit
level-to-product algebra equivalences, and the published topology
comparisons for those actual level rings. The source context is Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed pp.6–8, Theorem 3.6 and formulas (3.6.1)–(3.6.2), with
the level conventions on printed p.1. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The affine statement extends beyond the finite-type models used there.

These are statement targets, with proof publication separate. They do
not derive quasi-compactness or quasi-separatedness from the source's
finite-type models over Noetherian S-integer rings. In particular, the
Noetherian arithmetic realization of the curve-place S-integer ring,
model descent, the global-function-field realization, local nonaffine
point topologies, transition maps, the adelic colimit (3.5.1), and
independence of the initial model remain separate obligations. The
constructions allow every finite `S`; applying the source's function-field
convention requires `S` to be nonempty. The curve-place clause itself
needs no finite constants or specified rational parameter.

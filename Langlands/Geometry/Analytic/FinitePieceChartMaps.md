# Bounded chart maps into complete normed algebras

Lean module: `Langlands.Geometry.Analytic.FinitePieceChartMaps`
(namespace `Langlands.Analytic.AffineAnalytification.FinitePieceLocal`). Support module for
Task 7655.

## Content

Fix a complete ultrametric nontrivially normed field `K`, a `K`-algebra `A` with a finite
polynomial presentation `P`, and a normed `K`-algebra `E`. The `m`-th chart algebra
`algebra K P m` of the analytification of `A` is the quotient of the generalized Tate algebra of
polyradius `polyradius K P.arity m` by the relations of `P`.

* `Admits P E τ m`: the images under `τ : A →ₐ[K] E` of the generators of `A` have norm at most
  `radius K m`. `exists_admits` says every `τ` admits some level, and `Admits.mono` says admitted
  levels are upward closed.
* `tateLift`, `chartLift`, `chartLift_algebraMap`: if `τ` admits level `m` and `E` is complete
  and ultrametric, evaluation at the generator values (`GeneralizedTateAlgebra.evaluateHom`)
  gives a bounded map out of the Tate algebra. It kills the relations of `P`, so it descends
  (`PresentedAffinoidAlgebra.descendRelations`) to a bounded map out of the chart algebra that
  extends `τ`.
* `chart_hom_ext`: two bounded maps out of a chart algebra that agree on the image of `A` are
  equal (`PresentedAffinoidAlgebra.hom_ext_coordinate`).
* `origIndex`, `satMap`, `satMap_restriction`, `range_origIndex`,
  `range_origIndex_representative`: the saturated-atlas index of an original chart, and the
  coordinate map `A → algebra` of a saturated chart, given by `LocalDomainMaps.localAlgebraMap`.
* `orig_hom_ext`, `exists_orig_lift`: the same uniqueness and existence statements for the
  algebra of an original saturated index. That algebra is the chart algebra up to the definitional
  identification `saturatedRepresentative_original`. The proofs rewrite along that equation by
  `subst` (`whole_hom_ext`, `exists_whole_lift`).
* `exists_chart_superset`: a compact subset of the analytification lies in every sufficiently
  large chart. The interiors of the chart ranges form an increasing open cover
  (`range_chart_mem_nhds`).

## Proofs

`hasBoundedMonomials_of_admits` checks the radius-bounded-powers criterion
`GeneralizedTateAlgebra.hasBoundedMonomials_iff_radiusBoundedPowers` from `Admits`. The relation
check in `chartLift` uses `tateLift_polynomialMap`: on polynomials the lift is `τ ∘ P.map`, which
vanishes on the relations. The compactness argument extracts a finite subcover of the directed
cover.

## Provenance

Internal. These are the standard universal properties of Tate algebras and of their quotients,
stated for the Library's charts of an affine analytification. Task 7655 uses them to map chart
algebras into test algebras.

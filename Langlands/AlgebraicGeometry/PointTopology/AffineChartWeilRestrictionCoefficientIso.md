# Coefficient isomorphisms for actual affine-chart Weil restriction

This derived construction transports actual Weil restriction through an
isomorphism of its coefficient algebras. It compares independently glued
schemes and retains their original counits.

The source motivation is Brian Conrad, *Weil and Grothendieck approaches to
adelic points*, December 31, 2011, Example 4.2, printed pp.9–10, especially
the completed-tensor decomposition and the subsequent Weil-restriction
identities on printed p.10. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
That page was read. There is no source-specific errata file in the current
Library's `notes/errata` directory.

Conrad replaces the completed tensor algebra by a product of upper-place
fields. Applying a Weil construction to those two presentations requires
transport through the actual coefficient isomorphism. This module supplies
that step over arbitrary commutative rings. It does not construct the
arithmetic coefficient isomorphism. Its arbitrary-ring scope and its
local-ring point-topology statement are derived generalizations using
the existing actual all-test representation and scheme-point continuity
theorems, rather than verbatim statements of Example 4.2.

All rings and schemes use one arbitrary common universe. Let `A`, `B`, and
`D` be commutative rings with their given `A`-algebra structures, and let
`e : B ≃ₐ[A] D` be an actual algebra isomorphism. Assume `B` is finite
projective as an `A`-module. Let `Y` be an actual scheme over `Spec B`,
locally of finite type, separated over `Spec B`, such that every finite
set of its underlying points lies in an affine open. This last assumption
is the existing geometric predicate `HasFiniteAffineNeighborhoods`.
Neither representability nor an inverse to a comparison map is assumed.

Write `f : Spec D ⟶ Spec B` for the contravariant spectrum map of `e`,
and `Y_D = f*Y` for the actual categorical pullback. The principal
construction is

```text
affineChartWeilRestrictionCoefficientIso :
  Res_(B/A)(Y) ≅ Res_(D/A)(Y_D),
```

where both `Res` objects are the existing `affineChartWeilRestriction`
construction. The abbreviation `affineChartWeilRestrictionCoefficient`
expands to the right-hand construction using the finite and projective
instances derived from `e.toLinearEquiv`; it does not define a new
representation by transporting the old object.

`weilCoefficientSpecIso` is literally `Scheme.Spec.mapIso` of the actual
ring equivalence. `weilCoefficientSpecIso_hom_base` proves
`f ≫ Spec.algebraMap A B = Spec.algebraMap A D` from `e.commutes`.
For every actual test scheme `T` over `Spec A`,
`weilCoefficientTestIso` constructs

```text
Over.map(f)(T_D) ≅ T_B
```

by the actual map between the two pullbacks, with first component the
identity on `T` and second component `f`. The isomorphism of coefficient
spectra makes this pullback map invertible. Naturality is checked against
both pullback projections. Tests are arbitrary schemes, with no affine
restriction.

`weilCoefficientFinite` and `weilCoefficientProjective` derive the two
module properties of `D` from the linear equivalence underlying `e`.
Local finite type and separatedness of `Y_D` follow by pullback stability.
Its projection to `Y` is affine, since it is the pullback of a morphism
between affine spectra. The existing affine-inverse-image lemma therefore
derives `HasFiniteAffineNeighborhoods Y_D` from the original geometric
premise. No geometry of `Y_D` is an additional input.

`affineChartWeilRestrictionCoefficientComparison` first precomposes the
original counit comparison `T_B ⟶ Y` by the test isomorphism, then uses
`Over.mapPullbackAdj f` to obtain `T_D ⟶ Y_D`. Its `_fst` theorem
identifies the composite with the projection `Y_D ⟶ Y` exactly:

```text
(coefficientComparison T p).left ≫ pullback.fst Y.hom f
  = (weilCoefficientTestIso T).hom.left ≫
      (originalComparison T p).left.
```

Its naturality follows from the original comparison's naturality, the
test isomorphism's naturality, and the pullback adjunction's naturality.

`affineChartWeilRestrictionCoefficientTestEquiv` composes the proved
original representing equivalence with source transport by the test
isomorphism and the actual pullback adjunction. Its application theorem
identifies its function with the comparison above. Composing with the
inverse of the independently constructed `D/A` representing equivalence
gives `affineChartWeilRestrictionCoefficientRepresentingEquiv`, natural
on all actual tests. Its value on the identity defines the canonical
scheme morphism. Naturality identifies every component with
postcomposition by this fixed morphism, and Yoneda's bijectivity criterion
proves it is an isomorphism.

The `_Iso_comparison` theorem, named in full
`affineChartWeilRestrictionCoefficientIso_comparison`, states that for
every `T` and `p : T ⟶ Res_(B/A)(Y)`, the second scheme's original
counit comparison applied to `p` followed by this isomorphism is exactly
`affineChartWeilRestrictionCoefficientComparison T p`. It is proved by
the inverse law of the second representing equivalence. Thus the
construction fixes the actual comparison and preserves the separately
defined original counits.

For a commutative topological `A`-algebra `S` that is a local ring, with
open units and continuous inversion, the construction also gives
`affineChartWeilRestrictionCoefficientPointHomeomorph`. Its endpoints
are actual `RingPoint` sets, each equipped with its independently defined
`schemePointTopology`. It applies the published
`schemePointIsoHomeomorph` to the scheme isomorphism above. The `_apply`
theorem identifies its function as actual postcomposition, and its
`_comparison` theorem is the same original-counit identity at the actual
test `ringTest A S`.

No topology on `A`, `B` or `D`, no continuity assumption on `e`, and no
locality of either coefficient algebra is needed. The construction adds
no field, characteristic, separability, completeness or Hausdorff
hypothesis. The topology on `S` is the only topology supplied for this
step.

The actual completed tensor decomposition over all upper places, its
function-field instances, the identification of the factor targets,
complete-field point comparisons, integral models, geometric preservation
of Weil restriction and the global adelic homeomorphism remain separate
obligations. In particular, this contribution does not by itself finish
Example 4.2 or the whole-paper task.

# Independent point topologies for the finite-product Weil decomposition

Author: Worker 208.

This derived construction supplies the finite-product topological step in
Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Example 4.2, printed pages 9–10, especially the second
Weil-restriction identity on page 10. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source first makes a scalar base change, then decomposes restriction
along a product of completed fields into a product of Weil schemes.
Compatibility with finite products on local-ring points is the consequence
of Proposition 3.1, printed page 4, used for that step.

All types lie in a common arbitrary universe. The index type is finite,
possibly empty. Each commutative `A`-algebra `B i` is finite and projective
as an `A`-module. Write `P = ∀ i, B i`. The target `Y` is an actual scheme
over `Spec P`, locally of finite type and separated over that base, with
`HasFiniteAffineNeighborhoods Y.left`: every finite set of its points is
contained in an affine open. The value ring `S` is an `A`-algebra with a
topological commutative ring structure, is local, and satisfies
`IsOpenUnits S`, including continuous inversion with the subspace topology
on the units. No topology is required on `A`, any `B i`, or `P`.

The factor target `Y_i` is literally `finiteProductFactorScheme B Y i`,
the pullback along `Spec (B i) → Spec P` induced by the coordinate ring
projection. Its local finite type and separatedness are derived from
pullback stability. The preceding algebraic product construction derives its
finite affine neighborhoods from those of `Y`, and finite projectivity of
`P` from that of the finite family. No factor geometry is supplied as extra
data.

`affineChartWeilRestrictionProductPointHomeomorph B A S Y hY` has source
the actual relative `S`-points of the independently glued Weil scheme
`affineChartWeilRestriction A P Y`. Its target is the dependent product of
the actual relative `S`-points of the separately glued schemes
`affineChartWeilRestriction A (B i) Y_i`. Every factor point space and the
source have their independently constructed `schemePointTopology`; the
target has their ordinary product topology.

The implementation applies `schemeFiniteProductPointHomeomorph` to the
actual fan `affineChartWeilRestrictionProductFan` with its proved
`affineChartWeilRestrictionProductFanIsLimit`. Thus the algebraic universal
property and the general finite-product topology theorem provide the
homeomorphism. It does not assign either endpoint topology by transport
through an equivalence.

The `_apply` theorem identifies component `i` with
`p ≫ affineChartWeilRestrictionProductProjection B A Y hY i`.
The `_apply_iso` theorem identifies the same point with `p` followed by
the canonical Weil product scheme isomorphism and its `i`th categorical
projection. The `_comparison` theorem applies the original factor
base-change/counit map to that component and obtains exactly
`affineChartWeilRestrictionProductComparison B A Y (ringTest A S) p i`.
The latter is the actual pullback of the original counit comparison,
precomposed with the inverse of the canonical iterated-test identification.
These equations follow from the generic finite-product projection law and
the existing algebraic projection and counit identities; they are intrinsic
laws of the constructed map.

`projectiveImmersionWeilRestrictionProductPointHomeomorph` takes an actual
immersion `j : Y.left ⟶ ProjectiveSpace P n` whose composite with the
projective structure map is `Y.hom`. The published projective-immersion
adapters derive separatedness and finite affine neighborhoods, then invoke
the general homeomorphism. Its comparison theorem retains the exact same
counit formula. Local finite type remains an explicit hypothesis; no
quasi-compactness is inferred from an arbitrary immersion over a general
ring.

This arbitrary-ring result is a derived generalization of the product step
used in Example 4.2. It imposes no characteristic, separability, field,
Hausdorffness or completeness assumption. It does not yet identify an
actual completed tensor algebra with the product over all upper places or
compare each factor Weil scheme's base-field points with its target's
upper-field points. Those arithmetic and local-field realizations,
integral models, geometric preservation properties and the global adelic
comparison remain separate obligations.

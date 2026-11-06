# Failure of local compactness for the adelic affine-line subspace

Original proof: Worker 208. Checked for submission by Worker 1568.

The theorem `adelicAffineLineNonLocalCompactness` proves
`AdelicAffineLineNonLocalCompactnessStatement`, the non-local-compactness
consequence of Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), printed p.10, Example 4.3. It concerns the original adelic carrier with
the topology induced from the unrestricted product of completions and the
literal range of the actual standard affine-line map `a ↦ [1:a]` in arithmetic
adelic projective one-space.

The internal product criterion argues at a point mapping to zero in every
completed-field coordinate. A compact neighborhood contains the inverse image
of a product neighborhood. A basic cylinder inside that neighborhood restricts
only finitely many of the infinitely many noncompact coordinate spaces. At a
coordinate outside that finite set, every single-coordinate spike has a lift
to the original carrier inside the compact neighborhood. The continuous image
of the compact neighborhood under projection to that coordinate is therefore
the whole noncompact local space, a contradiction. The extra product factor
allows arbitrary additional coordinates to remain fixed during this argument.

For the actual curve-place adeles, the extra factor is a singleton. For full
number-field adeles, it is the product of all infinite completions. The spikes
are Mathlib's `RestrictedProduct.single` in the original restricted-product
carrier, with zero in every infinite coordinate in the number-field case.
`GlobalPlaceTopologyFacts` supplies intrinsic infinitude of the actual finite
place sets and noncompactness of the original completed-field topologies;
these are proved arithmetic facts rather than assumptions on a place package.
The curve-place assertion for the coefficient carrier even permits arbitrary
constant fields; the source-qualified final assertion uses finite constants.

Finally, the proved `curvePlaceAffineLineSubspace` and
`numberFieldAffineLineSubspace` embeddings give homeomorphisms from the
coefficient carriers with their product-induced topologies to the literal
ranges of the actual projective affine-line maps. Local compactness transfers
along a homeomorphism, giving the second negation in each branch.

The proof retains both global-field characteristics, arbitrary common universe,
all infinite number-field factors, every initial finite arithmetic set and
potentially inseparable finite function-field presentations. It does not prove
the separate rational-point density, nonclosedness or nondiscreteness claims of
Example 4.3, or whole-paper coverage.

Source: registered `conrad-2011-weil-grothendieck-adelic-points`, December 31,
2011 edition, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed p.10, Example 4.3. The compact-neighborhood argument above is the
implemented expansion of the source’s non-local-compactness consequence.

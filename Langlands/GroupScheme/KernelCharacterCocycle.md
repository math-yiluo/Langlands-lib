# Descent of characters of the full kernel

This is an internal construction for character lifting across a group-scheme
homomorphism. It uses the actual scheme-theoretic kernel, including when that
kernel is not smooth or reduced. All constructions are in every universe `u`
over an arbitrary base scheme `S`.

For a homomorphism `f : H ⟶ G` and two relative points `a,b` with equal image,
`difference f a b h` is the unique point of `kernel f` whose image in `H` is
`a⁻¹ * b`. It is constructed with the published `kernelPointsEquiv`.
Monomorphy of the actual kernel inclusion proves its naturality under every
test-scheme map and its multiplicative identity along triples.

`cocycle f χ` evaluates a character of the kernel on this right difference.
It is defined on every pair of scheme maps to `H` with equal composite with
`f`, not just on field points or relative affine tests. The equal composites
give equal structure maps to `S`, so both maps can be considered as relative
points over a common test scheme. The comparison `cocycle_on_over` identifies
this construction with evaluation on relative points. Naturality of character
evaluation and the difference identities then prove the two hypotheses of
effective unit-cocycle descent.

The auxiliary theorem
`Langlands.Scheme.Modules.exists_unit_coboundary_of_lineBundle_trivial`
applies effective descent along any affine, flat, surjective scheme map
`p : X ⟶ Y`. It assumes that every actual line bundle on `Y` is isomorphic
to the trivial line bundle. After choosing such an isomorphism for the
descended bundle, the proof compares its pulled-back trivialization with the
one supplied by descent. The scalar of the resulting structure-sheaf
automorphism gives a unit `q` with comparison scalar
`a* q · (b* q)⁻¹`. This follows the published proof of
`exists_unit_coboundary_of_pic_trivial`, replacing its affine module-Picard
hypothesis by the actual line-bundle triviality assumption.

Finally `exists_unit_coboundary` applies that theorem to `cocycle f χ`. Its
conclusion is the all-test identity

```text
χ(a⁻¹b) = a* q · (b* q)⁻¹.
```

The hypotheses are affineness, flatness and surjectivity of the underlying
scheme map and actual line-bundle triviality on the target. The construction
does not require centrality, reductivity, split maximal tori, or smoothness of
the kernel. It supplies the descent step only; converting a normalized
regular unit into a group-scheme character is a separate result.

The provenance is internal and derived from the published kernel, character
evaluation, structure-sheaf scalar, and effective unit-cocycle descent APIs.
The all-test cocycle argument follows the implemented method in
`HomogeneousCharacterLineBundle`, replacing its supplied homogeneous quotient
by the actual kernel of `f`. No new assertion is attributed to the literature.

The unit coboundary uses `Scheme.Modules.exists_unit_coboundary_of_lineBundlesTrivial` with the same inverse-scalar convention.

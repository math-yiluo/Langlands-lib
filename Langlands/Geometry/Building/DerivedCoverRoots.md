# Actual roots and root points through a cover of the derived group

This internal construction composes the published central-isogeny and
derived-inclusion comparisons used in the source-apartment construction.
It works over every field `k : Type u`.

Supply affine group schemes `C`, `D`, `G`, with `C` and `D` locally of
finite type and `G` smooth, a central isogeny `π : C → D`, and an actual
derived inclusion `d : D → G`. Supply split commutative tori `R`, `T`, `S`,
`A`, their acting homomorphisms `iC`, `iD`, `iG`, torus maps `t : R → T`,
`e : T → S`, `c : A → S`, and the commuting squares

```text
iC ≫ π = groupHom t ≫ iD,
iD ≫ d = groupHom e ≫ iG.
```

Assume `groupHom t` is an isogeny. Assume that the actual product
`centralComplementProduct e c : T × A → S` is flat and surjective and that
`groupHom c ≫ iG` is central on every test scheme.

`derivedCoverRootPullbackEquiv` constructs the bijection
`relativeRoots iG ≃ relativeRoots iC`. Its forward character map is exactly
`a ↦ t ≫ e ≫ a`, as its coe lemma proves. The construction composes
`RelativeRoot.derivedRelativeRootEquiv` with
`centralIsogenyRootPullbackEquiv`. Thus it uses the actual nonzero adjoint
relative roots throughout.

For each ambient root `a`, `derivedCoverRootGroupPointsEquiv` constructs a
multiplicative equivalence between the rational points of the source root
group for `t ≫ e ≫ a` and the ambient root group for `a`. It composes the
central-isogeny root-point equivalence with the derived-inclusion
equivalence at the base test scheme. Its coe lemma proves that the forward
map is exactly `rationalPoints.map (π ≫ d)`.

`map_rootGroupPoints_derivedCover` consequently identifies the image of
each corresponding source root group under this actual composite with
the entire ambient root group. `injective_rootGroupPoints_derivedCover`
proves injectivity of that composite on each such source root group.
These conclusions do not assert surjectivity on all ambient rational
points.

All content is derived by composing the imported actual-object
constructions and their evaluation formulas. Neither simply connectedness
of `C` nor maximality of the tori is required for this comparison; both may
be supplied in its intended application. The structural tori, isogeny,
derived inclusion, squares and product properties remain supplied. This
module does not transfer valuations or apartments and does not prove the
final normalizer-action equality.

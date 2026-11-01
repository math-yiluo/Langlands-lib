# Algebraic tensor maps and distribution products

Authors: Worker 6 and Worker 16. This construction implements the maps from David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, II.1.3, printed p.32 / PDF p.38. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Carriers and canonical test map

All scalar tests are the published `SchwartzBruhat` space of actual locally
constant compactly supported complex functions. All distributions are the
published full complex algebraic dual `Distribution`; there is no topology
on this dual. The tensor product over the complex numbers is algebraic.

`SchwartzBruhat.tensorBilinear` packages the existing external product
`SchwartzBruhat.tensor`, whose formula is `(x,y) ↦ f(x)g(y)`, as a complex
bilinear map. `SchwartzBruhat.tensorLinearMap` is its lift by the algebraic
tensor universal property. Its pure-tensor image is exactly the existing
external product. The construction proves its pointwise formula, but makes
no claim here that this map is bijective.

## Actual partial-evaluation maps

`SchwartzBruhat.sliceSnd f x` is the existing test `y ↦ f(x,y)`.
`SchwartzBruhat.sliceFst f y` supplies the test `x ↦ f(x,y)` by the existing
continuous-left-inverse restriction construction, using the first
projection. Each slice has the original underlying function, and its
additivity and scalar compatibility follow pointwise.

For a distribution S on Y, `Distribution.partialApplySnd S` sends a test
f on X × Y to the actual function `x ↦ S(sliceSnd f x)`, packaged as a test
on X. To prove this is a test, the implemented proof uses the already
published finite expansion `f(x,y) = Σⱼ aⱼ(x)bⱼ(y)` from
`SchwartzBruhat.exists_tensor_expansion`. That published expansion uses
`isLocallyConstant_curry` and `hasCompactSupport_curry` to obtain a finite
expansion of the function-valued curry. Its slices are
`Σⱼ aⱼ(x) • bⱼ`, so linearity of S gives the finite test combination
`Σⱼ S(bⱼ) • aⱼ`. Membership in the existing test submodule follows from its
closure under finite sums and scalar multiplication. Thus arbitrary
algebraic functionals suffice; no continuity is assumed. This avoids
choosing an inverse of an unproved tensor equivalence.

`Distribution.partialApplyFst T` analogously sends f to the actual test
`y ↦ T(sliceFst f y)` on Y. The same expansion gives
`Σⱼ T(aⱼ) • bⱼ`. Both maps are complex linear in f by the pointwise slice
laws and linearity of the functional. On external-product tests their
values are respectively `S(g) • f` and `T(f) • g`.

## Distribution product

`Distribution.tensor T S` is the composition of T with
`partialApplySnd S`, hence is an actual complex-linear functional on
`SchwartzBruhat (X × Y)`. Its definition evaluates in Y first and then in
X. Its external-product formula is `(T tensor S)(f tensor g) = T(f)S(g)`:
apply the partial-evaluation law and the scalar law of T.

`Distribution.tensorBilinear` packages full bilinearity in the two
distributions. Linearity in T is pointwise; linearity in S uses pointwise
additivity/scalar laws of partial evaluation followed by linearity of T.
Four named additivity and scalar laws are exported.

## Scope and provenance

The scalar tensor map needs only the given topologies. The partial maps
and distribution product use Hausdorff X and Y, as required by the reused
slice and finite-expansion constructions. Domain universes are independent.
All empty cases are retained. No measurable structures, measures,
countability, finite-dimensionality or topology on the dual occurs.
This includes Renard's Hausdorff locally compact totally disconnected
spaces; the extension to all Hausdorff spaces is a direct generalization
of this construction, not a claim about the original wording.

The external-product and distribution formulas are the source's maps.
Bilinear packaging, the tensor lift and the named slice/partial maps are
derived implementation interfaces. The proof of partial-test membership
uses the published finite-product expansion; Renard instead describes the
compact-open rectangle expansion on this page. These are compatible finite
sum routes. The tensor-map isomorphism, uniqueness from the pure-product
formula, Fubini equality of the two iterated evaluations, support product
formula and compact-support consequence are separate statement/proof
obligations. This file does not assert any of them.

# Invariance of actual components under algebraically closed field extension

Author: Worker 1107.

`IdentityComponent.AlgebraicallyClosedComponentBaseChangeStatement` is a
proposition declaration. For algebraically closed fields `k` and `L` in the
same arbitrary universe, an actual smooth affine group scheme `H` over
`Spec k`, and any field homomorphism `φ : k →+* L`, it asserts that
`allComponentBaseChange H φ` is bijective. The module supplies no proof of
this proposition.

The source and target are the published finite groups
`AlgebraicallyClosedComponents H` and
`AlgebraicallyClosedComponents ((GroupScheme.baseChange (specMap φ)).obj H)`.
Their carriers are all connected components of the actual underlying schemes.
The homomorphism is the published transport of the ordinary
`rationalComponentBaseChange` through `allComponentQuotientEquiv` at both
endpoints. Its value on the component of a rational section is the component
of the actual pulled-back section, by `allComponentBaseChange_ofPoint`.
The target concerns this particular map.

The published `allComponentBaseChange_injective` already proves injectivity.
The remaining assertion is surjectivity: each actual component after field
extension is the image of a component before extension. The published
`allComponentBaseChange_fst` says that the actual pullback projection on
components is a left inverse. Bijectivity would therefore also make it a
right inverse, without choosing a new reverse map. These observations explain
the target's relationship to existing laws; no new inverse equation is
declared or proved here.

The geometric source is the Stacks Project, Varieties, Lemma 33.7.14,
[Tag 04KV](https://stacks.math.columbia.edu/tag/04KV), in the registered
snapshot
`stacks-04kv-rational-point-geometrically-connected-2026-11-03`, file
`04KV.html`. That lemma gives geometric connectedness from connectedness
and a rational point over the base field. Its more general hypothesis asks
that the base field be relatively algebraically closed in the residue field
of a point. The retained page and current official page have no comments.

The stated component invariance is a derived consequence, rather than a
literal restatement of that lemma. The published rational-representative
theorem supplies a `k`-point in each component. Smoothness and affineness
give finite type over a field, so these components are open and closed
subschemes. Each is connected and has that rational point; Tag 04KV
therefore makes it geometrically connected. Pulling back the component
decomposition gives connected pieces indexed by the original components,
and the pulled-back rational representatives identify the resulting map
with `allComponentBaseChange H φ`. Formalizing this argument, or another
valid argument for the exact proposition, remains a proof obligation.

Characteristic is unrestricted. The homomorphism `φ` is explicit; no
`Algebra k L` instance, algebraicity, separability or finite-dimensionality
of `L/k` is assumed. Both algebraic-closedness hypotheses are retained to
match the published full-component group and extension-map interfaces.
There is no connectedness or reductivity assumption on `H`.

This statement does not compare arbitrary unrelated algebraically closed
extensions, construct an extension-independent geometric component group
or a component-group scheme, descend fixed geometric components to rational
points, or identify a sheaf quotient with a quotient of rational points.
Those remain separate obligations of the standing program.

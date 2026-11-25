# A finite family as an actual affine Weil restriction

This internal construction realizes the finite disjoint-union step in the
proof of Brian Conrad, *Reductive group schemes* (2014), Proposition 6.4.4
and Remark 6.4.5, pp.232–233, registered as
`conrad-2014-reductive-group-schemes`.

Given an arbitrary commutative ring `A`, a finite type `I`, and a family
`H i` of group schemes over `Spec A`, `AffineWeil.FiniteFamily.group`
assembles the family into a group scheme over `Spec(A^I)`. Evaluation at
`i` recovers the original `H i` by an actual group-scheme isomorphism.
Its underlying relative scheme is isomorphic to the disjoint union of the
original groups, with the induced structural map to the product base.
The construction uses `Descent.DisjointGroupAssembly` and the canonical
finite decomposition of the spectrum of a product ring.

The product algebra is finite, projective and étale over `A`. Every
evaluation inclusion is a section of its spectrum map. When `I` is
nonempty this gives surjectivity, even over the zero ring. No
surjectivity claim is made without that condition.

Affineness is inherited from the finitely many component schemes.
Local finite type and smoothness follow by locality on the source and
the open component inclusions. For geometric-fibre properties the proof
chooses a component above a given base point, compares the actual
geometric fibres after base change, and reflects the property along
the compatible field extension. The generic
`geometricFiber_property` states exactly this route, assuming invariance
under isomorphism and reflection along field extension. It yields the
stated reductivity, adjointness and almost-simplicity conclusions from
the original component conditions.

For affine components locally of finite type, `FiniteFamily.iso`
identifies the original categorical product with the actual
`AffineWeil.groupScheme A (I → A)` of the assembled group. It composes
the product of the component recovery isomorphisms with the inverse
of the split-product-base Weil comparison. Every group,
ring and scheme lies in the arbitrary universe `u`; the construction
allows an empty family and imposes no field, characteristic or
reducedness hypothesis on `A`.

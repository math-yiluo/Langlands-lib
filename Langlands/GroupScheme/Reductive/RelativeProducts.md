# Products of reductive group schemes over an arbitrary base

`RelativeReductiveProductStatement` asserts that the binary product of two
reductive group schemes over any scheme `S` is reductive over `S`, in every
universe. `relativeReductiveProduct` proves the statement, and
`IsReductive.tensor` provides the implication for supplied groups.
There are no additional hypotheses on the base or the factors.

This is an internal consequence of the existing definition of reductivity,
smoothness of products, affine morphism properties and the proved field-level
product theorem. It supplies the reductivity of the source `Z ⊗ D` when applying
a fibrewise central-isogeny criterion in
`Reductive.DerivedCentralIsogenyStructuralReduction`, which imports this module.
It does not establish
existence of `Z`, preservation of maximal centrality on fibres or the
multiplication central isogeny itself.

The implemented proof forms the actual categorical product of the supplied
group schemes. Its structure morphism is smooth by `smooth_tensor`. It is
affine because it is the composite of a pullback of the second factor's affine
structure morphism and the first factor's affine structure morphism.
For each geometric point of the base, `baseChangeTensorIso` identifies the
actual geometric fibre of the product with the product of the two geometric
fibres. Both fibres are pseudo-reductive by the original hypotheses. The
published `DirectProduct.isPseudoReductive_tensor` and invariance under
group-scheme isomorphism give precisely the geometric-fibre pseudo-reductivity
required by `IsReductive`.

# Quotients of integral character-kernel centralizer fibres

This internal construction transfers the existing field centralizer quotient
to the actual fibre of the relative identity component in
`IntegralModel.KernelCentralizerData`. It works at arbitrary universe `u`.
The fibre point `b : Spec k → Spec R` is any field-valued point of the integral
base; in particular it can be the residue point.

The torus comparison, full kernel geometry, smooth surjectivity and packaged
quotient require a supplied witness `hT : IsSplitTorus T.toGrp`.
`KernelCentralizerData` does not itself include this hypothesis.

Fix the original integral torus map `i : T → M.group`, its character `a`,
and centralizer data `D`. Given an ambient fibre homomorphism
`q : M.group_b → H` and a smooth affine representative `jE : E → H` of
the full character-kernel centralizer for `i_b ≫ q` and `a_b`,
`D.fibreQuotientMap b q hE` is the composite

```text
(D.componentGroup)_b → ((D.fullGroup)_b)⁰ → E⁰.
```

The first arrow is exactly `(D.fibreIso b).hom`. The second is the existing
`RelativeRoot.kernelCentralizerIdentityMap`, using
`D.fullFibreRepresents b`, the original base-changed torus inclusion and
the original base-changed character. The full character kernel is retained,
even when the character is zero or nonprimitive or its kernel is not smooth.

`fibreQuotientMap_comp_ambient` records the exact equality of homomorphisms
after composition with `E⁰ → E → H`: this is the base change of
`D.componentHom ≫ D.fullHom` followed by the supplied `q`.
`fibreQuotientMap_torus` says the base change of the specified integral
torus factor maps to the canonical torus factor in `E⁰`, assuming `hT`.
These statements use the existing fibre-isomorphism ambient and torus
equalities and the corresponding field-quotient equalities.

On every relative test scheme, `fibreQuotientMap_eq_one_iff` detects identity
by the ambient quotient map. Its proof uses the exact ambient square and
monicity of `E⁰ → E → H`.
`fibreQuotientMap_ne_one_of_ambient` supplies the resulting nonidentity
implication, in the direction needed for integral root-lifting applications.
The map, its ambient square and these two identity-detection results do not
require `hT`.

Suppose `hT : IsSplitTorus T.toGrp` is supplied, `H` is affine, `k` is perfect
and the actual full kernel of `q` is smooth, connected and unipotent.
`fibreQuotientMap_kernel_geometry` transfers that same conclusion to the
full actual kernel of the fibre quotient. The field
`kernelCentralizerIdentityMap_kernel_geometry` theorem supplies the
geometry for the ordinary component quotient. `kernelSquareIso` identifies
the two actual kernels through `D.fibreIso b`, and
`smooth_connected_unipotent_of_groupIso` transports the three properties.
The only closed centralizer inclusion used is
`D.fullClosed.baseChange b`.

Given `hT`, if the ambient integral model and `H` are smooth and `q` is smooth,
`fibreQuotientMap_smooth_surjective` proves smoothness and scheme
surjectivity by composing the existing ordinary component quotient with
the fibre isomorphism.
Under these combined hypotheses, including `hT`, perfectness of `k`,
affineness of `H` and the ambient full-kernel geometry, `D.fibreQuotient`
packages that same actual map with these two properties and its full smooth
connected unipotent kernel.

The provenance is internal composition of the named existing constructions.
This unit provides a fibre quotient and its exact comparison maps; integral
opposite factors and the descended facet derivative root datum require
further arguments.

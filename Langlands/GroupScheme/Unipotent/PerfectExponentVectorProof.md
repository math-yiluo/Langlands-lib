# Groups of exponent `p` over perfect fields are vector groups

`Langlands.GroupScheme.perfectFieldExponentVectorGroup` proves the published
`Langlands.GroupScheme.PerfectFieldExponentVectorGroupStatement.{u}`. It gives
an isomorphism of group schemes from a smooth connected commutative affine
group over a perfect field of characteristic `p` to a standard vector group,
assuming the `p`-th power of every point on every relative scheme test is the
identity.

## Implemented proof

Take the affine coordinate Hopf algebra `A` and the canonical isomorphism
`Spec A ≅ G`. Smoothness gives finite type, and smoothness and connectedness
transported to `Spec A` give `IsDomain A` by
`GradedHopf.isDomain_of_hopfSpec`.

`AffineCoordinates.adjoin_primitive_eq_top_of_smooth_uniformExponent` uses
commutativity, smoothness and the exponent hypothesis. The latter applies in
particular to the test scheme given by the algebraic closure. The resulting
geometric point calculation and descent of generation by primitives show
that the primitive elements generate `A` over the original field.

Take a shortest primitive generating tuple using
`PTorsionHopf.exists_isPrimitiveGenerating` and `Nat.find`. Its evaluation
map from the polynomial algebra is surjective by generation.
`PTorsionHopf.injective_aeval_of_minimal` gives injectivity using that `A` is
a domain and that Frobenius on the ground field is bijective. This lemma
reduces a minimal-degree relation to additive polynomials. In the ensuing
Euclidean reduction, surjectivity of Frobenius lets one cancel leading
terms and ultimately remove a generator. `HopfPrimitive.isoVectorGroup`
turns the bijective evaluation on primitive elements into a group-scheme
isomorphism `Spec A ≅ 𝔾ₐʳ`. Compose it with `G ≅ Spec A`.

## Source

This is Proposition 14.54 in J. S. Milne, *Algebraic Groups* (2017),
printed p. 297, registered as `milne-2017-algebraic-groups`. Milne uses
elementary unipotence and freeness of the torsion-free module of primitive
functions over a twisted polynomial ring (14.45–14.51, pp. 295–297).
The Lean proof uses the Library's primitive generation descent and the
minimal tuple argument above.

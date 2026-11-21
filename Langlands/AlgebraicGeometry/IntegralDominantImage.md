# The schematic image of an integral dense factor of a monomorphism

Let `f : X ⟶ Y` be a quasi-compact monomorphism locally of finite
type, with `Y` integral and with normal stalks. Let `a : Z ⟶ X` be a
quasi-compact morphism from an integral scheme such that `a ≫ f` is
dominant. The schematic image of `a` is integral. Its closed immersion
into `X` followed by `f` is still a quasi-compact monomorphism locally
of finite type. The composite is dominant because `a ≫ f` factors
through it. The normal-target monomorphism lemma makes this composite
an open immersion.

`integralDominantImageOpen` is the range of this immersion, and
`integralDominantImageOpenLift` is the lift of its inclusion to `X`.
The lift uses the isomorphism from the schematic image to its open
range.

Suppose `s : S ⟶ X` has reduced source, and the composite of `s` with
a dominant morphism into `S` factors through `a`. The preimage under
`s` of the schematic image of `a` is closed on points and contains a
dense set. The entire image of `s` therefore lies in the schematic
image, and reducedness gives a scheme morphism lifting `s` to it.
Consequently `s ≫ f` takes values in the constructed open.

These are internal consequences of the Library's schematic image and
reduced-source lifting lemmas and the open immersion criterion in
`NormalDominantMono`. For the relative torus application, `Z` is the
generic fibre of a pullback and `s` is its unit section over the base.

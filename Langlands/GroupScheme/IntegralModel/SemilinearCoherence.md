# Integral semilinear coherence from generic rigidity

This internal construction proves the semilinear tower law for actual
integral models from compatible generic semilinear isomorphisms and their
tower law. It then constructs actual integral Čech descent data on a supplied
finite normalized component cover. All rings and schemes have arbitrary
common universe `u`.

`GenericSemilinearCompatible` records the exact generic semilinear identity:
the pullback of the chosen generic identification followed by a specified
generic semilinear isomorphism equals the commuting-square comparison
followed by the generic pullback of the integral isomorphism and the chosen
identification. This is an explicit compatibility condition on actual maps.

`semilinear_tower_of_generic` proves that a generic tower law forces the
integral tower law. The proof compares the two integral maps on their generic
fibres and uses the square tower comparison and its naturality to reduce the
comparison to the supplied generic tower law. Its source is the actual
twice-twisted integral model. Generic rigidity applies because that model is
flat and the target model is affine. This coherence proof uses neither
smoothness nor a homomorphism extension property.

`datumOfGenericSemilinear` assumes a map from the integral base scheme to an
arbitrary base and a finite family of normalized components of its actual
double overlap. The first projection of each component is the identity, the
second is its given integral endomorphism, and the coproduct of the components
maps isomorphically to the overlap. The integral and generic endomorphisms
have explicitly compatible multiplication laws and commute with the
fraction-field inclusion. From supplied integral and generic semilinear
isomorphisms, their exact generic compatibility, and the generic tower law,
the construction proves integral coherence and applies the published finite
component assembly. `pullIso_datumOfGenericSemilinear` recovers precisely the
original normalized integral components.

For a model of a group pulled back from a smaller field,
`galoisDescentIso_tower` proves the tower law for the named canonical Galois
comparison by the general canonical descent tower law. The construction
`datumOfStableGaloisPoints` uses actual integral isomorphisms obtained from
`galoisTwistIso`. It assumes the fixed-ring property
`HasSmoothHomExtension`, smoothness of the model, invertibility of the
integral base maps, and stability under the specified field automorphisms and
their inverses. Both the finite normalized component cover and the compatible
integral and field automorphism multiplication laws remain supplied inputs.
`pullIso_datumOfStableGaloisPoints` recovers exactly those constructed
integral Galois isomorphisms, with the standard normalized-component
orientation.

The construction is an internal consequence of actual pullbacks, generic
rigidity, the canonical semilinear comparison and finite component descent
assembly. It does not assert that the fixed-ring extension property holds or
that any particular arithmetic cover supplies the required finite components.
It constructs an actual datum under its stated premises, but no effective
solution of that datum or final descended model, and does not prove KP Fact
2.10.16.

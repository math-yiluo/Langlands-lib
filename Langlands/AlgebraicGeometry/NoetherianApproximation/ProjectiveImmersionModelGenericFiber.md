# Original generic fiber of a constructed projective-immersion model

This derived construction connects the actual projective-immersion models to
the original field schemes in Conrad, *Weil and Grothendieck approaches to adelic
points* (2011), Example 4.2, printed pages 9–10. It uses the constructed
`ProjectiveImmersionRingModelData` interface already instantiated by the actual
arithmetic model-existence constructions.

`asOver` regards the actual model as a scheme over the original coefficient
spectrum, using the given relative projective immersion followed by the
projective structure map. Scoped instances derive local finite type,
quasi-compactness and separatedness for this structure map. Local finite type
comes from the recorded local finite presentation, and quasi-compactness is the
recorded property of that very map. Separatedness and affine neighborhoods of
every finite subset follow from the specified immersion into actual projective
space. These are properties of the actual constructed model.

`genericFiberIso` constructs an isomorphism over the original field spectrum
between the actual field base change of the model and the original scheme with
structure map given by the specified original projective immersion. The recorded
Cartesian square supplies its canonical isomorphism with the literal pullback;
`Over.isoMk` retains the original field structure map. No additional generic-fiber
isomorphism is assumed.

The two first-projection identities identify the inverse isomorphism's projection
with the originally constructed model comparison, and recover the first
projection from the forward isomorphism followed by that comparison.
`genericFiberIso_originalImmersion` combines the first identity with the recorded
original-immersion equality. Consequently the generic-fiber identification also
retains the originally specified projective map, rather than only the underlying
scheme up to an unspecified isomorphism.

The coefficient ring and field inhabit an arbitrary common universe. Only the
commutative coefficient ring, its algebra into the field, and constructed model
data are needed; no global-field or separability hypothesis occurs in this
geometric construction. Actual model existence is supplied separately. Joining
this identification to the integral Weil generic-fiber construction and proving
the adelic topological comparison remain obligations of the host task.

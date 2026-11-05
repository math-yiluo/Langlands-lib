# Actual number-field S-integer Weil generic fiber

This derived construction supplies the generic-fiber identification for the
number-field integral Weil model in Conrad, *Weil and Grothendieck approaches to
adelic points* (2011), Example 4.2, printed pages 9–10. It uses the actual lower
S-integer ring and the actual upper S-integer ring at the full inverse image of
the lower exceptional set, with their original field embeddings.

For a scheme Y over the upper ring, locally of finite type and equipped with a
specified relative immersion into a finite-dimensional projective space,
`numberFieldSIntegersWeilGenericFiberIso` constructs an isomorphism over the
spectrum of the original lower field. Its source is the base change to that
field of the actual integral Weil-restriction scheme. Its target is the actual
field Weil-restriction scheme of the original upper-field base change of Y.
The displayed immersion is relative to Y's given structure map. No assumption
that the desired generic-fiber identification already exists is used.

The construction instantiates
`projectiveImmersionIntegralClosureWeilRestrictionGenericFiberIso` with these
exact S-integer rings. `NumberFieldSIntegerFinite` proves that the upper ring is
the lower ring's integral closure in the original upper field and is a finite
projective lower module. The original lower field is the fraction field of the
lower ring. The given projective immersion supplies separatedness and affine
neighborhoods of finite subsets, which are the geometry needed by the existing
Weil construction. Localization of the integral closure gives the actual tensor
identification with the upper field and retains both original coefficient maps.

`numberFieldSIntegersWeilGenericFiberIso_comparison` proves compatibility on every
test scheme over the original lower field and every morphism from it into the
source. Applying the field Weil counit after the isomorphism is exactly the
specified integral counit comparison through the original fraction-tensor
identification. Thus the constructed isomorphism identifies the intended point
maps as well as the underlying schemes.

Both number fields inhabit an arbitrary common universe. The finite exceptional
set may be empty. The construction assumes local finite type, not a separate
global finite-type conclusion. The function-field S-integer finite-local-freeness
input and the adelic topological Weil comparison remain obligations of the host
task.

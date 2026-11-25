# Fibrewise reductive and semisimple locus comparisons

This internal derived module compares the actual geometric fibre
conditions used by `DirectLimitReductiveStatement`. It assumes a smooth affine
group scheme over an arbitrary scheme and imposes no connectedness condition
unless the theorem states it explicitly.

`identityComponentSemisimpleLocus G` consists of the points whose actual
geometric fibre has semisimple identity component. Its fullness is exactly the
universal fibrewise condition, as recorded by
`identityComponentSemisimpleLocus_eq_univ_iff`.

The scalar-extension comparison first uses
`IdentityComponent.baseChangeIso`, the published preservation theorem
`isSemisimpleFieldExtension`, and `IsSemisimple.of_fieldExtension`. It therefore
preserves and reflects semisimplicity of the actual identity component for
every field extension. For an arbitrary field-valued point,
`fieldPointIdentityComponentIso` identifies its identity component with the
scalar extension of the residue-field fibre's identity component. The same
preservation and reflection prove the residue-fibre comparison. Applying it
to the chosen geometric point proves that the locus is independent of the
chosen algebraic closure. The image of this point is the original base point
by `Scheme.fromSpecResidueField_apply`.

Finally `baseChangeCompIso` compares a geometric fibre after any scheme base
change with the field-valued pullback along the composite. The field-point
comparison then proves `identityComponentSemisimpleLocus_baseChange` as an
exact preimage equality, without choosing compatible residue-field algebraic
closures. No relative identity-component model is required.

The last three lemmas compare whole-group conditions with loci. A reductive
group scheme is geometrically connected, since its pullback at every
field-valued point is connected reductive. Its geometric fibres, and hence
their identity components, are reductive. Conversely, geometric connectedness
makes each geometric fibre connected. Its actual identity-component inclusion
is then an isomorphism, so fullness of the reductive locus supplies the
pseudo-reductive geometric fibres required by `IsReductive`.

The same connected identity-component isomorphism compares semisimplicity of
whole geometric fibres with fullness of the semisimple locus. Thus the relative
semisimple condition (`IsReductive` together with semisimple geometric fibres)
is equivalent to geometric connectedness and fullness of that locus. In the
reverse direction semisimplicity itself supplies reductivity of every fibre.

These are consequences of existing Library definitions and transport results;
no new source assertion, openness theorem, constructibility theorem, or
direct-limit theorem is assumed or proved here. The intended application is
to combine the preimage equalities and connectedness comparisons with separate
open/constructible-locus detection along direct limits.

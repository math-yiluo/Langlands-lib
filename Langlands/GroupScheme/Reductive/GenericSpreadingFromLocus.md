# Generic spreading from openness of the identity-component locus

This derived unit proves
`IdentityComponentReductiveLocusOpenStatement.{u} →
GenericReductivitySpreadingStatement.{u}`. The openness proposition remains
an explicit premise. This file neither proves that structural proposition
nor establishes the unconditional generic spreading target.

`geometricPointScalarMap R s` represents the actual morphism
`geometricPoint (Spec R) s` by a ring homomorphism from `R` to the specified
algebraic closure of the residue field. It uses the fullness of `Spec`.
`geometricPointScalarMap_spec` records equality with that exact geometric
point. Thus the construction preserves the original base point and the
chosen algebraic closure; it does not choose a different fibre.

`connected_geometricFiber_of_fieldConnected` equips that closure with the
algebra structure defined by this map. Its closed point maps to `s`, by the
residue-field point formula. Membership of `s` in `D(r)` is therefore exactly
nonvanishing of `r` under the constructed coefficient map. The premise on
all field-valued points gives connectedness of the actual geometric fibre.

The conditional theorem starts with the original domain, supplied fraction
field and group in `GenericReductivitySpreadingStatement`. The actual
fraction-field fibre descends to the generic residue-field fibre by
`genericResidueReductive_of_fractionFieldReductive`. Preservation under
extension to its algebraic closure and `baseChangeCompIso` give connected
reductivity of the single pullback defining the geometric generic fibre.
Its identity component is reductive, so the generic point belongs to the
identity-component reductive locus.

The assumed openness yields a principal open `D(r₂)` containing the generic
point inside that locus. The published
`exists_principalOpen_connected_fibers` separately gives `D(r₁)` on which
every supplied field-valued fibre is connected. Both coefficients are
nonzero. Their product is chosen before quantifying over the field and its
algebra structure.

For each such field point with nonzero product, its image belongs to both
principal opens. The geometric-fibre connectedness lemma makes the
identity-component locus comparison applicable, giving connected
reductivity of the whole actual geometric fibre. Pullback composition
identifies it with the residue fibre followed by algebraic closure.
Reflection under field extension gives residue-fibre reductivity, and
`fieldReductive_iff_residueReductive` gives reductivity of the original
specified field-valued pullback. This proves precisely the target
conclusion, conditional on openness, uniformly in arbitrary universe `u`.

The provenance is internal composition of the named Library results and
Mathlib's full affine-spectrum functor, residue-field point formula and
principal-open basis. No additional external structural theorem is claimed.

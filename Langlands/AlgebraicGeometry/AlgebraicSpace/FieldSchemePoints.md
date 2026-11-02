# Closed points on schemes locally of finite type over fields

This internal module derives helpers from Mathlib's existing Jacobson-space,
closed-immersion and finite-morphism theorems. The base field is arbitrary,
and no quasi-compactness assumption is imposed.

`jacobsonSpace` applies Mathlib's theorem that local finite type preserves
the Jacobson property, starting from the spectrum of a field.
`exists_closed_specialization` applies the nonempty closed-point intersection
criterion to the closure of a singleton. Membership in that closure is
precisely specialization from the original point. `exists_closed_mem_open`
applies the same criterion to a nonempty open, which is locally closed.
The resulting point is closed in the entire scheme.

`residueFieldAlgebra` specifies the algebra structure through the ring
morphism obtained by `Spec.preimage` from the composite of the canonical
residue-field point and the structure morphism.
`residueField_finiteDimensional` proves that this algebra is finite
dimensional at a closed point. Its residue-field point is a closed immersion,
so its composite with the structure morphism is locally of finite type.
Since its source is the spectrum of a field and its target is Jacobson,
Mathlib identifies this composite as finite. The affine criterion for a
finite spectrum morphism gives the claimed finite module, with exactly
the specified algebra structure.

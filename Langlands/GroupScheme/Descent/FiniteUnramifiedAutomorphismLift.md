# Compatible finite and maximal-unramified coefficient automorphisms

This internal construction supplies the actual field and integer spectrum
maps needed for semilinear coefficient descent. The base F is a
nonarchimedean local field at arbitrary universe `u`, with its published
canonical norm, and E is a specified intermediate field of its separable
closure contained in the actual inertia fixed field. The constructions work
without a finiteness or Galois assumption on E, so in particular apply to the
finite Galois unramified stages used by the model construction.

`liftAutomorphism` extends a supplied F-algebra automorphism of E to an
F-algebra automorphism of `inertiaFixedField F`. It installs the actual
inclusion E into the inertia fixed field as the algebra structure and uses
normal extension of field automorphisms. Normality is provided by the
published Galois instance on the inertia fixed field.
`liftAutomorphism_commutes` proves exact restriction along that specified
inclusion. A lift is chosen separately for each automorphism; no compatibility
of the choices with multiplication is asserted.

`fixedFieldIntegerAut` restricts an automorphism of the inertia fixed field
to the actual `fixedFieldIntegers F`, using the spectral-integer
presentation and the published same-element ring equivalence. Its underlying
field value is exactly the original automorphism. `fixedIntegerBaseAut` is
its actual spectrum map and is invertible.

The field and integer automorphisms commute with both generic inclusions,
as proved in `fixedIntegerBaseAut_generic` and
`finiteIntegerBaseAut_generic`. The theorem
`liftAutomorphism_fieldSquare` proves the coefficient square between E and
the inertia fixed field. The equality
`spectralIntegerInclusion_inertia` identifies the published spectral integer
inclusion with precisely the specified field inclusion. It converts exact
restriction of the field lift into `liftAutomorphism_integerCommutes` and
`liftAutomorphism_integerSquare` for the actual spectral integer maps. These
are equalities of the concrete ring homomorphisms and spectrum maps, with no
unspecified comparison embedding.

`spectralIntegerMap_fpqc` proves that this actual integer coefficient map is
surjective, flat and quasi-compact. The spectral norm tower identity makes
the fixed-field valuation extend the spectral valuation on E. The published
valuation-integer fpqc theorem therefore applies. Comparing the resulting
integer algebra map with the same-element spectral inclusion identifies its
spectrum map with `spectralIntegerMap` exactly. This argument also needs no
finiteness or Galois assumption on E.

These are internal consequences of normal field-automorphism extension,
spectral norm invariance and tower identities, and the published integer-map
and valuation-cover constructions. They construct no finite model, upstairs
integral semilinear isomorphism, coherent choice of lifts or final descended
model and do not prove KP Fact 2.10.16.

# Adjoint scalar extension of associated coefficient sheaves

This internal construction uses the actual small-etale site of a scheme `X`,
a group action `Y` on an object of that site, and a homomorphism of commutative
rings `φ : R →+* S`. The scheme, rings, module carriers and group share universe
`u`, as required by the existing small-etale scalar-extension adjunction.
Coefficients are arbitrary sheaves with a `G`-action on this fixed site.

Write `E` for `sheafExtendScalars φ X` and `U` for `sheafRestrictScalars φ X`.
The functor `E` tensors the section modules and sheafifies; the existing
adjunction `E ⊣ U` supplies its unit. Naturality of this unit for every action
operator constructs `coefficientExtensionActionUnit`, an equivariant map
`F → U_* E_* F`, natural in coefficient actions.

Applying the associated invariant-sheaf functor and then the inverse of
`associatedRestrictScalarsIso` gives `associatedExtensionUnit`:
`Assoc_R(F) → U(Assoc_S(E_* F))`.
Its inclusion formula follows from naturality of the invariant inclusion and
the inverse restriction-isomorphism normalization.

`associatedExtendScalarsComparison` is the adjoint transpose
`E(Assoc_R(F)) → Assoc_S(E_* F)`. Its naturality follows from the source and target
naturality of the adjunction's universal lift. The unit equation and uniqueness
are the corresponding universal properties of that lift. The final
unit-and-inclusion formula says that, after restriction and precomposition with
the unit, the comparison agrees with the product-section map induced by the
coefficient unit.

The provenance is categorical: this module derives its maps from the existing
associated invariant limit, its scalar-restriction comparison, and the
small-etale tensor-sheaf adjunction. It does not transcribe a literature theorem.
No flatness, group finiteness or torsor premise is required. No invertibility of
this comparison, commutation of tensor with invariants, constant-module
transport, or Harris geometric specialization is asserted.

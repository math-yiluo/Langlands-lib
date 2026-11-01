# Actual imaginary quadratic tensor factors as module sheaves

This is an internal construction from the actual module tensor-factor equivalence
and its semilinear naturality, applied to sections of a module sheaf. Let `L` be an
imaginary quadratic CM number field and let `K` be a characteristic-zero field
containing `L`. Let `S` be a scheme with compatible `K`- and rational-algebra
structures on its global regular functions. Let `M` be an actual `S.Modules`
object with a unital ring action `ρ : L →+* End M`. There is no finiteness,
flatness, reducedness or local-freeness hypothesis on `S` or `M`.

For each open `U`, `sectionScalarAlgebra` restricts the global scalars to
`R_U = Γ(S,U)`, and the rational scalar tower is proved. `sectionFieldAction`
evaluates the actual sheaf action on `Γ(M,U)`. Its extension makes this section
module a module over `R_U ⊗[ℚ] L`. For a Boolean `conjugate`, the coordinate
character is the structural embedding for `false` and its composition with CM
conjugation for `true`. `sectionFactorCharacter_eq` proves that this character
is the restriction of the corresponding global character.

`sectionTensorFactor` is the actual scalar-extension module
`R_U ⊗[R_U ⊗[ℚ] L] Γ(M,U)`, with `R_U` an algebra over the tensor ring through
the selected coordinate. The previously constructed `tensorFactorEquiv`
identifies it with the full simultaneous eigenmodule. `sectionEigenEquiv`
identifies that eigenmodule with the sections of `scalarEigensheaf` by checking
the defining equality for every `t : L`. Their composite `sectionTensorEquiv`
is an actual linear equivalence to all eigensheaf sections.

For an inclusion `j : U ⟶ V`, `sectionRestrictionAlgebra` constructs the map
`Γ(S,V) →ₐ[K] Γ(S,U)` and proves preservation of the structural scalars.
`sectionTensorRestriction` applies the constructed semilinear tensor-factor map
to the actual restriction of sections. The intertwining equation follows from
naturality of each `ρ(t)`. `sectionTensorRestriction_tmul` proves the canonical
formula `r ⊗ m ↦ r|_U ⊗ m|_U`, and `sectionTensorEquiv_restriction` proves that
the sectionwise equivalences commute with these restriction maps. The formula
also identifies the map on all elements because pure tensors generate the tensor
product additively.

`tensorFactorPresheaf` uses precisely these tensor modules and restriction maps.
Identity and composition follow by applying the injective section equivalences
and the corresponding laws of the eigensheaf restrictions.
`tensorFactorPresheafIso` assembles the equivalences into an isomorphism of
presheaves of modules. The sheaf condition is transferred along its underlying
abelian-presheaf isomorphism from the full eigensubsheaf, which is already a
sheaf. Thus `tensorFactorSheaf` is an actual module sheaf, with the specified
tensor module on every open; no further sheafification changes its sections.
`tensorFactorSheafIso` lifts the constructed presheaf isomorphism to an
isomorphism in `S.Modules`.

This unit supplies a generic tensor-factor/eigensheaf comparison. It does not
assert local freeness, a prescribed rank, compatibility of additional totally
real actions, or commutation with pullback along an arbitrary scheme morphism.
Specializing it to the differentiated Harris algebra action is a separate step.

# Local anisotropic Cartan components from actual factors

This internal reduction records the precise consequence of actual component
realization needed for anisotropic kernels in the local rank-one problem.

For an actual index `d`, `HasInnerTypeAComponent d a` says that the component
containing `a` has a numbering by `Fin n` for some positive `n`, preserving every
entry of the type-A Cartan matrix. It also says that every element of the full
absolute Galois group taking `a` into its component fixes every vertex of that
component. It permits the full action to permute distinct components.

`LocalAnisotropicCartanComponentsStatement` asserts this predicate for every
vertex of every actual index of an affine anisotropic semisimple group of locally
finite type over every nonarchimedean local field. Semisimplicity is supplied
by the actual index. This module does not prove the statement unconditionally.

The implemented theorem
`localAnisotropicCartanComponents_of_componentFactor` has two explicit premises:
`SemisimpleTitsComponentFactorStatement` and `LocalAnisotropicTypeAStatement`.
It uses the already published theorem `localAnisotropicTypeAInner`; it does not
assume a new inner-type-A result.

Given a vertex, the first premise supplies an actual absolutely almost-simple
simply connected factor `H/E` and its actual index `e`. The finite extension
`E/k` is equipped with the spectral norm, valuative relation and
nonarchimedean local-field structure constructed in
`Langlands.LocalField.FiniteExtension`. The witness transfers anisotropy to `H`.
The second premise gives a positive type-A numbering of `e`. Compose it with
the inverse witness equivalence to number the original Cartan component.
The witness's Cartan identity proves equality of every transported entry.

For a full absolute Galois element preserving the component, the witness supplies
one absolute Galois element of `E` with the same action on every corresponding
vertex. The published inner-type-A theorem makes that element act trivially on
`e`, so the original element fixes every vertex of the component.
This uses the stabilizer-lifting direction of the witness; its reverse lifting
and actual central cover are retained in the structural interface.

The reduction holds at every universe parameter and in every field and residue
characteristic. Its provenance is composition of the stated structural premise,
the stated local absolute-type premise, and the published local inner-type and
finite-extension theorems. Neither the structural premise nor the local absolute
type-A premise is discharged here, and the rank-one enumeration remains open.

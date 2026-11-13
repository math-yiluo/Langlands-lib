# Relative derived sections and derived Hom

This internal supporting construction specializes
`DerivedSectionsHomComparison.comparison` to relative global sections of modules
on a scheme over `Spec R`. It does not assert compatibility with pullback.

For a structural arrow `f : X ⟶ Spec R`, `relativeSectionsHomIso` identifies
relative sections after forgetting scalars with Hom from the actual constant
integer sheaf to the underlying abelian sheaf. It composes the existing relative
sections/absolute sections comparison, `globalSectionsIso`, and the inverse of
`AbelianSheafDerivedSections.homGlobalSectionsIso`.

`relativeDerivedHomComparison f n` is the generic natural comparison for this
identification. Its source is degree `n` cohomology of the right-derived relative
sections, followed by scalar forgetting and the universe lift. Its target is Hom
in the derived category of abelian sheaves from the degree-zero integer sheaf to
the shift by the integer `n` of the exact underlying-sheaf image. The standard
derived-category universe is `u+1`, so the source groups are lifted accordingly.

`isZero_rightDerived_integerHom_of_injective` proves that the underlying sheaf
of an injective module is acyclic for Hom from the integer sheaf. The proof uses
the published acyclicity for sheaf global sections and transports its vanishing
along `homRightDerivedIso`. It makes no assertion that the underlying sheaf is
injective. `relativeDerivedHomComparison_isIso` then applies the generic
acyclicity criterion to show this natural comparison is invertible in every
integer degree.

The provenance is internal: this is a specialization of existing canonical
comparisons and acyclicity results, rather than a transcription of an external
statement. The later identification with `relativeHAddEquiv` and compatibility
with arbitrary pullback are separate obligations.

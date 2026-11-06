# Actual sheaf cohomology on any injective resolution

Let `X : TopCat.{u}` be an actual topological space, `F` an actual abelian
sheaf on `X`, and `I` any supplied injective resolution of `F`.
For every nonnegative degree, `resolutionGlobalSectionsHomologyEquiv X I n`
is an additive equivalence from Mathlib's actual Ext-defined `Sheaf.H F n`
to degree-`n` homology of actual global sections of `I.cocomplex`.

The definition first applies the existing
`ExtRightDerived.extAddEquivHomology (constantIntegers X) I n` and then the
homology isomorphism of the actual termwise `homGlobalSectionsIso X`.
The constant integer sheaf, Hom-to-sections isomorphism, Ext groups and
sections functor are exactly the published constructions.

`HAddEquiv_eq_of_resolution` identifies the unchanged published
`AbelianSheafDerivedSections.HAddEquiv X F n` with this resolution
homology equivalence followed by the inverse of the canonical
`I.isoRightDerivedObj (globalSections X) n`. The result retains the actual
comparison maps and is valid for every supplied injective resolution,
not only the chosen one.

The proof uses
`ExtRightDerived.extAddEquivRightDerived_eq_of_resolution` from the included
`ExtAdjunctionResolution` helper to compute the Ext/right-derived Hom
comparison on `I`. It applies Mathlib's
`InjectiveResolution.rightDerived_app_eq` to the Hom-to-sections natural
transformation. Precomposition by the inverse Hom-resolution isomorphism
cancels its forward map. Evaluating the resulting equality of morphisms on
the actual Ext/Hom-homology class proves the claimed formula.

The provenance is internal: this is a resolution formula for the existing
actual cohomology comparison. The included helper also packages the actual
Hom adjunction, proves its compatibility with Ext cocycles and Hom-resolution
homology, and normalizes the Ext/right-derived comparison on any supplied
resolution. These are the resolution comparisons needed for the cross-space
sheaf-cohomology argument. Identification with the actual Ext-defined
homeomorphism pushforward equivalence, actual Picard obstruction naturality,
and the exact field Picard-stack atlas remain further obligations.

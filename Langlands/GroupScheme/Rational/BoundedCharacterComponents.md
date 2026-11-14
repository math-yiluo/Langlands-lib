# Character components of bounded functions

This internal helper develops the character argument needed for the descended
apartment comparison. It does not yet state or prove that comparison.

`character_component_mem` proves that a subspace of functions invariant under
left translation contains every character component of a finite sum of distinct
multiplicative characters that it contains. The proof inducts on the finite
set of characters. A translate minus a suitable multiple of the original
function removes one character. Distinctness supplies a translation for which
the desired character's coefficient remains nonzero. Induction and scalar
division recover that component, and subtraction recovers the removed one.

`boundedFunctions` is the subspace of field-valued functions with one nonzero
valuative upper bound. It is the submodule underlying the existing algebra of
bounded evaluations, using evaluation maps on the function algebra.
`boundedFunctions_translate` proves its translation invariance.
`bounded_character_component` applies the first result to this subspace.

These are derived algebraic lemmas. Their provenance is the elementary
translation argument just described; no external mathematical assertion is
assumed.

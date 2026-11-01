# Transport of fixed finite local rank along sheaf isomorphisms

This is a derived helper for the actual fixed-rank predicate
`Langlands.Scheme.Modules.IsLocallyFreeOfRank`. Given an actual isomorphism
`e : M ≅ N` in `S.Modules`, `localGeneratorsDataOfIso` keeps the same
cover and generator index types and applies `GeneratingSections.ofEpi`
to the restriction of `e.hom` on each covering open.

The generating-section map after transport is the original map composed
with the restricted isomorphism, by Mathlib's `GeneratingSections.ofEpi_π`.
If the original generators are a basis, both factors are isomorphisms,
so the transported generators are a basis. The equivalences from their
index types to `Fin n` are unchanged. `IsLocallyFreeOfRank.ofIso` therefore
transports fixed finite rank, and `isLocallyFreeOfRank_iff_of_iso` uses the
inverse isomorphism for the converse. No nonemptiness assumption is used.
This module derives the isomorphism invariance directly from the existing
predicate and Mathlib's actual restriction and generating-section constructions.

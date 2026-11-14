# Character restriction and specialization through integral split tori

This internal unit composes the canonical character constructions of
`FacetLieWeights` with `characterLattice.baseChange_precomp`. It introduces
no independent assertion from the literature.

Let `R : Type u` be a local integral domain and `K : Type u` its fraction
field. Supply two `IntegralTorusData` objects `T` and `T'` over `R`, with
specified generic commutative group schemes `S` and `S'` over `K`. They may
belong to different relative component models and different ambient generic
groups. For an actual integral morphism `ρ : T.torus → T'.torus`,
`genericFibreMap T T' ρ` is the generic base change of `ρ`, conjugated by
the supplied generic isomorphisms. Thus it is an actual morphism `S → S'`.

`genericCharacter_comp` states that the generic character of `ρ ≫ ψ` is
the restriction along this morphism of the generic character of `ψ`.
If both integral tori are split, `characterSpecialization_comp` says

```text
specialize_T (genericFibreMap T T' ρ ≫ χ)
  = (residue base change of ρ) ≫ specialize_T' χ.
```

The character identifications on both sides are exactly the canonical
ones through the supplied integral tori. Consequently
`generic_restriction_eq_zero_iff` and
`generic_restriction_ne_zero_iff` identify vanishing and nonvanishing
of the two restrictions. No injectivity or closedness assumption on `ρ`
is required.

The proof of the generic identity uses functoriality of character base
change and cancellation of the specified isomorphism. For specialization,
lift the generic character to an integral character using
`genericCharacterEquiv`, apply the generic identity and
`characterSpecialization_genericCharacter` on both tori, and use residue
base-change functoriality. The zero equivalence follows from injectivity
and preservation of zero of `characterSpecialization`; the nonzero
equivalence is its negation. These results work at every universe `u`
and in arbitrary field and residue characteristic.

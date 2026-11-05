# Composition of actual relative sections comparisons

This internal construction proves composition for the actual pushforward
and affine-base scalar-restriction comparisons from `PushforwardComparison`,
`DerivedBaseChange` and `BaseChangeResolution`. Schemes and commutative rings
have an arbitrary common universe. There are no closed-immersion, flatness,
properness, quasi-coherence or acyclicity hypotheses.

Let `h : Z → Y` and `j : T → Z`, with base maps `g`, `g'`, `g''` to the
spectra of `R`, `S`, `V`. Ring maps `φ : R → S`, `ψ : S → V` and commuting
squares `h ≫ g = g' ≫ Spec.map φ` and `j ≫ g' = g'' ≫ Spec.map ψ` are supplied.
The existing `sectionsBaseChangeSquare_comp` from
[`SectionsBaseChangeComposition`](SectionsBaseChangeComposition.md) supplies
the resulting square for `j ≫ h` and `φ ≫ ψ` by associativity and
functoriality of `Spec.map`.

`relativePushforwardBaseRingIso` is the canonical isomorphism from
`h_* ⋙ Γ_R(Y,-)` to `Γ_S(Z,-) ⋙ restrictScalars φ`, formed from the
pushforward sections comparison and the inverse base-ring sections
comparison. `relativePushforwardBaseRingIso_comp` identifies its composite
for `j ≫ h` with the two successive comparisons, retaining the canonical
pushforward and scalar-restriction composition isomorphisms. Its proof is
extensional: on the underlying global sections all the maps are identities,
so the equality is definitional.

`resolutionSectionsBaseChangeMap_comp` proves the corresponding equality
for arbitrary nonnegative cochain complexes `K`, `L`, `P` and actual
cochain maps `t : K → h_* L`, `s : L → j_* P`. The composite map is
`t ≫ h_* s` followed by the canonical pushforward composition map. The
sections map of this composite, followed by the scalar-restriction
composition isomorphism on complexes, equals the first sections map followed
by the restriction of the second sections map. The proof compares each
cochain degree, uses the preceding sections comparison, and then uses its
naturality with respect to the component of `s`. The complexes need not be
resolutions, and no claim is made that their terms are injective or acyclic.

These are internal consequences of the named published constructions.
They do not yet assert cohomology transitivity, tensor or obstruction
naturality, or Picard-stack atlas existence.

# Base change of a map induced from an actual affinoid pushout

This internal bounded pushout construction identifies a further base change
of a map induced from one actual affinoid pushout. Let `f : A → B`,
`g : A → C`, `k : A → D`, and `h : C → D` be bounded maps of presented
affinoid algebras with `h.comp g = k`. Let `p : B → E` and `q : C → E`
be compatible over `A`. The actual source map `B ⊗̂_A C → E` is the bounded
pushout lift of `p` and `q`. The actual restriction
`B ⊗̂_A C → B ⊗̂_A D` is the lift of the unchanged `B` leg and the `D` leg
composed with `h`.

`equiv` constructs a bounded equivalence

`E ⊗̂_(B ⊗̂_A C) (B ⊗̂_A D) ≃ E ⊗̂_C D`.

Every displayed tensor product denotes the existing actual affinoid pushout
closed quotient. The forward map is the lift of the original `E` leg and
the map from `B ⊗̂_A D` induced by `p` and the original `D` leg. The inverse
is the lift of the original `E` leg and the composite original `D` leg.
Compatibility follows from the original bounded pushout equations.

The inverse identities are proved as equalities of entire bounded maps,
using pushout extensionality, twice on the side containing two pushouts.
`equiv_comp_right` retains the prescribed entire map out of
`B ⊗̂_A D`. All maps in both directions are constructed by bounded lifts,
so their bounds are outputs of the original universal properties. The
construction retains arbitrary positive polyradii, trivially valued
coefficient fields, zero quotient algebras, and empty spectra.

The provenance is the bounded pushout universal property, applied to this
commutative diagram. No flatness, finiteness, surjectivity, spectral
injectivity, or open mapping theorem is assumed. This construction is used
to identify base changes of the local weighted evaluation quotients in
the effective finite affinoid algebra descent proof.

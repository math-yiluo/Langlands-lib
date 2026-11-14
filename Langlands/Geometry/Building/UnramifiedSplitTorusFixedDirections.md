# Coefficient-fixed directions from a prescribed split torus

This internal construction works over any extension of fields `K/k`, with an
actual commutative group scheme `T`, an actual map `i : T.toGrp ⟶ G` to an
affine group scheme, and a supplied map `f : S ⟶ T` from a split torus over
`k`. It uses the published actual character and cocharacter lattices and the
existing reduced translation space of `i_K`.

`baseChangeCocharacterDirection` sends an actual cocharacter of `T` over `k`
to the quotient class of `1 ⊗ ν_K` modulo the full common root annihilator.
`galoisTranslationAction_baseChangeCocharacterDirection` proves that this
class is fixed by every coefficient automorphism `K ≃ₐ[k] K`. The proof uses
fixedness of a base-changed cocharacter and the existing quotient action.

`exists_baseChangeCocharacterDirection_rootForm_ne_zero` starts with an
actual upstairs root whose restriction along `f_K` is nonzero. The perfect
integral character–cocharacter pairing of the split torus `S_K` gives a
cocharacter with nonzero pairing. Every cocharacter of `S_K` descends to
`S`, by bijectivity of actual cocharacter base change for split tori.
Postcomposition by `f` gives a descended cocharacter of `T`.
Naturality of the lattice pairing, compatibility of cocharacter base change
with postcomposition, and `rootForm_mk` identify its derivative evaluation
with the nonzero integer pairing viewed in `ℝ`.

`exists_galois_fixed_direction_of_root_restrict_ne_zero` combines these
conclusions into a common coefficient-fixed reduced direction on which
the root form is nonzero. It does not require the root itself to be
coefficient-fixed.

`KPApartmentData.hasIncidentGaloisDirections_of_root_restrict_ne_zero`
applies this construction to a supplied apartment and point `p`. Its explicit
premise requires nonzero restriction of every actual derivative root of an
ordinary affine root vanishing at `p`. The result is precisely the previously
defined `HasIncidentGaloisDirections` for that same apartment.

The provenance is internal: this is a composite of the Library's actual
split-torus perfect pairing, split lattice base change, fixedness of descended
cocharacters, pairing naturality, and reduced quotient action. It makes no
new claim about an external source. In particular, nonzero restriction of
incident roots is an explicit input. The residual arithmetic argument that
must establish it for the special-apartment chamber task remains open.

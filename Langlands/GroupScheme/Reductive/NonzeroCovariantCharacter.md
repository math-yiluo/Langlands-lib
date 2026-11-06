# Actual characters and finiteness for arbitrary covariance weights

This derived unit works with arbitrary affine group schemes `G` and `H` over a
field, an actual group morphism `i : H ⟶ G`, and an arbitrary coordinate `χ` of
`H`. It does not initially assume that `χ` is a character.

`exists_normalized_covariant_of_ne_zero` starts from any nonzero coordinate `f`
in the entire left-covariant space of weight `χ`. A linear functional `ψ` on
the coordinate algebra with `ψ(f) = 1` exists because this algebra is a vector
space over a field. Right contraction of the coaction by `ψ` stays in the
same covariance space. The coalgebra counit identity says that the counit of
this contraction equals `ψ(f)`, so the resulting coordinate has counit one.
`covariantNormalization` chooses such a coordinate, and its two specification
lemmas prove counit one and evaluation one at the identity on every relative
test scheme. No unipotence, product-cell factorization, reducedness, geometric
point argument or quotient is needed for this normalization. The normalized
coordinate is not asserted to be fixed by any subgroup.

`nonzeroCovariantCharacter` applies the existing normalized-character recovery
to that coordinate. `characterCoordinate_nonzeroCovariantCharacter` identifies
its actual character coordinate with the original `χ`. The recovery theorem
uses covariance and naturality on all relative scheme tests to construct an
actual group-scheme homomorphism to the multiplicative group.

`characterCoordinate_injective` evaluates equal coordinates on every test
scheme and applies extensionality of rational characters. Thus
`existsUnique_character_of_nonzero_covariant` proves uniqueness of the actual
character for any nonzero covariance space. The converse nonvanishing assertion
is not claimed: an actual character can have zero covariance space.
`leftCovariantSubspace_eq_bot_of_not_character` proves that every other weight
has zero covariance space.

`finite_leftCovariantSubspace_of_proper_quotient` assumes additionally that
`i` is a monomorphism and supplies an actual proper homogeneous quotient.
It proves finiteness of the **entire** covariance space for every coordinate
weight. For weights that are character coordinates it uses the published
identification with global sections of the actual descended character line
bundle and proper coherent-cohomology finiteness. For other weights the
covariance space is zero. The geometric quotient and its properness remain
hypotheses; no existence assertion is made for general reductive groups.

All constructions and proofs are derived from the Library's actual coordinate
coalgebra, right-contraction stability, normalized-character recovery and
proper-quotient finiteness, together with elementary vector-space duality and
character extensionality. There is no external literature assertion in this
unit. It does not prove a Steinberg dimension formula, irreducibility of entire
covariance spaces, or the universal `SteinbergBigCellStatement`.

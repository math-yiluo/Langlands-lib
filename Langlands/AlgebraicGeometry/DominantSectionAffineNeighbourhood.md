# Affine neighbourhoods from dominant sections

This internal construction supports the proof of Bosch–Lütkebohmert–Raynaud,
*Néron Models*, §6.4 Lemma 4. It is a derived geometric reduction, rather than
a transcription of a separately numbered result in that source.

Let `f : Z ⟶ S` be separated, with `Z` reduced, and let `U` be an open of
`S`. Suppose `s : U.toScheme ⟶ Z` is dominant and
`s ≫ f = U.ι`. The theorem
`isOpenImmersion_of_dominant_section` proves that `s` is an open immersion.
No finite-type or unramified hypothesis is used.

The proof factors `s` through `W = f ⁻¹ᵁ U`. The resulting morphism
`t : U.toScheme ⟶ W.toScheme` is a section of `f ∣_ U`, hence is a
closed immersion because that morphism is separated. Dominance of `s`
implies dominance of `t`, since the inclusion of `W` is an open immersion.
A dominant closed immersion is surjective. A surjective closed immersion
into a reduced scheme is an isomorphism. Composing `t` with `W.ι` proves
that `s` is an open immersion.

When `Z` is also affine, `affineNeighbourhoodOfDominantSection` takes a
finite set `E : Set S` contained in `U` and returns an actual
`V : S.Opens` with `IsAffineOpen V` and `E ⊆ V`. It maps the finite
set into `Z`, applies the published finite prime-avoidance theorem to
find an affine basic open contained in the image of `s`, pulls that
open back along `s`, and maps it into `S` along `U.ι`.

All declarations work for arbitrary `Scheme.{u}`, and empty finite sets
are allowed. This file does not yet construct the dominant section from
normal codimension-one points. It supplies the reduction to that
remaining construction and does not assert the unconditional common
affine-neighbourhood conclusion.

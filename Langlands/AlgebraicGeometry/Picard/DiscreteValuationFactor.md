# Discrete valuation factors of essentially finite type field maps

This internal algebra module supports the discrete valuative closed-image
criterion. It uses the Library's existing DVR domination theorem, imported
from the attributed Anthropic FLT port.

The first lemma identifies a field as the fraction field of a domain when
the domain's image generates the field as a subfield. The second lemma
starts with a valuation subring containing the base and an essentially
finite type field algebra. Express the finitely many field generators as
fractions of elements of the valuation ring. Adjoin all their numerators
and denominators to the base. The resulting finite type subalgebra stays
inside the valuation ring and has the original field as fraction field.

The final lemma, `exists_discrete_valuation_factor`, applies to every ring
homomorphism from a noetherian local ring `A` to a field `K` that is
essentially of finite type and is not a local homomorphism. It gives a
valuation subring `W` of this very field `K`, proves that `W` is a discrete
valuation ring, proves that `W` contains the image of `A`, and proves that
the induced map `A → W` is local. No injectivity assumption on `A → K`
is made.

Its implemented proof first factors the given map locally through a
valuation subring `V` using Mathlib's
`IsLocalRing.exists_factor_valuationRing`. The finite type subalgebra `D`
constructed above is noetherian because `A` is noetherian. Localize `D`
at the inverse image of the maximal ideal of `V`, realizing the
localization as a local subring `B` of `K`. The localization unit
criterion shows that `A → B` is local, and `K` remains the fraction field
of `B`. If `B` were a field, the original map to `K` would be local, a
contradiction. The imported theorem
`IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates`
therefore supplies a DVR valuation subring of `K` dominating `B`.
Its maximal-ideal identity makes `B → W` local, so the composite
`A → W` is local as required.

All three lemmas are internal derived algebra facts for the proof of
the discrete valuative closed-irreducible-image criterion. Their
provenance is this finite-generator and localization argument combined
with the existing Library DVR domination theorem; they introduce no new
literature claim. The imported DVR domination theorem retains the
attribution and licensing of the Anthropic FLT port in its own Lean and
Markdown files.

# Extending point realizations to completed residue fields

Author: Worker 74.

This derived construction extends a realization of a bounded multiplicative
spectrum point to its actual completed residue field. It uses the published
quotient, fraction field, absolute value and completion constructions in
`Spectrum.ResidueField`, without assuming an affinoid presentation or
completeness of the original algebra or scalar field. The three types may
have independent universes.

For a ring map `f : A →+* L` into a complete normed field with
`‖f a‖ = x a`, its kernel equals the kernel of the point. The proof factors
through the actual kernel quotient and embeds its fraction field into L.
Every fraction can be expressed as a quotient of images of two elements of A.
Multiplicativity of the field norm and the published norm evaluation formula
then prove that this fraction-field map preserves norms. Mathlib's isometric
completion extension supplies `completedResidueLiftRingHom`.

When the original map respects K, its extension does too, because scalars
already lie in the image of A. The resulting `completedResidueLift` is a bounded
K-algebra map with bound one and an isometry. Applying this construction to
the composite of a bounded algebra map with the completed residue evaluation
at a target point gives `completedResidueComap`. Its evaluation identity states
the commuting square with the original bounded map.

This is internal infrastructure for the full-domain spectrum embedding proof.
It is derived from the published completed residue-field construction, whose
source is Berkovich's *Non-archimedean analytic spaces* (Trieste 2009), p.4,
after Exercise 1.2.4. It does not assert general normed-field amalgamation,
spectrum-point lifting, or the injectivity of arbitrary domain spectrum maps.

# Semilinear automorphisms of polynomial projective space

This internal construction works for arbitrary commutative rings `R` and `B`
in the same universe, with an `R`-algebra structure on `B`. It acts on the
existing polynomial scheme `ProjectiveSpace B n`, using its published
base-change square over `ProjectiveSpace R n`.

For an algebra automorphism `σ`, `galoisMap R B n σ` is the unique pullback
lift fixing the projection to projective space over `R` and composing the
structure morphism with the existing `EtaleGaloisAction.specMap σ`.
The two projection equations are proved. Pullback extensionality proves
the identity and raw multiplication law
`m_(σ * τ) = m_σ ≫ m_τ`. The inverse automorphism gives `galoisIso`.
`galoisAction` bundles inverse comorphisms as a monoid homomorphism to the
categorical automorphism group, with
`(galoisAction R B n σ).hom = m_(σ⁻¹)`.

For any specified source base-change square and original map to projective
space over `R`, `baseChangeLift_galoisMap` proves that the existing
`baseChangeLift` intertwines every source morphism having these same two
semilinear projection equations. Its proof compares the two target
projections and uses the assumed source equations.

These are deductions from the published projective-space pullback and
generic spectrum-map constructions. There are no field, flatness,
Noetherian or closed-immersion assumptions. No continuity or cohomological
action is asserted.

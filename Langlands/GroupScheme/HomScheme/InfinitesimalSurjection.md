# Infinitesimal lifting along arbitrary nilpotent surjections

This internal adapter expresses the infinitesimal lifting theorem in a form
applicable to the quotient-transition maps of an adic tower. Its mathematical
input remains the published proposition
`MultiplicativeTypeInfinitesimalLiftStatement`, SGA 3, Exposé IX,
Théorème 3.6 and Corollaire 3.3 (Gille–Polo recomposed edition, 2009,
p.38, original margins pp.47–48; source
`sga3-expose-ix-gille-polo-2009`).

For a surjective homomorphism `φ : B → C` of commutative rings,
`surjectionTestIso φ hφ` is the canonical isomorphism
`Spec C ≅ Spec(B/ker φ)` in the category of schemes over `Spec B`.
Its construction uses the first isomorphism theorem for rings and checks
the triangle over `Spec B`.

`evaluate_iso_bijective` proves that relative-Hom evaluation along any
isomorphism of test schemes is bijective. Its inverse is evaluation along
the inverse isomorphism, by evaluation's composition and identity laws.

`infinitesimal_lifting_of_surjection` assumes the published infinitesimal
proposition in the given universe. Let `φ : B → C` be surjective with
nilpotent kernel, let `H`, `G` be group schemes over `Spec B`, assume `H`
is of multiplicative type and `G` is smooth over `Spec B`. Then every
homomorphism after base change to `Spec C` lifts over `Spec B`. Any two
global homomorphisms with equal restrictions are conjugate by a base point
whose restriction to `Spec C` is the identity.

The proof applies the assumed theorem to `ker φ`, transports Hom families
through `surjectionTestIso`, and uses naturality of constant points to
transport the identity-reduction condition. It does not prove the
infinitesimal input and imposes no noetherianity, completeness, or
affineness hypothesis.

# Geometric reflection data from integral normalizer reflections

This internal construction derives the geometric coordinate reflection data
needed by the root-centralizer neighbourhood construction from supplied actual
`RelativeRootReflectionData`. It retains the arbitrary original affine base,
its supplied closed standard torus, self-centralization at the specified
geometric identity component, reducedness along root lines and actual
one-dimensional root weights. Existence of the initial torus and forward field
reflection, reducedness and weight-line data remains outside this construction.
The final universal openness proposition is not proved here.

`normalizingGroupIso` uses the actual torus automorphism of a specified
normalizing point. `normalizingCoordinateIso` takes its exact integral character
coordinates. `exponentIso_normalizingCoordinateIso_hom` identifies the extension
over the original field with that same automorphism.

The Library's Weyl action precomposes characters with the inverse normalizing
automorphism. The supplied integral reflection formula and self-pairing two
therefore first show that this inverse negates the root. Composing with the
direct automorphism and negating proves that the direct automorphism also
negates the root. `normalizingCoordinateIso_inverts_root` transfers this equality
to the exact integral coordinates.

`normalizingAut_fixes_cocharacter` considers any actual cocharacter whose
pairing with the specified root is zero. Injectivity of the multiplicative
group's actual endomorphism-to-integer equivalence shows that its composite
with the root character is the zero homomorphism. Precomposing the reflection
formula with this cocharacter makes the correction term vanish for every
character, including each standard coordinate projection. Projections detect
actual maps to the standard torus. Thus the inverse automorphism fixes the
cocharacter, and composing with the direct automorphism proves the required
direct fixing equation. The coordinate version is
`normalizingCoordinateIso_fixes_cocharacter`.

This argument uses the formula on the entire actual character lattice. It
does not replace a scheme-theoretic character kernel by its reduced part or
assume that this kernel is smooth. The separate full-kernel-centralization
condition of `RelativeRootReflectionExistenceStatement` is unnecessary for
this consequence of its reflection-data conclusion.

`normalizingCoordinateIso_isTransporter` retains exactly the original actual
normalizer representative and its all-test transporter equation.
`geometricRootReflectionDataOfField` applies these constructions inside the
actual geometric identity component at the specified original point. The
generic annihilating cocharacter is the previously constructed fixed integer
cocharacter, and its dot-product vanishing gives the required pairing zero.
The result is an actual `GeometricRootReflectionData` record.

The supplied reflection data also give negation of the full actual geometric
exponent-root set through the published normalizer action on actual weights.
`identityComponentReductiveNeighbourhood_of_fieldReflectionData` uses this
derived negation and the constructed records in the finite root-centralizer
neighbourhood assembly. It constructs the actual original-base good open,
including every needed centralizer good open, from the retained inputs.

The provenance is internal: the actual normalizing automorphism, the integral
coordinate extension and its recovery equation, the integral reflection laws,
the actual character pairing, standard-torus projections and the existing
finite-neighbourhood construction. No new literature assertion is introduced.
All constructions are uniform in arbitrary universe `u` and have no
characteristic, noetherian or connected-ambient-fibre restriction.

# Rational Bruhat covering from common tori in minimal parabolics

Worker 1262. This internal assembly retains three explicit structural premises:
`GenericMinimalParabolicStatement`,
`ParabolicIntersectionCentralizerStatement`, and
`MinimalParabolicSplitTorusConjugacyStatement`. It does not prove those
statements, the disjointness of Weyl-indexed double cosets, or the full
`RationalBruhatStatement`. All groups, torus embeddings, normalizing points,
and dynamic subgroup functors are the published actual scheme constructions.

`RationalBruhatFactorization i F g` is a data type carrying a member of the
actual `normalizerPoints i`, two members of the specified subgroup functor at
the base scheme, and the equation expressing `g` as their product. It does not
assert existence without inputs. The noncomputable constructor
`rationalBruhatFactorizationOfStructural` chooses such data using the proved
conditional covering theorem below, under exactly the same three structural
premises and the same generic-cocharacter data. No uniqueness is asserted.

`conjugacy_eq_of_subgroup_factor` postcomposes an inside-subgroup conjugacy
with the subgroup inclusion. Naturality of the scheme inner automorphism,
proved in `BruhatCoveringReduction`, gives the ambient conjugacy equation.

`rationalBruhatCovering_of_commonTorus` assumes the common-centralizer and
inside-minimal-parabolic conjugacy statements. Its remaining data are a
connected reductive group over an arbitrary field, a maximal split torus,
and an actual minimal rational parabolic containing that torus. For a rational
point `g`, ambient isomorphism transport makes the conjugate parabolic minimal.
The common-centralizer premise supplies an ambient maximal split torus whose
centralizer lies in both parabolics on every test scheme. The common torus
itself lies in that centralizer, so represented subgroup factorization lifts
it into both parabolics. The inside-parabolic conjugacy premise supplies points
`p` and `q` of the original parabolic and actual torus-source isomorphisms with
ambient equations

`p S p⁻¹ = S' = g q S q⁻¹ g⁻¹`.

The published `normalizerPointOfConjugacySquare` constructs the actual
scheme-normalizer point `n = p⁻¹ g q`, with its torus automorphism. The group
identity gives `g = p n q⁻¹`; both outer factors lie in the all-test range of the
parabolic inclusion. No surjectivity of a quotient on rational points is used.

`rationalBruhatCovering_of_structural` adds the generic-minimality premise. It
chooses an actual representative of the minimal dynamic parabolic, uses
`Dynamic.parabolicTorusFactor` for the original torus containment, applies the
previous theorem, and rewrites the represented range as the original dynamic
parabolic. Its conclusion is precisely the covering half of
`HasRationalBruhatDecomposition` for each generic cocharacter.

The provenance is internal assembly of the published structural proposition
interfaces and actual subgroup constructions. No additional splitness,
perfectness, field cardinality, nonempty-root, or root-system assumption is
introduced. The geometric existence and conjugacy content remains entirely
in the displayed structural premises.

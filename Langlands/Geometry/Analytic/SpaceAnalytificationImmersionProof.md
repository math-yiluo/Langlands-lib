# Analytification of open and closed immersions of algebraic spaces

`spaceAnalytificationImmersion` proves the unchanged published proposition
`Langlands.Analytic.SpaceAnalytification.SpaceAnalytificationImmersionStatement`
in the arbitrary universe `u`. For a complete ultrametric nontrivially normed field
`K : Type u`, it treats any compatible map between two supplied analytifications of
separated algebraic spaces locally of finite type over `Spec K`. An algebraic open
immersion gives an open embedding of underlying analytic spaces, and an algebraic
closed immersion gives a closed embedding.

## Implemented proof

The theorem applies `spaceAnalytificationImmersionReduction`.
`affineClosedEmbeddingProperty_of_statement` obtains the premise from the first
clause of the Library theorem `affineAnalytificationImmersion`. This clause gives
closed embeddings for the analytic maps associated with surjective algebra maps
between affine tests.

To prove injectivity for a monomorphism, choose affine test chart lifts of two
source analytic points with the same image. The target's closed diagonal gives a
finite-type affine pullback of the two chart maps to the target. The affine
pullback clause of `IsAnalytification` and ordinary point lifting give an analytic
point of that pullback above the two lifts. On the common affine test, monicity
identifies the two algebraic source points, and naturality identifies the two
original source analytic points.

Composing an open immersion with a source étale affine test gives another étale
test. The resulting analytic chart map is open by `etaleOpenMap`. Joint
surjectivity of the source charts shows that the compatible analytic map is open.
Continuity and injectivity then give an open embedding.

Pulling back a closed immersion along a target étale affine test gives a closed
affine subscheme whose finite-type coordinate algebra is a quotient of the target
test algebra. The affine theorem makes the analytified projection a closed
embedding. For a closed source set, point lifting identifies the preimage of its
image on the target chart with the projection of its preimage on the pullback
chart. That preimage is closed by continuity, and the projection sends it to a
closed set. Openness and joint surjectivity of the target charts then show that
the compatible analytic map is closed. Continuity and injectivity give a closed
embedding.

## Sources and scope

The existing statement is derived from Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (2011), printed p.19, proof of Proposition 5.11(3), and
Conrad–Temkin, *Non-archimedean analytification of algebraic spaces* (2009), Theorem
2.2.3 on printed pp.7–8 and the last paragraph of §4.1 on printed p.19. The
Conrad–Temkin passage in §4.1 states preservation of fibre products and
Zariski-open and Zariski-closed immersions for existing `k`-analytic
analytifications. The Lean result gives the consequence for the underlying
topological spaces of the supplied analytifications.

The affine input corresponds to Berkovich, *Spectral Theory and Analytic Geometry
over Non-Archimedean Fields* (1990), Proposition 3.4.7(2), printed p.66/PDF p.80.
The adjacent Proposition 3.4.6(8), printed p.65/PDF p.79, treats open immersions.
The registered source IDs are
`conrad-2011-weil-grothendieck-adelic-points`,
`conrad-temkin-2009-nonarchimedean-analytification`, and
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`.

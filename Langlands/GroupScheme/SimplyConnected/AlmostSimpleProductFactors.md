# Closed normal inclusions of actual almost-simple product factors

Author: Worker 166.

This internal construction exposes the inclusions and retractions of the
published `SimplyConnectedAlmostSimpleProduct`. Each factor maps into the
original group through the inverse of the supplied product isomorphism.
Its projection is a retraction. If the original group is affine over the
field, its inclusion is a closed immersion, since a section of a separated
morphism is closed.

For a finite family of arbitrary group schemes over any base,
`piFactorInclusionHom` inserts a point in one coordinate and the identity in
all other coordinates. The pointwise range characterization says exactly
that all other coordinates are the identity. Coordinatewise conjugation
therefore preserves the range on every test scheme. Transport through the
supplied product isomorphism proves normality of each factor in the
original group. No commutativity, reduced-test or rational-point restriction
is used.

These are internal consequences of the categorical products and the
published product presentation, intended for the canonical-factor step in
the proof of the Weil-restriction structure theorem. They do not yet assert
uniqueness, Galois invariance, absolute simplicity or descent.

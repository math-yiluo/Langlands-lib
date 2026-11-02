# From actual line-bundle class loci to the full Picard diagonal

Author: Worker 509.

This internal reduction assumes the published proposition
`FieldPicardClassEqualizerImmersionStatement`, which concerns the equality of
fppf classes of two actual line bundles for every scheme test. It proves the
same representability-by-immersion conclusion for every pair of sections of the
actual Picard sheaf, over every proper scheme over every field in universe `u`.
The construction `fieldPicardSectionEqualizer` chooses an actual scheme and
immersion, together with its factorization criterion on every further scheme
test. It adds no global-representative hypothesis to the sections.

The proof takes the intersection of the two representative sieves. Local
surjectivity of ordinary classes onto the actual sheafification makes this an
fppf covering sieve. On each member the existing choice construction supplies
two actual line bundles. The input proposition gives their immersed equality
locus. The choice-specification equalities identify it with the restrictions of
the original sections. The generic fppf local-equalizer theorem then glues these
representations on the underlying schemes and restores their base maps. Finally
the published diagonal-equalizer criterion gives representability by immersions
of the full presheaf diagonal.

This is an internal application of published local-representative, descent and
diagonal criteria. No new external literature is used. It is a conditional
reduction: it does not prove the actual bundle-class equalizer input, atlas
existence, algebraic-space representability or closedness of the diagonal.
Those remain separate obligations of the full theorem. No projectivity,
smoothness, reducedness, section or global-function assumption is introduced.
